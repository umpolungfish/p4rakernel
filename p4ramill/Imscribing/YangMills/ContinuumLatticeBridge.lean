import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Int.ModEq
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

namespace Imscribing.Millennium.ContinuumLatticeBridge

theorem natMod_injective_of_abs_sub_lt {L : ℕ} (hL : 0 < L) {a b : ℤ}
    (hab : |a - b| < (L : ℤ)) (hmod : Int.natMod a L = Int.natMod b L) : a = b := by
  have hLne : (L : ℤ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hL)
  have hrem : a % (L : ℤ) = b % (L : ℤ) := by
    have hcast := congrArg (fun n : ℕ => (n : ℤ)) hmod
    simpa [Int.natMod, Int.toNat_of_nonneg (Int.emod_nonneg a hLne),
      Int.toNat_of_nonneg (Int.emod_nonneg b hLne)] using hcast
  have hdvd : (L : ℤ) ∣ b - a := by
    exact (Int.modEq_iff_dvd).mp hrem
  have hba : |b - a| < (L : ℤ) := by simpa [abs_sub_comm] using hab
  have hbounds := abs_lt.mp hba
  have hLpos : 0 < (L : ℤ) := by exact_mod_cast hL
  rcases hdvd with ⟨k, hk⟩
  by_cases hk0 : k = 0
  · rw [hk0, mul_zero, sub_eq_zero] at hk
    exact hk.symm
  · rcases lt_or_gt_of_ne hk0 with hkneg | hkpos
    · have hk_le : k ≤ -1 := by omega
      have hprod : (L : ℤ) * k ≤ -(L : ℤ) := by
        calc
          (L : ℤ) * k ≤ (L : ℤ) * (-1) := mul_le_mul_of_nonneg_left hk_le hLpos.le
          _ = -(L : ℤ) := by ring
      rw [hk] at hbounds
      omega
    · have hk_ge : 1 ≤ k := by omega
      have hprod : (L : ℤ) ≤ (L : ℤ) * k := by
        calc
          (L : ℤ) = (L : ℤ) * 1 := by ring
          _ ≤ (L : ℤ) * k := mul_le_mul_of_nonneg_left hk_ge hLpos.le
      rw [hk] at hbounds
      omega

theorem eventually_ne_of_ne
    {X : Type*} [PseudoMetricSpace X]
    {L : ℕ → Type*} (site : ∀ N, X → L N) (embed : ∀ N, L N → X)
    (err : ℕ → ℝ)
    (herr_bound : ∀ N x, dist (embed N (site N x)) x ≤ err N)
    (herr_tendsto : Filter.Tendsto err Filter.atTop (nhds 0))
    {x y : X} (hxy : 0 < dist x y) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, site N x ≠ site N y := by
  have hhalf : 0 < dist x y / 2 := half_pos hxy
  rw [Metric.tendsto_atTop] at herr_tendsto
  obtain ⟨N₀, hN₀⟩ := herr_tendsto (dist x y / 2) hhalf
  refine ⟨N₀, fun N hN hEq => ?_⟩
  have herrN : err N < dist x y / 2 := by
    have h := hN₀ N hN
    rw [Real.dist_eq, sub_zero] at h
    exact lt_of_le_of_lt (le_abs_self (err N)) h
  have hNx : dist (embed N (site N x)) x < dist x y / 2 :=
    lt_of_le_of_lt (herr_bound N x) herrN
  have hNy : dist (embed N (site N y)) y < dist x y / 2 :=
    lt_of_le_of_lt (herr_bound N y) herrN
  have hlt : dist x y < dist x y := by
    calc dist x y
        ≤ dist x (embed N (site N x)) + dist (embed N (site N x)) y := dist_triangle _ _ _
      _ = dist (embed N (site N x)) x + dist (embed N (site N y)) y := by rw [dist_comm x, hEq]
      _ < dist x y / 2 + dist x y / 2 := add_lt_add hNx hNy
      _ = dist x y := add_halves _
  exact (lt_irrefl _ hlt).elim

theorem eventually_injective_on_tuple
    {X : Type*} [MetricSpace X]
    {L : ℕ → Type*} (site : ∀ N, X → L N) (embed : ∀ N, L N → X)
    (err : ℕ → ℝ)
    (herr_bound : ∀ N x, dist (embed N (site N x)) x ≤ err N)
    (herr_tendsto : Filter.Tendsto err Filter.atTop (nhds 0))
    {m : ℕ} (pts : Fin m → X) (hpts : Function.Injective pts) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, Function.Injective (fun i => site N (pts i)) := by
  classical
  let thresh : Fin m × Fin m → ℕ := fun p =>
    if h : p.1 = p.2 then 0
    else Classical.choose
      (eventually_ne_of_ne site embed err herr_bound herr_tendsto
        (dist_pos.mpr (hpts.ne h)))
  refine ⟨Finset.univ.sup thresh, fun N hN i j hij => ?_⟩
  by_contra hsite
  have hindices : i ≠ j := by
    intro heq
    subst j
    exact hsite rfl
  have hle : thresh (i, j) ≤ Finset.univ.sup thresh :=
    Finset.le_sup (f := thresh) (Finset.mem_univ (i, j))
  have hsep := eventually_ne_of_ne site embed err herr_bound herr_tendsto
    (dist_pos.mpr (hpts.ne hindices))
  have hspec := Classical.choose_spec hsep
  have hthresh : thresh (i, j) = Classical.choose hsep := by
    dsimp [thresh]
    rw [dif_neg hindices]
  exact hspec N (le_trans (hthresh ▸ hle) hN) hij

noncomputable def gridSite {d : ℕ} (freq : ℕ → ℝ) (N : ℕ) (x : Fin d → ℝ) : Fin d → ℤ :=
  fun i => ⌊x i * freq N⌋

noncomputable def gridEmbed {d : ℕ} (freq : ℕ → ℝ) (N : ℕ) (z : Fin d → ℤ) : Fin d → ℝ :=
  fun i => (z i : ℝ) / freq N

theorem grid_err_bound {d : ℕ} (freq : ℕ → ℝ) (hpos : ∀ N, 0 < freq N)
    (N : ℕ) (x : Fin d → ℝ) :
    dist (gridEmbed freq N (gridSite freq N x)) x ≤ 1 / freq N := by
  have hfpos : 0 < freq N := hpos N
  rw [dist_pi_le_iff (by positivity)]
  intro i
  rw [Real.dist_eq, gridEmbed, gridSite]
  have hfl : (⌊x i * freq N⌋ : ℝ) ≤ x i * freq N := Int.floor_le _
  have hfu : x i * freq N < (⌊x i * freq N⌋ : ℝ) + 1 := Int.lt_floor_add_one _
  have hdiff_nonpos : (⌊x i * freq N⌋ : ℝ) / freq N - x i ≤ 0 := by
    rw [sub_nonpos, div_le_iff₀ hfpos]
    exact hfl
  rw [abs_of_nonpos hdiff_nonpos, neg_sub, sub_le_iff_le_add, ← add_div, le_div_iff₀ hfpos]
  linarith

theorem hypercubic_eventually_injective_on_tuple
    {d m : ℕ} (freq : ℕ → ℝ)
    (hpos : ∀ N, 0 < freq N)
    (hdiv : Filter.Tendsto (fun N => 1 / freq N) Filter.atTop (nhds 0))
    (pts : Fin m → (Fin d → ℝ)) (hpts : Function.Injective pts) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, Function.Injective (fun i => gridSite freq N (pts i)) :=
  eventually_injective_on_tuple
    (site := gridSite freq)
    (embed := gridEmbed freq)
    (err := fun N => 1 / freq N)
    (herr_bound := grid_err_bound freq hpos)
    hdiv pts hpts

noncomputable def diagStageFreq {Y : Type*} [PseudoMetricSpace Y]
    (M : ℕ → ℕ → ℕ → Y) (M_inf : ℕ → ℕ → Y)
    (h_inner : ∀ k N, Filter.Tendsto (fun F => M k N F) Filter.atTop (nhds (M_inf k N)))
    (N : ℕ) : ℕ :=
  Finset.sup (Finset.range (N + 1)) fun k =>
    Classical.choose ((Metric.tendsto_atTop.mp (h_inner k N))
      (1 / (N + 1 : ℝ)) (by positivity))

theorem exists_uniform_frequency {ι Y : Type*} [Finite ι] [PseudoMetricSpace Y]
    (M : ι → ℕ → Y) (L : ι → Y)
    (hlim : ∀ i, Filter.Tendsto (M i) Filter.atTop (nhds (L i)))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ F : ℕ, ∀ i, dist (M i F) (L i) < ε := by
  have hAll : ∀ᶠ F : ℕ in Filter.atTop, ∀ i, dist (M i F) (L i) < ε := by
    rw [Filter.eventually_all]
    intro i
    obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.mp (hlim i)) ε hε
    exact Filter.eventually_atTop.2 ⟨N, hN⟩
  exact hAll.exists

noncomputable def uniformFrequency {ι Y : Type*} [Finite ι] [PseudoMetricSpace Y]
    (M : ι → ℕ → Y) (L : ι → Y)
    (hlim : ∀ i, Filter.Tendsto (M i) Filter.atTop (nhds (L i)))
    (ε : ℝ) (hε : 0 < ε) : ℕ :=
  Classical.choose (exists_uniform_frequency M L hlim hε)

theorem uniformFrequency_spec {ι Y : Type*} [Finite ι] [PseudoMetricSpace Y]
    (M : ι → ℕ → Y) (L : ι → Y)
    (hlim : ∀ i, Filter.Tendsto (M i) Filter.atTop (nhds (L i)))
    (ε : ℝ) (hε : 0 < ε) :
    ∀ i, dist (M i (uniformFrequency M L hlim ε hε)) (L i) < ε :=
  Classical.choose_spec (exists_uniform_frequency M L hlim hε)

noncomputable def stageSchedule {Y : Type*} [PseudoMetricSpace Y]
    (N₀ : ℕ) (M : ℕ → ℕ → Y) (L : ℕ → Y)
    (h_conv : ∀ k, Filter.Tendsto (M k) Filter.atTop (nhds (L k))) : ℕ → ℕ
  | 0 => max N₀
      (Classical.choose ((Metric.tendsto_atTop.mp (h_conv 0)) 1 (by positivity)))
  | n + 1 =>
      max (stageSchedule N₀ M L h_conv n + 1)
        (Finset.sup (Finset.range (n + 2)) fun k =>
          Classical.choose ((Metric.tendsto_atTop.mp (h_conv k))
            (1 / (n + 2 : ℝ)) (by positivity)))

theorem stageSchedule_strictMono {Y : Type*} [PseudoMetricSpace Y]
    (N₀ : ℕ) (M : ℕ → ℕ → Y) (L : ℕ → Y)
    (h_conv : ∀ k, Filter.Tendsto (M k) Filter.atTop (nhds (L k))) :
    StrictMono (stageSchedule N₀ M L h_conv) := by
  refine strictMono_nat_of_lt_succ fun n => ?_
  dsimp [stageSchedule]
  exact Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (le_max_left _ _)

theorem stageSchedule_ge_threshold {Y : Type*} [PseudoMetricSpace Y]
    (N₀ : ℕ) (M : ℕ → ℕ → Y) (L : ℕ → Y)
    (h_conv : ∀ k, Filter.Tendsto (M k) Filter.atTop (nhds (L k))) :
    ∀ n : ℕ, N₀ ≤ stageSchedule N₀ M L h_conv n := by
  intro n
  induction n with
  | zero => exact le_max_left _ _
  | succ n ih =>
      exact le_trans ih (le_trans (Nat.le_succ _) (le_max_left _ _))

theorem choose_stage_schedule_with_inj {Y : Type*} [PseudoMetricSpace Y]
    (N₀ : ℕ) (M : ℕ → ℕ → Y) (L : ℕ → Y)
    (h_conv : ∀ k, Filter.Tendsto (M k) Filter.atTop (nhds (L k))) :
    let stage := stageSchedule N₀ M L h_conv
    (∀ n, N₀ ≤ stage n) ∧
    (∀ k n, k ≤ n → dist (M k (stage n)) (L k) < 1 / (n + 1 : ℝ)) ∧
    (∀ k, Filter.Tendsto (fun n => M k (stage n)) Filter.atTop (nhds (L k))) := by
  intro stage
  refine ⟨stageSchedule_ge_threshold N₀ M L h_conv, ?_, ?_⟩
  · intro k n hkn
    cases n with
    | zero =>
        have hk0 : k = 0 := Nat.eq_zero_of_le_zero hkn
        subst hk0
        have hspec := Classical.choose_spec
          ((Metric.tendsto_atTop.mp (h_conv 0)) 1 (by positivity))
        simpa using hspec (stage 0) (le_max_right _ _)
    | succ m =>
        have hspec := Classical.choose_spec
          ((Metric.tendsto_atTop.mp (h_conv k)) (1 / (m + 2 : ℝ)) (by positivity))
        have hle :
            Classical.choose ((Metric.tendsto_atTop.mp (h_conv k))
              (1 / (m + 2 : ℝ)) (by positivity)) ≤ stage (m + 1) := by
          refine le_trans ?_ (le_max_right _ _)
          simpa using (Finset.le_sup
            (f := fun j : ℕ => Classical.choose ((Metric.tendsto_atTop.mp (h_conv j))
              (1 / (m + 2 : ℝ)) (by positivity)))
            (Finset.mem_range.mpr (Nat.lt_succ_of_le hkn)))
        have hdist := hspec (stage (m + 1)) hle
        convert hdist using 1 <;> norm_num [Nat.cast_add, Nat.cast_one, add_assoc]
  · intro k
    exact (h_conv k).comp (stageSchedule_strictMono N₀ M L h_conv).tendsto_atTop

theorem choose_stage_frequency_double_limit
    {Y : Type*} [PseudoMetricSpace Y]
    (M : ℕ → ℕ → ℕ → Y) (M_inf : ℕ → ℕ → Y) (L : ℕ → Y)
    (h_inner : ∀ k N, Filter.Tendsto (fun F => M k N F) Filter.atTop (nhds (M_inf k N)))
    (h_outer : ∀ k, Filter.Tendsto (fun N => M_inf k N) Filter.atTop (nhds (L k))) :
    ∀ k : ℕ, Filter.Tendsto
      (fun N => M k N (diagStageFreq M M_inf h_inner N)) Filter.atTop (nhds (L k)) := by
  intro k
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N₁, hN₁⟩ := (Metric.tendsto_atTop.mp (h_outer k)) (ε / 2) (half_pos hε)
  obtain ⟨N₂, hN₂⟩ := exists_nat_one_div_lt (half_pos hε)
  refine ⟨max k (max N₁ N₂), fun N hN => ?_⟩
  have hkN : k ≤ N := le_trans (le_max_left _ _) hN
  have hN₁N : N₁ ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hN
  have hN₂N : N₂ ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hN
  have hfreq_ge :
      Classical.choose ((Metric.tendsto_atTop.mp (h_inner k N)) (1 / (N + 1 : ℝ)) (by positivity)) ≤
      diagStageFreq M M_inf h_inner N := by
    dsimp [diagStageFreq]
    simpa using (Finset.le_sup
      (f := fun j : ℕ => Classical.choose
        ((Metric.tendsto_atTop.mp (h_inner j N)) (1 / (N + 1 : ℝ)) (by positivity)))
      (Finset.mem_range.mpr (Nat.lt_succ_of_le hkN)))
  have h1 : dist (M k N (diagStageFreq M M_inf h_inner N)) (M_inf k N) < 1 / (N + 1 : ℝ) :=
    Classical.choose_spec
      ((Metric.tendsto_atTop.mp (h_inner k N)) (1 / (N + 1 : ℝ)) (by positivity))
      (diagStageFreq M M_inf h_inner N) hfreq_ge
  have h1' : (1 : ℝ) / (N + 1 : ℝ) < ε / 2 := by
    have hle : (1 : ℝ) / (N + 1 : ℝ) ≤ 1 / (N₂ + 1 : ℝ) := by
      apply one_div_le_one_div_of_le (by positivity)
      exact_mod_cast Nat.succ_le_succ hN₂N
    exact lt_of_le_of_lt hle hN₂
  have h2 : dist (M_inf k N) (L k) < ε / 2 := hN₁ N hN₁N
  calc dist (M k N (diagStageFreq M M_inf h_inner N)) (L k)
      ≤ dist (M k N (diagStageFreq M M_inf h_inner N)) (M_inf k N) + dist (M_inf k N) (L k) :=
        dist_triangle _ _ _
    _ < ε / 2 + ε / 2 := add_lt_add (lt_trans h1 h1') h2
    _ = ε := add_halves _

end Imscribing.Millennium.ContinuumLatticeBridge
