import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

namespace Imscribing.YangMills.TorusWraparoundBridge

/-- Periodic 1D lattice coordinate matching `(Int.natMod ⌊u / a⌋ L) % L : Fin L`. -/
noncomputable def torusCoord (L : ℕ) [NeZero L] (a : ℝ) (u : ℝ) : Fin L :=
  ⟨(Int.natMod ⌊u / a⌋ L) % L, Nat.mod_lt _ (NeZero.pos L)⟩

/-- Periodic d-dimensional torus site map. -/
noncomputable def torusSite {d : ℕ} (L : ℕ) [NeZero L] (a : ℝ) (x : Fin d → ℝ) : Fin d → Fin L :=
  fun μ => torusCoord L a (x μ)

/-- Exact characterization of periodic wraparound collisions in 1D. -/
theorem torusCoord_eq_iff (L : ℕ) [NeZero L] (a : ℝ) (u v : ℝ) :
    torusCoord L a u = torusCoord L a v ↔
      ∃ k : ℤ, ⌊u / a⌋ - ⌊v / a⌋ = (L : ℤ) * k := by
  have hLpos : 0 < L := NeZero.pos L
  have hLposZ : (0 : ℤ) < L := by exact_mod_cast hLpos
  have hLneZ : (L : ℤ) ≠ 0 := hLposZ.ne'
  have hmod_lt : ∀ z : ℤ, Int.natMod z L < L := fun z => by
    have hz0 : 0 ≤ z % (L : ℤ) := Int.emod_nonneg z hLneZ
    have hzL : z % (L : ℤ) < (L : ℤ) := Int.emod_lt_of_pos z hLposZ
    dsimp [Int.natMod]
    omega
  constructor
  · intro h
    have hv : (Int.natMod ⌊u / a⌋ L) % L = (Int.natMod ⌊v / a⌋ L) % L :=
      congrArg Fin.val h
    rw [Nat.mod_eq_of_lt (hmod_lt _), Nat.mod_eq_of_lt (hmod_lt _)] at hv
    dsimp [Int.natMod] at hv
    have hu0 : 0 ≤ ⌊u / a⌋ % (L : ℤ) := Int.emod_nonneg _ hLneZ
    have hv0 : 0 ≤ ⌊v / a⌋ % (L : ℤ) := Int.emod_nonneg _ hLneZ
    have hZ : ⌊u / a⌋ % (L : ℤ) = ⌊v / a⌋ % (L : ℤ) := by
      calc
        ⌊u / a⌋ % (L : ℤ) = (Int.natMod ⌊u / a⌋ L : ℤ) := by
          symm
          exact Int.toNat_of_nonneg hu0
        _ = (Int.natMod ⌊v / a⌋ L : ℤ) := congrArg Int.ofNat hv
        _ = ⌊v / a⌋ % (L : ℤ) := Int.toNat_of_nonneg hv0
    have h1 := Int.emod_add_mul_ediv ⌊u / a⌋ (L : ℤ)
    have h2 := Int.emod_add_mul_ediv ⌊v / a⌋ (L : ℤ)
    refine ⟨⌊u / a⌋ / L - ⌊v / a⌋ / L, ?_⟩
    linarith
  · rintro ⟨k, hk⟩
    have hmod : ⌊u / a⌋ % (L : ℤ) = ⌊v / a⌋ % (L : ℤ) := by
      have heq : ⌊u / a⌋ = ⌊v / a⌋ + (L : ℤ) * k := by linarith
      rw [heq, Int.add_mul_emod_self_left]
    apply Fin.ext
    dsimp [torusCoord, Int.natMod]
    rw [hmod]

/-- Non-wraparound 1D separation: if `a ≤ |u - v| ≤ (L - 1) * a`, then
    `u` and `v` map to distinct periodic sites. -/
theorem torusCoord_ne_of_sep (L : ℕ) [NeZero L] {a u v : ℝ}
    (ha : 0 < a) (hlow : a ≤ |u - v|) (hhigh : |u - v| ≤ ((L : ℝ) - 1) * a) :
    torusCoord L a u ≠ torusCoord L a v := by
  intro hEq
  obtain ⟨k, hk⟩ := (torusCoord_eq_iff L a u v).mp hEq
  have h1 : (⌊u / a⌋ : ℝ) ≤ u / a := Int.floor_le _
  have h2 : u / a < (⌊u / a⌋ : ℝ) + 1 := Int.lt_floor_add_one _
  have h3 : (⌊v / a⌋ : ℝ) ≤ v / a := Int.floor_le _
  have h4 : v / a < (⌊v / a⌋ : ℝ) + 1 := Int.lt_floor_add_one _
  have hdiff_lt : (u - v) / a < ((⌊u / a⌋ - ⌊v / a⌋ : ℤ) : ℝ) + 1 := by
    have hdiv : (u - v) / a = u / a - v / a := by field_simp [ha.ne'] <;> ring
    rw [hdiv]
    push_cast
    linarith
  have hdiff_gt : ((⌊u / a⌋ - ⌊v / a⌋ : ℤ) : ℝ) - 1 < (u - v) / a := by
    have hdiv : (u - v) / a = u / a - v / a := by field_simp [ha.ne'] <;> ring
    rw [hdiv]
    push_cast
    linarith
  have hk_cast : ((⌊u / a⌋ - ⌊v / a⌋ : ℤ) : ℝ) = (L : ℝ) * (k : ℝ) := by
    exact_mod_cast hk
  rw [hk_cast] at hdiff_lt hdiff_gt
  rcases lt_trichotomy k 0 with hk_neg | rfl | hk_pos
  · have hk1 : (k : ℝ) ≤ -1 := by exact_mod_cast Int.le_sub_one_of_lt hk_neg
    have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast NeZero.pos L
    have hlt : u - v < (((L : ℝ) * (k : ℝ)) + 1) * a := by
      rw [← div_lt_iff₀ ha]
      exact hdiff_lt
    have hle : ((L : ℝ) * (k : ℝ) + 1) * a ≤ -(((L : ℝ) - 1) * a) := by nlinarith
    have hneg : ((L : ℝ) - 1) * a < -(u - v) := by linarith
    exact not_le_of_gt (lt_of_lt_of_le hneg (neg_le_abs (u - v))) hhigh
  · simp only [Int.cast_zero, mul_zero, zero_add, zero_sub] at hdiff_lt hdiff_gt
    have habs : |u - v| / a < 1 := by
      rw [← abs_of_pos ha, ← abs_div, abs_lt]
      exact ⟨by linarith [show (u - v) / a = u / a - v / a by ring],
        by linarith [show (u - v) / a = u / a - v / a by ring]⟩
    have hlt : |u - v| < a := by rwa [div_lt_one ha] at habs
    exact not_le_of_gt hlt hlow
  · have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk_pos
    have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast NeZero.pos L
    have hgt : (((L : ℝ) * (k : ℝ)) - 1) * a < u - v := by
      rw [← lt_div_iff₀ ha]
      exact hdiff_gt
    have hge : ((L : ℝ) - 1) * a ≤ ((L : ℝ) * (k : ℝ) - 1) * a := by nlinarith
    have hpos : ((L : ℝ) - 1) * a < u - v := by linarith
    exact not_le_of_gt (lt_of_lt_of_le hpos (le_abs_self (u - v))) hhigh

/-- Fixed-torus 1D separation: if every `B`-periodic translate of `u - v` is at distance
    at least `a` (where `B = L * a`), then `u` and `v` map to distinct periodic sites. -/
theorem torusCoord_ne_of_torus_sep (L : ℕ) [NeZero L] {a u v : ℝ}
    (ha : 0 < a) (hsep : ∀ k : ℤ, a ≤ |u - v - (k : ℝ) * ((L : ℝ) * a)|) :
    torusCoord L a u ≠ torusCoord L a v := by
  intro hEq
  obtain ⟨k, hk⟩ := (torusCoord_eq_iff L a u v).mp hEq
  have h1 : (⌊u / a⌋ : ℝ) ≤ u / a := Int.floor_le _
  have h2 : u / a < (⌊u / a⌋ : ℝ) + 1 := Int.lt_floor_add_one _
  have h3 : (⌊v / a⌋ : ℝ) ≤ v / a := Int.floor_le _
  have h4 : v / a < (⌊v / a⌋ : ℝ) + 1 := Int.lt_floor_add_one _
  have hk_cast : ((⌊u / a⌋ - ⌊v / a⌋ : ℤ) : ℝ) = (L : ℝ) * (k : ℝ) := by
    exact_mod_cast hk
  have hdiv : |(u - v - (k : ℝ) * ((L : ℝ) * a)) / a| < 1 := by
    have heq : (u - v - (k : ℝ) * ((L : ℝ) * a)) / a =
        (u / a - v / a) - ((⌊u / a⌋ - ⌊v / a⌋ : ℤ) : ℝ) := by
      rw [hk_cast]
      field_simp [ha.ne']
    rw [heq, abs_lt]
    push_cast
    constructor <;> linarith
  have hlt : |u - v - (k : ℝ) * ((L : ℝ) * a)| < a := by
    rw [abs_div, abs_of_pos ha, div_lt_one ha] at hdiv
    exact hdiv
  exact not_le_of_gt hlt (hsep k)

/-- Infinite-volume + continuum regime: if `a_N → 0` and `L_N a_N → ∞`, any fixed
    injective finite tuple in `(Fin d → ℝ)` maps injectively to periodic torus sites eventually. -/
theorem torus_eventually_injective_infinite_volume
    {d m : ℕ} (L : ℕ → ℕ) [∀ N, NeZero (L N)] (a : ℕ → ℝ)
    (ha_pos : ∀ N, 0 < a N)
    (ha_zero : Filter.Tendsto a Filter.atTop (nhds 0))
    (hvol : Filter.Tendsto (fun N => (L N : ℝ) * a N) Filter.atTop Filter.atTop)
    (pts : Fin m → (Fin d → ℝ)) (hpts : Function.Injective pts) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, Function.Injective (torusSite (L N) (a N) ∘ pts) := by
  classical
  have hpair : ∀ i j : Fin m, i ≠ j →
      ∃ N₀ : ℕ, ∀ N ≥ N₀, torusSite (L N) (a N) (pts i) ≠ torusSite (L N) (a N) (pts j) := by
    intro i j hij
    obtain ⟨μ, hμ⟩ := Function.ne_iff.mp (hpts.ne hij)
    have hsep : 0 < |pts i μ - pts j μ| := abs_pos.mpr (sub_ne_zero.mpr hμ)
    obtain ⟨N₁, hN₁⟩ := (Metric.tendsto_atTop.mp ha_zero) |pts i μ - pts j μ| hsep
    obtain ⟨N₂, hN₂⟩ := (Metric.tendsto_atTop.mp ha_zero) 1 zero_lt_one
    obtain ⟨N₃, hN₃⟩ := Filter.eventually_atTop.mp
      (Filter.tendsto_atTop.mp hvol (|pts i μ - pts j μ| + 1))
    refine ⟨max N₁ (max N₂ N₃), fun N hN hEq => ?_⟩
    have h1 : a N ≤ |pts i μ - pts j μ| := by
      have := hN₁ N (le_trans (le_max_left _ _) hN)
      rw [Real.dist_eq, sub_zero, abs_of_pos (ha_pos N)] at this
      exact this.le
    have h2 : a N < 1 := by
      have := hN₂ N (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hN)
      rw [Real.dist_eq, sub_zero, abs_of_pos (ha_pos N)] at this
      exact this
    have h3 : |pts i μ - pts j μ| + 1 ≤ (L N : ℝ) * a N :=
      hN₃ N (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hN)
    have hhigh : |pts i μ - pts j μ| ≤ ((L N : ℝ) - 1) * a N := by linarith
    have hcoord : torusCoord (L N) (a N) (pts i μ) = torusCoord (L N) (a N) (pts j μ) :=
      congrFun hEq μ
    exact torusCoord_ne_of_sep (L N) (ha_pos N) h1 hhigh hcoord
  let thresh : Fin m × Fin m → ℕ := fun p =>
    if h : p.1 = p.2 then 0 else Classical.choose (hpair p.1 p.2 h)
  refine ⟨Finset.univ.sup thresh, fun N hN i j hij => ?_⟩
  by_contra hne
  have hle : thresh (i, j) ≤ Finset.univ.sup thresh :=
    Finset.le_sup (f := thresh) (Finset.mem_univ (i, j))
  have hthresh : thresh (i, j) = Classical.choose (hpair i j hne) := by
    dsimp [thresh]
    exact dif_neg hne
  exact (Classical.choose_spec (hpair i j hne)) N (le_trans (hthresh ▸ hle) hN) hij

/-- Fixed-period torus regime: if `(L N) * a N = B` and `a N → 0`, any finite tuple
    distinct modulo `B ℤ^d` maps injectively to torus sites eventually. -/
theorem torus_eventually_injective_fixed_torus
    {d m : ℕ} (B : ℝ) (hB : 0 < B)
    (L : ℕ → ℕ) [∀ N, NeZero (L N)] (a : ℕ → ℝ)
    (ha_pos : ∀ N, 0 < a N)
    (ha_zero : Filter.Tendsto a Filter.atTop (nhds 0))
    (hperiod : ∀ N, (L N : ℝ) * a N = B)
    (pts : Fin m → (Fin d → ℝ))
    (hpts_mod : ∀ i j : Fin m, i ≠ j → ∃ μ : Fin d, ∀ k : ℤ,
      pts i μ - pts j μ ≠ (k : ℝ) * B) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, Function.Injective (torusSite (L N) (a N) ∘ pts) := by
  classical
  have hpair : ∀ i j : Fin m, i ≠ j →
      ∃ N₀ : ℕ, ∀ N ≥ N₀, torusSite (L N) (a N) (pts i) ≠ torusSite (L N) (a N) (pts j) := by
    intro i j hij
    obtain ⟨μ, hμ⟩ := hpts_mod i j hij
    let q : ℤ := ⌊(pts i μ - pts j μ) / B⌋
    have hq_le : (q : ℝ) * B ≤ pts i μ - pts j μ := by
      rw [← le_div_iff₀ hB]
      exact Int.floor_le _
    have hq_lt : pts i μ - pts j μ < ((q + 1 : ℤ) : ℝ) * B := by
      rw [← div_lt_iff₀ hB]
      push_cast
      exact Int.lt_floor_add_one _
    have hq_ne : pts i μ - pts j μ ≠ (q : ℝ) * B := hμ q
    have hq_gt : (q : ℝ) * B < pts i μ - pts j μ := lt_of_le_of_ne hq_le hq_ne.symm
    let δ : ℝ := min ((pts i μ - pts j μ) - (q : ℝ) * B)
      (((q + 1 : ℤ) : ℝ) * B - (pts i μ - pts j μ))
    have hδ : 0 < δ := lt_min (sub_pos.mpr hq_gt) (sub_pos.mpr hq_lt)
    obtain ⟨N₀, hN₀⟩ := (Metric.tendsto_atTop.mp ha_zero) δ hδ
    refine ⟨N₀, fun N hN hEq => ?_⟩
    have haδ : a N ≤ δ := by
      have := hN₀ N hN
      rw [Real.dist_eq, sub_zero, abs_of_pos (ha_pos N)] at this
      exact this.le
    have hsep : ∀ k : ℤ, a N ≤ |pts i μ - pts j μ - (k : ℝ) * ((L N : ℝ) * a N)| := by
      intro k
      rw [hperiod N]
      refine le_trans haδ ?_
      rcases le_or_gt k q with hkq | hkq
      · have hkB : (k : ℝ) * B ≤ (q : ℝ) * B :=
          mul_le_mul_of_nonneg_right (by exact_mod_cast hkq) hB.le
        have hpos : 0 ≤ pts i μ - pts j μ - (k : ℝ) * B := by linarith
        rw [abs_of_nonneg hpos]
        exact le_trans (min_le_left _ _) (by linarith)
      · have hq1 : q + 1 ≤ k := hkq
        have hkB : ((q + 1 : ℤ) : ℝ) * B ≤ (k : ℝ) * B :=
          mul_le_mul_of_nonneg_right (by exact_mod_cast hq1) hB.le
        have hnonpos : pts i μ - pts j μ - (k : ℝ) * B ≤ 0 := by linarith
        rw [abs_of_nonpos hnonpos, neg_sub]
        exact le_trans (min_le_right _ _) (by linarith)
    exact torusCoord_ne_of_torus_sep (L N) (ha_pos N) hsep (congrFun hEq μ)
  let thresh : Fin m × Fin m → ℕ := fun p =>
    if h : p.1 = p.2 then 0 else Classical.choose (hpair p.1 p.2 h)
  refine ⟨Finset.univ.sup thresh, fun N hN i j hij => ?_⟩
  by_contra hne
  have hle : thresh (i, j) ≤ Finset.univ.sup thresh :=
    Finset.le_sup (f := thresh) (Finset.mem_univ (i, j))
  have hthresh : thresh (i, j) = Classical.choose (hpair i j hne) := by
    dsimp [thresh]
    exact dif_neg hne
  exact (Classical.choose_spec (hpair i j hne)) N (le_trans (hthresh ▸ hle) hN) hij

/-- Fundamental-domain special case: distinct points in `[0,B)^d` never wrap around. -/
theorem torus_eventually_injective_fundamental_domain
    {d m : ℕ} (B : ℝ) (hB : 0 < B)
    (L : ℕ → ℕ) [∀ N, NeZero (L N)] (a : ℕ → ℝ)
    (ha_pos : ∀ N, 0 < a N)
    (ha_zero : Filter.Tendsto a Filter.atTop (nhds 0))
    (hperiod : ∀ N, (L N : ℝ) * a N = B)
    (pts : Fin m → (Fin d → ℝ)) (hpts : Function.Injective pts)
    (hbox : ∀ i : Fin m, ∀ μ : Fin d, 0 ≤ pts i μ ∧ pts i μ < B) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, Function.Injective (torusSite (L N) (a N) ∘ pts) := by
  refine torus_eventually_injective_fixed_torus B hB L a ha_pos ha_zero hperiod pts ?_
  intro i j hij
  obtain ⟨μ, hμ⟩ := Function.ne_iff.mp (hpts.ne hij)
  refine ⟨μ, fun k hk => ?_⟩
  have hi := hbox i μ
  have hj := hbox j μ
  rcases lt_trichotomy k 0 with hk_neg | rfl | hk_pos
  · have hk1 : (k : ℝ) ≤ -1 := by exact_mod_cast Int.le_sub_one_of_lt hk_neg
    have : (k : ℝ) * B ≤ -B := by nlinarith
    linarith
  · simp only [Int.cast_zero, zero_mul, sub_eq_zero] at hk
    exact hμ hk
  · have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk_pos
    have : B ≤ (k : ℝ) * B := by nlinarith
    linarith

end Imscribing.YangMills.TorusWraparoundBridge
