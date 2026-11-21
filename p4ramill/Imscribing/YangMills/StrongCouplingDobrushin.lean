import Mathlib
import Imscribing.YangMills.OSCompletion
import Imscribing.YangMills.Wilson4DOp
import Imscribing.YangMills.FeynmanKac

set_option maxHeartbeats 250000
set_option synthInstance.maxHeartbeats 50000
set_option maxRecDepth 20000

open scoped InnerProductSpace
open Complex Finset Real MeasureTheory Set

namespace YangMills

/-! ## §43.  Volume-independent strong-coupling mass gap via Dobrushin expansion -/

section StrongCouplingDobrushin

/-- Inverse coordinate shift along `d : Fin 4` on `cubicTorus4 Ls Lt`. -/
def cubicShift4Inv (Ls Lt : ℕ) [NeZero Ls] [NeZero Lt] (d : Fin 4)
    (x : Fin Lt × Fin Ls × Fin Ls × Fin Ls) :
    Fin Lt × Fin Ls × Fin Ls × Fin Ls :=
  match d with
  | 0 => (x.1 - 1, x.2.1, x.2.2.1, x.2.2.2)
  | 1 => (x.1, x.2.1 - 1, x.2.2.1, x.2.2.2)
  | 2 => (x.1, x.2.1, x.2.2.1 - 1, x.2.2.2)
  | 3 => (x.1, x.2.1, x.2.2.1, x.2.2.2 - 1)

theorem cubicShift4_inv_cancel (Ls Lt : ℕ) [NeZero Ls] [NeZero Lt] (d : Fin 4)
    (x : (cubicTorus4 Ls Lt).Site) :
    cubicShift4 Ls Lt d (cubicShift4Inv Ls Lt d x) = x := by
  rcases x with ⟨t, a, b, c⟩
  fin_cases d <;> simp [cubicShift4, cubicShift4Inv]

/-- Plaquettes in `cubic4Plaquettes Ls Lt` incident to link `e`. -/
noncomputable def plaqsTouching (Ls Lt : ℕ) [NeZero Ls] [NeZero Lt]
    (e : (cubicTorus4 Ls Lt).Link) : List (LatticePlaquette (cubicTorus4 Ls Lt)) :=
  (cubic4Plaquettes Ls Lt).filter (fun p => decide (e ∈ p.loop.map Prod.fst))

/-- Plaquettes in `cubic4Plaquettes Ls Lt` disjoint from link `e`. -/
noncomputable def plaqsNotTouching (Ls Lt : ℕ) [NeZero Ls] [NeZero Lt]
    (e : (cubicTorus4 Ls Lt).Link) : List (LatticePlaquette (cubicTorus4 Ls Lt)) :=
  (cubic4Plaquettes Ls Lt).filter (fun p => !decide (e ∈ p.loop.map Prod.fst))

/-- Symmetric link-adjacency relation on `cubicTorus4 Ls Lt`: two distinct links sharing a plaquette. -/
def SharesPlaq4 (Ls Lt : ℕ) [NeZero Ls] [NeZero Lt]
    (e₁ e₂ : (cubicTorus4 Ls Lt).Link) : Prop :=
  e₁ ≠ e₂ ∧ ∃ p ∈ cubic4Plaquettes Ls Lt,
    e₁ ∈ p.loop.map Prod.fst ∧ e₂ ∈ p.loop.map Prod.fst

noncomputable instance instDecidableSharesPlaq4 (Ls Lt : ℕ) [NeZero Ls] [NeZero Lt] :
    DecidableRel (SharesPlaq4 Ls Lt) := fun e₁ e₂ => by
  unfold SharesPlaq4; infer_instance

theorem sharesPlaq4_symm (Ls Lt : ℕ) [NeZero Ls] [NeZero Lt]
    {e₁ e₂ : (cubicTorus4 Ls Lt).Link} (h : SharesPlaq4 Ls Lt e₁ e₂) :
    SharesPlaq4 Ls Lt e₂ e₁ :=
  ⟨h.1.symm, let ⟨p, hp, h1, h2⟩ := h.2; ⟨p, hp, h2, h1⟩⟩

theorem plaquette_mem_cubic4_characterize (Ls Lt : ℕ) [NeZero Ls] [NeZero Lt]
    {p : LatticePlaquette (cubicTorus4 Ls Lt)} (hp : p ∈ cubic4Plaquettes Ls Lt) :
    ∃ (x : (cubicTorus4 Ls Lt).Site) (d₁ d₂ : Fin 4),
      d₁ < d₂ ∧ p.loop = cubic4Plaquette x d₁ d₂ := by
  unfold cubic4Plaquettes at hp
  rw [List.mem_flatMap] at hp
  rcases hp with ⟨x, _, hp'⟩
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hp'
  rcases hp' with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨x, 0, 1, by decide, rfl⟩
  · exact ⟨x, 0, 2, by decide, rfl⟩
  · exact ⟨x, 0, 3, by decide, rfl⟩
  · exact ⟨x, 1, 2, by decide, rfl⟩
  · exact ⟨x, 1, 3, by decide, rfl⟩
  · exact ⟨x, 2, 3, by decide, rfl⟩

/-- Every link `e` belongs to at most `6` plaquettes in `cubic4Plaquettes Ls Lt`. -/
theorem plaqsTouching_length_le (Ls Lt : ℕ) [NeZero Ls] [NeZero Lt]
    (e : (cubicTorus4 Ls Lt).Link) :
    (plaqsTouching Ls Lt e).length ≤ 6 := by
  let S_idx := Finset.univ.filter (fun q : Fin 4 × Bool => q.1 ≠ e.2)
  have hS_card : S_idx.card = 6 := by
    dsimp [S_idx]
    have hd : e.2 ∈ Finset.univ := Finset.mem_univ _
    revert hd
    generalize e.2 = d
    intro _
    fin_cases d <;> decide
  let φ : Fin 4 × Bool → (cubicTorus4 Ls Lt).Site × Fin 4 × Fin 4 := fun q =>
    let y := if q.2 then cubicShift4Inv Ls Lt q.1 e.1 else e.1
    if e.2 < q.1 then (y, e.2, q.1) else (y, q.1, e.2)
  let key : LatticePlaquette (cubicTorus4 Ls Lt) →
      (cubicTorus4 Ls Lt).Site × Fin 4 × Fin 4 := fun p =>
    (p.base,
      (p.loop.head?.map (fun x => x.1.2)).getD 0,
      ((p.loop.drop 1).head?.map (fun x => x.1.2)).getD 0)
  have h_nodup_key : ((plaqsTouching Ls Lt e).map key).Nodup := by
    have h_all_nodup : ((cubic4Plaquettes Ls Lt).map key).Nodup := by
      unfold cubic4Plaquettes
      have h_flat : ∀ (xs : List (cubicTorus4 Ls Lt).Site), xs.Nodup →
          ((xs.flatMap fun x =>
            [ ({ base := x, loop := cubic4Plaquette x 0 1, is_closed := cubic4Plaquette_isPath x 0 1 } :
                  LatticePlaquette (cubicTorus4 Ls Lt)),
              { base := x, loop := cubic4Plaquette x 0 2, is_closed := cubic4Plaquette_isPath x 0 2 },
              { base := x, loop := cubic4Plaquette x 0 3, is_closed := cubic4Plaquette_isPath x 0 3 },
              { base := x, loop := cubic4Plaquette x 1 2, is_closed := cubic4Plaquette_isPath x 1 2 },
              { base := x, loop := cubic4Plaquette x 1 3, is_closed := cubic4Plaquette_isPath x 1 3 },
              { base := x, loop := cubic4Plaquette x 2 3, is_closed := cubic4Plaquette_isPath x 2 3 } ]).map key).Nodup := by
        intro xs hxs
        induction xs with
        | nil => simp
        | cons x xs ih =>
          rw [List.nodup_cons] at hxs
          rw [List.flatMap_cons, List.map_append, List.nodup_append]
          refine ⟨by simp [key, cubic4Plaquette], ih hxs.2, ?_⟩
          intro k hk1 b hb hkb
          subst hkb
          rw [List.mem_map] at hb
          rcases hb with ⟨p, hp, rfl⟩
          rw [List.mem_flatMap] at hp
          rcases hp with ⟨y, hy, hp'⟩
          have hxy : x ≠ y := fun heq => hxs.1 (heq ▸ hy)
          rcases List.mem_map.mp hk1 with ⟨px, hpx, h_eq⟩
          simp only [List.mem_cons, List.mem_nil_iff, or_false] at hpx
          have hkx : (key px).1 = x := by
            rcases hpx with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
          simp only [List.mem_cons, List.mem_nil_iff, or_false] at hp'
          have hby : (key p).1 = y := by
            rcases hp' with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
          exact hxy (hkx.symm.trans ((congrArg Prod.fst h_eq).trans hby))
      exact h_flat _ (Finset.nodup_toList _)
    exact h_all_nodup.sublist (List.Sublist.map key List.filter_sublist)
  have h_sub : ∀ k ∈ (plaqsTouching Ls Lt e).map key, k ∈ S_idx.image φ := by
    intro k hk
    rw [List.mem_map] at hk
    rcases hk with ⟨p, hp, rfl⟩
    rw [plaqsTouching, List.mem_filter] at hp
    have hp_mem := hp.1
    have he_mem : e ∈ p.loop.map Prod.fst := of_decide_eq_true hp.2
    unfold cubic4Plaquettes at hp_mem
    rw [List.mem_flatMap] at hp_mem
    rcases hp_mem with ⟨y, _, hp'⟩
    have h_case : ∀ (d₁ d₂ : Fin 4), d₁ < d₂ →
        p = { base := y, loop := cubic4Plaquette y d₁ d₂, is_closed := cubic4Plaquette_isPath y d₁ d₂ } →
        key p ∈ S_idx.image φ := by
      intro d₁ d₂ h12 hp_eq
      subst hp_eq
      simp only [cubic4Plaquette, List.map_cons, List.map_nil, List.mem_cons,
        List.mem_nil_iff, or_false] at he_mem
      change (y, d₁, d₂) ∈ S_idx.image φ
      rw [Finset.mem_image]
      rcases he_mem with h | h | h | h
      · have hy1 : y = e.1 := (congrArg Prod.fst h).symm
        have hd1 : d₁ = e.2 := (congrArg Prod.snd h).symm
        subst hy1; subst hd1
        refine ⟨(d₂, false), Finset.mem_filter.mpr ⟨Finset.mem_univ _, h12.ne'⟩, ?_⟩
        simp [φ, h12]
      · have hy1 : cubicShift4 Ls Lt d₁ y = e.1 := (congrArg Prod.fst h).symm
        have hd2 : d₂ = e.2 := (congrArg Prod.snd h).symm
        subst hd2
        have hy_inv : y = cubicShift4Inv Ls Lt d₁ e.1 := by
          rw [← hy1]; rcases y with ⟨t, a, b, c⟩; fin_cases d₁ <;> simp [cubicShift4, cubicShift4Inv]
        subst hy_inv
        refine ⟨(d₁, true), Finset.mem_filter.mpr ⟨Finset.mem_univ _, h12.ne⟩, ?_⟩
        simp [φ, not_lt_of_gt h12]
      · have hy2 : cubicShift4 Ls Lt d₂ y = e.1 := (congrArg Prod.fst h).symm
        have hd1 : d₁ = e.2 := (congrArg Prod.snd h).symm
        subst hd1
        have hy_inv : y = cubicShift4Inv Ls Lt d₂ e.1 := by
          rw [← hy2]; rcases y with ⟨t, a, b, c⟩; fin_cases d₂ <;> simp [cubicShift4, cubicShift4Inv]
        subst hy_inv
        refine ⟨(d₂, true), Finset.mem_filter.mpr ⟨Finset.mem_univ _, h12.ne'⟩, ?_⟩
        simp [φ, h12]
      · have hy1 : y = e.1 := (congrArg Prod.fst h).symm
        have hd2 : d₂ = e.2 := (congrArg Prod.snd h).symm
        subst hy1; subst hd2
        refine ⟨(d₁, false), Finset.mem_filter.mpr ⟨Finset.mem_univ _, h12.ne⟩, ?_⟩
        simp [φ, not_lt_of_gt h12]
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hp'
    rcases hp' with rfl | rfl | rfl | rfl | rfl | rfl
    · exact h_case 0 1 (by decide) rfl
    · exact h_case 0 2 (by decide) rfl
    · exact h_case 0 3 (by decide) rfl
    · exact h_case 1 2 (by decide) rfl
    · exact h_case 1 3 (by decide) rfl
    · exact h_case 2 3 (by decide) rfl
  have h_card_le : ((plaqsTouching Ls Lt e).map key).toFinset.card ≤ (S_idx.image φ).card :=
    Finset.card_le_card fun k hk => h_sub k ((List.mem_toFinset).mp hk)
  rw [List.toFinset_card_of_nodup h_nodup_key, List.length_map] at h_card_le
  exact h_card_le.trans (Finset.card_image_le.trans (le_of_eq hS_card))

/-- Volume-independent Dobrushin degree bound: every link has at most `18` plaquette-neighbors. -/
theorem sharesPlaq4_card_le (Ls Lt : ℕ) [NeZero Ls] [NeZero Lt]
    (e : (cubicTorus4 Ls Lt).Link) :
    (Finset.univ.filter (SharesPlaq4 Ls Lt e)).card ≤ 18 := by
  classical
  let S_nb := (plaqsTouching Ls Lt e).toFinset.biUnion
    (fun p => ((p.loop.map Prod.fst).filter (fun e' => decide (e' ≠ e))).toFinset)
  have h_sub : Finset.univ.filter (SharesPlaq4 Ls Lt e) ⊆ S_nb := by
    intro e' he'
    rw [Finset.mem_filter] at he'
    rcases he'.2 with ⟨hne, p, hp, he_p, he'_p⟩
    rw [Finset.mem_biUnion]
    refine ⟨p, List.mem_toFinset.mpr (List.mem_filter.mpr ⟨hp, decide_eq_true he_p⟩), ?_⟩
    rw [List.mem_toFinset, List.mem_filter]
    exact ⟨he'_p, decide_eq_true hne.symm⟩
  have h_each_le : ∀ p ∈ (plaqsTouching Ls Lt e).toFinset,
      ((p.loop.map Prod.fst).filter (fun e' => decide (e' ≠ e))).toFinset.card ≤ 3 := by
    intro p hp
    rw [List.mem_toFinset, plaqsTouching, List.mem_filter] at hp
    rcases plaquette_mem_cubic4_characterize Ls Lt hp.1 with ⟨x, d₁, d₂, _, hp_loop⟩
    have he_p : e ∈ p.loop.map Prod.fst := of_decide_eq_true hp.2
    have h_len4 : (p.loop.map Prod.fst).length = 4 := by rw [hp_loop]; simp [cubic4Plaquette]
    have h_erase : ((p.loop.map Prod.fst).filter (fun e' => decide (e' ≠ e))).length ≤ 3 := by
      have h_le_erase : ∀ l : List (cubicTorus4 Ls Lt).Link,
          (l.filter (fun e' => decide (e' ≠ e))).length ≤ (l.erase e).length := by
        intro l
        induction l with
        | nil => simp
        | cons a tl ih =>
          by_cases ha : a = e
          · subst ha
            simp only [List.filter_cons, ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true,
              ↓reduceIte, List.erase_cons_head]
            exact List.length_filter_le _ _
          · simp only [List.filter_cons, ne_eq, ha, not_false_eq_true, decide_true, ↓reduceIte,
              List.erase_cons, beq_false_of_ne ha, ↓reduceIte, List.length_cons]
            exact Nat.succ_le_succ ih
      have h_erase_len := h_le_erase (p.loop.map Prod.fst)
      rw [List.length_erase_of_mem he_p, h_len4] at h_erase_len
      exact h_erase_len
    exact (List.toFinset_card_le _).trans h_erase
  calc (Finset.univ.filter (SharesPlaq4 Ls Lt e)).card
      ≤ S_nb.card := Finset.card_le_card h_sub
    _ ≤ ∑ p ∈ (plaqsTouching Ls Lt e).toFinset,
          ((p.loop.map Prod.fst).filter (fun e' => decide (e' ≠ e))).toFinset.card :=
          Finset.card_biUnion_le
    _ ≤ ∑ _p ∈ (plaqsTouching Ls Lt e).toFinset, 3 := Finset.sum_le_sum h_each_le
    _ = (plaqsTouching Ls Lt e).toFinset.card * 3 := by simp [Finset.sum_const]
    _ ≤ (plaqsTouching Ls Lt e).length * 3 :=
          Nat.mul_le_mul_right 3 (List.toFinset_card_le _)
    _ ≤ 6 * 3 := Nat.mul_le_mul_right 3 (plaqsTouching_length_le Ls Lt e)

/-- Walk of length `n` in the `SharesPlaq4` plaquette-adjacency graph. -/
inductive PlaqWalk (Ls Lt : ℕ) [NeZero Ls] [NeZero Lt] :
    ℕ → (cubicTorus4 Ls Lt).Link → (cubicTorus4 Ls Lt).Link → Prop
  | zero (e : (cubicTorus4 Ls Lt).Link) : PlaqWalk Ls Lt 0 e e
  | step {n : ℕ} {e₁ e₂ e₃ : (cubicTorus4 Ls Lt).Link} :
      SharesPlaq4 Ls Lt e₁ e₂ → PlaqWalk Ls Lt n e₂ e₃ → PlaqWalk Ls Lt (n + 1) e₁ e₃

theorem plaqWalk_trans {Ls Lt : ℕ} [NeZero Ls] [NeZero Lt]
    {m n : ℕ} {e₁ e₂ e₃ : (cubicTorus4 Ls Lt).Link}
    (h1 : PlaqWalk Ls Lt m e₁ e₂) (h2 : PlaqWalk Ls Lt n e₂ e₃) :
    PlaqWalk Ls Lt (m + n) e₁ e₃ := by
  induction h1 with
  | zero _ => simpa using h2
  | step h12 _ ih =>
    rw [Nat.add_right_comm]
    exact PlaqWalk.step h12 (ih h2)

open Classical in
/-- Plaquette graph distance from link `e` to link set `S` on `cubicTorus4 Ls Lt`. -/
noncomputable def plaqDist4 (Ls Lt : ℕ) [NeZero Ls] [NeZero Lt]
    (S : Finset (cubicTorus4 Ls Lt).Link) (e : (cubicTorus4 Ls Lt).Link) : ℕ :=
  if h : ∃ k, ∃ e₀ ∈ S, PlaqWalk Ls Lt k e e₀ then Nat.find h else 0

theorem plaqDist4_mem {Ls Lt : ℕ} [NeZero Ls] [NeZero Lt]
    {S : Finset (cubicTorus4 Ls Lt).Link} {e : (cubicTorus4 Ls Lt).Link} (he : e ∈ S) :
    plaqDist4 Ls Lt S e = 0 := by
  classical
  have hex : ∃ k, ∃ e₀ ∈ S, PlaqWalk Ls Lt k e e₀ := ⟨0, e, he, PlaqWalk.zero e⟩
  dsimp [plaqDist4]
  rw [dif_pos hex]
  exact Nat.eq_zero_of_le_zero (Nat.find_min' hex ⟨e, he, PlaqWalk.zero e⟩)

theorem plaqDist4_adj_le {Ls Lt : ℕ} [NeZero Ls] [NeZero Lt]
    (S : Finset (cubicTorus4 Ls Lt).Link)
    {e₁ e₂ : (cubicTorus4 Ls Lt).Link} (hadj : SharesPlaq4 Ls Lt e₁ e₂)
    (h_reach : ∃ k, ∃ e₀ ∈ S, PlaqWalk Ls Lt k e₂ e₀) :
    plaqDist4 Ls Lt S e₁ ≤ plaqDist4 Ls Lt S e₂ + 1 := by
  classical
  have hex1 : ∃ k, ∃ e₀ ∈ S, PlaqWalk Ls Lt k e₁ e₀ := by
    rcases h_reach with ⟨k, e₀, he₀, hw⟩
    exact ⟨k + 1, e₀, he₀, PlaqWalk.step hadj hw⟩
  have h2_spec := Nat.find_spec h_reach
  rcases h2_spec with ⟨e₀, he₀, hw2⟩
  dsimp [plaqDist4]
  rw [dif_pos hex1, dif_pos h_reach]
  exact Nat.find_min' hex1 ⟨e₀, he₀, PlaqWalk.step hadj hw2⟩

/-- Single-link oscillation `δ_e(f)` of a gauge-field observable `f`. -/
noncomputable def linkOsc {Ls Lt N : ℕ} [NeZero Ls] [NeZero Lt]
    (f : GaugeField (cubicTorus4 Ls Lt) (Matrix.specialUnitaryGroup (Fin N) ℂ) → ℂ)
    (e : (cubicTorus4 Ls Lt).Link) : ℝ :=
  sSup { r : ℝ | ∃ U V, (∀ e', e' ≠ e → U e' = V e') ∧ r = ‖f U - f V‖ }

theorem linkOsc_nonneg {Ls Lt N : ℕ} [NeZero Ls] [NeZero Lt]
    (f : GaugeField (cubicTorus4 Ls Lt) (Matrix.specialUnitaryGroup (Fin N) ℂ) → ℂ)
    (M : ℝ) (hbd : ∀ U, ‖f U‖ ≤ M) (e : (cubicTorus4 Ls Lt).Link) :
    0 ≤ linkOsc f e := by
  let S := { r : ℝ | ∃ U V, (∀ e', e' ≠ e → U e' = V e') ∧ r = ‖f U - f V‖ }
  have h0 : (0 : ℝ) ∈ S := ⟨fun _ => 1, fun _ => 1, fun _ _ => rfl, by simp⟩
  have hbdd : BddAbove S := ⟨2 * M, fun r hr => by
    rcases hr with ⟨U, V, _, rfl⟩
    calc ‖f U - f V‖ ≤ ‖f U‖ + ‖f V‖ := norm_sub_le _ _
      _ ≤ M + M := add_le_add (hbd U) (hbd V)
      _ = 2 * M := by ring⟩
  exact le_csSup hbdd h0

theorem norm_sub_le_linkOsc {Ls Lt N : ℕ} [NeZero Ls] [NeZero Lt]
    (f : GaugeField (cubicTorus4 Ls Lt) (Matrix.specialUnitaryGroup (Fin N) ℂ) → ℂ)
    (M : ℝ) (hbd : ∀ U, ‖f U‖ ≤ M) (e : (cubicTorus4 Ls Lt).Link)
    {U V : GaugeField (cubicTorus4 Ls Lt) (Matrix.specialUnitaryGroup (Fin N) ℂ)}
    (hUV : ∀ e', e' ≠ e → U e' = V e') :
    ‖f U - f V‖ ≤ linkOsc f e := by
  let S := { r : ℝ | ∃ U V, (∀ e', e' ≠ e → U e' = V e') ∧ r = ‖f U - f V‖ }
  have hbdd : BddAbove S := ⟨2 * M, fun r hr => by
    rcases hr with ⟨U', V', _, rfl⟩
    calc ‖f U' - f V'‖ ≤ ‖f U'‖ + ‖f V'‖ := norm_sub_le _ _
      _ ≤ M + M := add_le_add (hbd U') (hbd V')
      _ = 2 * M := by ring⟩
  exact le_csSup hbdd ⟨U, V, hUV, rfl⟩

theorem linkOsc_le_two_mul {Ls Lt N : ℕ} [NeZero Ls] [NeZero Lt]
    (f : GaugeField (cubicTorus4 Ls Lt) (Matrix.specialUnitaryGroup (Fin N) ℂ) → ℂ)
    (M : ℝ) (hM : 0 ≤ M) (hbd : ∀ U, ‖f U‖ ≤ M) (e : (cubicTorus4 Ls Lt).Link) :
    linkOsc f e ≤ 2 * M := by
  let S := { r : ℝ | ∃ U V, (∀ e', e' ≠ e → U e' = V e') ∧ r = ‖f U - f V‖ }
  have hne : S.Nonempty := ⟨0, fun _ => 1, fun _ => 1, fun _ _ => rfl, by simp⟩
  refine csSup_le hne fun r hr => ?_
  rcases hr with ⟨U, V, _, rfl⟩
  calc ‖f U - f V‖ ≤ ‖f U‖ + ‖f V‖ := norm_sub_le _ _
    _ ≤ M + M := add_le_add (hbd U) (hbd V)
    _ = 2 * M := by ring

/--
Single-link complex total-variation contraction for two conditional densities
bounded below by `c > 0` on `SU(N)` with respect to `suHaar N`:
`‖∫ u, f u * (ρ₁ u - ρ₂ u) d(suHaar N)‖ ≤ (1 - c) * osc(f)`.
-/
theorem condDensity_tv_bound {N : ℕ}
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (f : Matrix.specialUnitaryGroup (Fin N) ℂ → ℂ)
    (hf_m : Measurable f) (D : ℝ) (hD_nn : 0 ≤ D)
    (hf_osc : ∀ u v, ‖f u - f v‖ ≤ D)
    (M_f : ℝ) (hf_bd : ∀ u, ‖f u‖ ≤ M_f)
    (ρ₁ ρ₂ : Matrix.specialUnitaryGroup (Fin N) ℂ → ℝ)
    (hρ1_m : Measurable ρ₁) (hρ2_m : Measurable ρ₂)
    (c : ℝ) (hc_nn : 0 ≤ c) (hc_le1 : c ≤ 1)
    (hρ1_lb : ∀ u, c ≤ ρ₁ u) (hρ2_lb : ∀ u, c ≤ ρ₂ u)
    (hρ1_ub : ∀ u, ρ₁ u ≤ c⁻¹) (hρ2_ub : ∀ u, ρ₂ u ≤ c⁻¹)
    (hρ1_int : ∫ u, ρ₁ u ∂(suHaar N) = 1)
    (hρ2_int : ∫ u, ρ₂ u ∂(suHaar N) = 1) :
    ‖∫ u, ((ρ₁ u - ρ₂ u : ℝ) : ℂ) * f u ∂(suHaar N)‖ ≤ (1 - c) * D := by
  have hM_f : 0 ≤ M_f := (norm_nonneg (f 1)).trans (hf_bd 1)
  have hmax_pos : 0 ≤ max c⁻¹ 1 := zero_le_one.trans (le_max_right c⁻¹ 1)
  let μ := suHaar N
  haveI := suHaar_prob N
  let m : Matrix.specialUnitaryGroup (Fin N) ℂ → ℝ := fun u => min (ρ₁ u) (ρ₂ u)
  let r₁ : Matrix.specialUnitaryGroup (Fin N) ℂ → ℝ := fun u => ρ₁ u - m u
  let r₂ : Matrix.specialUnitaryGroup (Fin N) ℂ → ℝ := fun u => ρ₂ u - m u
  have hm_m : Measurable m := hρ1_m.min hρ2_m
  have hr1_m : Measurable r₁ := hρ1_m.sub hm_m
  have hr2_m : Measurable r₂ := hρ2_m.sub hm_m
  have hr1_nn : ∀ u, 0 ≤ r₁ u := fun u => sub_nonneg.mpr (min_le_left _ _)
  have hr2_nn : ∀ u, 0 ≤ r₂ u := fun u => sub_nonneg.mpr (min_le_right _ _)
  have hr1_ub : ∀ u, r₁ u ≤ c⁻¹ := fun u => (sub_le_self _ (hc_nn.trans (le_min (hρ1_lb u) (hρ2_lb u)))).trans (hρ1_ub u)
  have hr2_ub : ∀ u, r₂ u ≤ c⁻¹ := fun u => (sub_le_self _ (hc_nn.trans (le_min (hρ1_lb u) (hρ2_lb u)))).trans (hρ2_ub u)
  have hm_int : MeasureTheory.Integrable m μ := by
    refine (MeasureTheory.integrable_const (max c⁻¹ 1)).mono' hm_m.stronglyMeasurable.aestronglyMeasurable ?_
    refine Filter.Eventually.of_forall fun u => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (hc_nn.trans (le_min (hρ1_lb u) (hρ2_lb u)))]
    exact le_max_of_le_left ((min_le_left _ _).trans (hρ1_ub u))
  have hρ1_int_m : MeasureTheory.Integrable ρ₁ μ := by
    refine (MeasureTheory.integrable_const (max c⁻¹ 1)).mono' hρ1_m.stronglyMeasurable.aestronglyMeasurable ?_
    refine Filter.Eventually.of_forall fun u => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (hc_nn.trans (hρ1_lb u))]; exact le_max_of_le_left (hρ1_ub u)
  have hρ2_int_m : MeasureTheory.Integrable ρ₂ μ := by
    refine (MeasureTheory.integrable_const (max c⁻¹ 1)).mono' hρ2_m.stronglyMeasurable.aestronglyMeasurable ?_
    refine Filter.Eventually.of_forall fun u => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (hc_nn.trans (hρ2_lb u))]; exact le_max_of_le_left (hρ2_ub u)
  have hr1_int_m : MeasureTheory.Integrable r₁ μ := hρ1_int_m.sub hm_int
  have hr2_int_m : MeasureTheory.Integrable r₂ μ := hρ2_int_m.sub hm_int
  let Z_r : ℝ := ∫ u, r₁ u ∂μ
  have hZr_eq : ∫ u, r₂ u ∂μ = Z_r := by
    dsimp [Z_r, r₁, r₂]
    rw [MeasureTheory.integral_sub hρ2_int_m hm_int, MeasureTheory.integral_sub hρ1_int_m hm_int,
      hρ2_int, hρ1_int]
  have hZr_nn : 0 ≤ Z_r := MeasureTheory.integral_nonneg hr1_nn
  have hZr_le : Z_r ≤ 1 - c := by
    dsimp [Z_r, r₁]
    rw [MeasureTheory.integral_sub hρ1_int_m hm_int, hρ1_int]
    have hm_ge : c ≤ ∫ u, m u ∂μ := by
      calc c = ∫ _u, c ∂μ := by simp [Measure.real, MeasureTheory.measure_univ]
        _ ≤ ∫ u, m u ∂μ := MeasureTheory.integral_mono (MeasureTheory.integrable_const c) hm_int
              (fun u => le_min (hρ1_lb u) (hρ2_lb u))
    linarith
  have h_split : (∫ u, ((ρ₁ u - ρ₂ u : ℝ) : ℂ) * f u ∂μ) =
      (∫ u, ((r₁ u : ℝ) : ℂ) * f u ∂μ) - (∫ u, ((r₂ u : ℝ) : ℂ) * f u ∂μ) := by
    have hr1_c : MeasureTheory.Integrable (fun u => ((r₁ u : ℝ) : ℂ) * f u) μ :=
      integrable_of_measurable_bound μ _ ((Complex.continuous_ofReal.measurable.comp hr1_m).mul hf_m)
        (max c⁻¹ 1 * M_f) fun u => by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hr1_nn u)]
        exact mul_le_mul (le_max_of_le_left (hr1_ub u)) (hf_bd u) (norm_nonneg _) (by positivity)
    have hr2_c : MeasureTheory.Integrable (fun u => ((r₂ u : ℝ) : ℂ) * f u) μ :=
      integrable_of_measurable_bound μ _ ((Complex.continuous_ofReal.measurable.comp hr2_m).mul hf_m)
        (max c⁻¹ 1 * M_f) fun u => by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hr2_nn u)]
        exact mul_le_mul (le_max_of_le_left (hr2_ub u)) (hf_bd u) (norm_nonneg _) (by positivity)
    rw [← MeasureTheory.integral_sub hr1_c hr2_c]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
    dsimp [r₁, r₂]; push_cast; ring
  rw [h_split]
  rcases eq_or_lt_of_le hZr_nn with hZ0 | hZ_pos
  · have hr1_zero : r₁ =ᵐ[μ] 0 :=
      (MeasureTheory.integral_eq_zero_iff_of_nonneg_ae (Filter.Eventually.of_forall hr1_nn) hr1_int_m).mp
        hZ0.symm
    have hr2_zero : r₂ =ᵐ[μ] 0 :=
      (MeasureTheory.integral_eq_zero_iff_of_nonneg_ae (Filter.Eventually.of_forall hr2_nn) hr2_int_m).mp
        (hZr_eq.trans hZ0.symm)
    have hi1 : ∫ u, ((r₁ u : ℝ) : ℂ) * f u ∂μ = 0 := by
      refine MeasureTheory.integral_eq_zero_of_ae ?_
      filter_upwards [hr1_zero] with u hu
      simp only [Pi.zero_apply] at hu
      have hu0 : r₁ u = 0 := hu
      rw [hu0, Complex.ofReal_zero, zero_mul]
      rfl
    have hi2 : ∫ u, ((r₂ u : ℝ) : ℂ) * f u ∂μ = 0 := by
      refine MeasureTheory.integral_eq_zero_of_ae ?_
      filter_upwards [hr2_zero] with u hu
      simp only [Pi.zero_apply] at hu
      have hu0 : r₂ u = 0 := hu
      rw [hu0, Complex.ofReal_zero, zero_mul]
      rfl
    rw [hi1, hi2, sub_zero, norm_zero]
    exact mul_nonneg (by linarith) hD_nn
  · have h_double :
        ((Z_r : ℝ) : ℂ) * ((∫ u, ((r₁ u : ℝ) : ℂ) * f u ∂μ) - (∫ v, ((r₂ v : ℝ) : ℂ) * f v ∂μ)) =
          ∫ p : Matrix.specialUnitaryGroup (Fin N) ℂ × Matrix.specialUnitaryGroup (Fin N) ℂ,
            ((r₁ p.1 * r₂ p.2 : ℝ) : ℂ) * (f p.1 - f p.2) ∂(μ.prod μ) := by
      have h_int_prod : MeasureTheory.Integrable
          (fun p : Matrix.specialUnitaryGroup (Fin N) ℂ × Matrix.specialUnitaryGroup (Fin N) ℂ =>
            ((r₁ p.1 * r₂ p.2 : ℝ) : ℂ) * (f p.1 - f p.2)) (μ.prod μ) := by
        have hm_p : Measurable (fun p : _ × _ => ((r₁ p.1 * r₂ p.2 : ℝ) : ℂ) * (f p.1 - f p.2)) :=
          (Complex.continuous_ofReal.measurable.comp
            ((hr1_m.comp measurable_fst).mul (hr2_m.comp measurable_snd))).mul
            ((hf_m.comp measurable_fst).sub (hf_m.comp measurable_snd))
        refine (MeasureTheory.integrable_const ((max c⁻¹ 1) ^ 2 * D)).mono'
          hm_p.stronglyMeasurable.aestronglyMeasurable ?_
        refine Filter.Eventually.of_forall fun p => ?_
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (mul_nonneg (hr1_nn p.1) (hr2_nn p.2)), sq]
        exact mul_le_mul (mul_le_mul (le_max_of_le_left (hr1_ub p.1))
            (le_max_of_le_left (hr2_ub p.2)) (hr2_nn p.2) (by positivity))
          (hf_osc p.1 p.2) (norm_nonneg _) (mul_nonneg hmax_pos hmax_pos)
      rw [MeasureTheory.integral_prod _ h_int_prod]
      have h_in : ∀ u,
          (∫ v, ((r₁ u * r₂ v : ℝ) : ℂ) * (f u - f v) ∂μ) =
            ((r₁ u : ℝ) : ℂ) * f u * ((Z_r : ℝ) : ℂ) -
              ((r₁ u : ℝ) : ℂ) * (∫ v, ((r₂ v : ℝ) : ℂ) * f v ∂μ) := by
        intro u
        have h1 : MeasureTheory.Integrable (fun v => ((r₁ u : ℝ) : ℂ) * f u * ((r₂ v : ℝ) : ℂ)) μ :=
          integrable_of_measurable_bound μ _
            (measurable_const.mul (Complex.continuous_ofReal.measurable.comp hr2_m))
            (max c⁻¹ 1 * M_f * max c⁻¹ 1) fun v => by
            rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
              Real.norm_eq_abs, abs_of_nonneg (hr1_nn u), abs_of_nonneg (hr2_nn v)]
            exact mul_le_mul (mul_le_mul (le_max_of_le_left (hr1_ub u)) (hf_bd u)
              (norm_nonneg _) (by positivity)) (le_max_of_le_left (hr2_ub v)) (hr2_nn v) (by positivity)
        have h2 : MeasureTheory.Integrable (fun v => ((r₁ u : ℝ) : ℂ) * (((r₂ v : ℝ) : ℂ) * f v)) μ :=
          integrable_of_measurable_bound μ _
            (measurable_const.mul ((Complex.continuous_ofReal.measurable.comp hr2_m).mul hf_m))
            (max c⁻¹ 1 * (max c⁻¹ 1 * M_f)) fun v => by
            rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
              Real.norm_eq_abs, abs_of_nonneg (hr1_nn u), abs_of_nonneg (hr2_nn v)]
            exact mul_le_mul (le_max_of_le_left (hr1_ub u))
              (mul_le_mul (le_max_of_le_left (hr2_ub v)) (hf_bd v) (norm_nonneg _) (by positivity))
              (mul_nonneg (hr2_nn v) (norm_nonneg _)) hmax_pos
        have h_sub_fn : (fun v => ((r₁ u * r₂ v : ℝ) : ℂ) * (f u - f v)) =
            fun v => ((r₁ u : ℝ) : ℂ) * f u * ((r₂ v : ℝ) : ℂ) -
              ((r₁ u : ℝ) : ℂ) * (((r₂ v : ℝ) : ℂ) * f v) := by
          funext v; push_cast; ring
        rw [h_sub_fn, MeasureTheory.integral_sub h1 h2, MeasureTheory.integral_const_mul,
          MeasureTheory.integral_const_mul]
        have h_r2_cast : (∫ v, ((r₂ v : ℝ) : ℂ) ∂μ) = ((Z_r : ℝ) : ℂ) := by
          have hr2c : MeasureTheory.Integrable (fun v => ((r₂ v : ℝ) : ℂ)) μ :=
            integrable_of_measurable_bound μ _ (Complex.continuous_ofReal.measurable.comp hr2_m)
              (max c⁻¹ 1) fun v => by
              rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hr2_nn v)]
              exact le_max_of_le_left (hr2_ub v)
          have hre : (∫ v, ((r₂ v : ℝ) : ℂ) ∂μ).re = Z_r := by
            change RCLike.re (∫ v, ((r₂ v : ℝ) : ℂ) ∂μ) = Z_r
            rw [← integral_re hr2c]; exact hZr_eq
          have him : (∫ v, ((r₂ v : ℝ) : ℂ) ∂μ).im = 0 := by
            have h1' : (∫ v, ((r₂ v : ℝ) : ℂ) ∂μ).im =
                RCLike.re (-Complex.I * ∫ v, ((r₂ v : ℝ) : ℂ) ∂μ) := by simp [Complex.mul_re]
            rw [h1', ← MeasureTheory.integral_const_mul, ← integral_re (hr2c.const_mul (-Complex.I))]
            refine MeasureTheory.integral_eq_zero_of_ae (Filter.Eventually.of_forall fun v => ?_)
            simp [Complex.mul_re]
          exact Complex.ext hre him
        rw [h_r2_cast]
      simp_rw [h_in]
      have h_out1 : MeasureTheory.Integrable (fun u => ((r₁ u : ℝ) : ℂ) * f u * ((Z_r : ℝ) : ℂ)) μ :=
        integrable_of_measurable_bound μ _
          (((Complex.continuous_ofReal.measurable.comp hr1_m).mul hf_m).mul measurable_const)
          (max c⁻¹ 1 * M_f * Z_r) fun u => by
          rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
            Real.norm_eq_abs, abs_of_nonneg (hr1_nn u), abs_of_nonneg hZr_nn]
          exact mul_le_mul (mul_le_mul (le_max_of_le_left (hr1_ub u)) (hf_bd u)
            (norm_nonneg _) (by positivity)) le_rfl hZr_nn (by positivity)
      have h_out2 : MeasureTheory.Integrable
          (fun u => ((r₁ u : ℝ) : ℂ) * ∫ v, ((r₂ v : ℝ) : ℂ) * f v ∂μ) μ :=
        integrable_of_measurable_bound μ _
          ((Complex.continuous_ofReal.measurable.comp hr1_m).mul measurable_const)
          (max c⁻¹ 1 * (max c⁻¹ 1 * M_f)) fun u => by
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hr1_nn u)]
          have hi2 : ‖∫ v, ((r₂ v : ℝ) : ℂ) * f v ∂μ‖ ≤ max c⁻¹ 1 * M_f := by
            calc ‖∫ v, ((r₂ v : ℝ) : ℂ) * f v ∂μ‖
                ≤ ∫ v, ‖((r₂ v : ℝ) : ℂ) * f v‖ ∂μ := MeasureTheory.norm_integral_le_integral_norm _
              _ ≤ ∫ _v, max c⁻¹ 1 * M_f ∂μ := by
                  refine MeasureTheory.integral_mono
                    (integrable_of_measurable_bound μ (fun v => ((r₂ v : ℝ) : ℂ) * f v)
                      ((Complex.continuous_ofReal.measurable.comp hr2_m).mul hf_m)
                      (max c⁻¹ 1 * M_f) fun v => by
                        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hr2_nn v)]
                        exact mul_le_mul (le_max_of_le_left (hr2_ub v)) (hf_bd v)
                          (norm_nonneg _) (by positivity)).norm
                    (MeasureTheory.integrable_const _) fun v => by
                    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hr2_nn v)]
                    exact mul_le_mul (le_max_of_le_left (hr2_ub v)) (hf_bd v)
                      (norm_nonneg _) (by positivity)
              _ = max c⁻¹ 1 * M_f := by simp [Measure.real, MeasureTheory.measure_univ]
          exact mul_le_mul (le_max_of_le_left (hr1_ub u)) hi2 (norm_nonneg _) (by positivity)
      rw [MeasureTheory.integral_sub h_out1 h_out2, MeasureTheory.integral_mul_const,
        MeasureTheory.integral_mul_const]
      have h_r1_cast : (∫ u, ((r₁ u : ℝ) : ℂ) ∂μ) = ((Z_r : ℝ) : ℂ) := by
        have hr1c : MeasureTheory.Integrable (fun u => ((r₁ u : ℝ) : ℂ)) μ :=
          integrable_of_measurable_bound μ _ (Complex.continuous_ofReal.measurable.comp hr1_m)
            (max c⁻¹ 1) fun u => by
            rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hr1_nn u)]
            exact le_max_of_le_left (hr1_ub u)
        have hre : (∫ u, ((r₁ u : ℝ) : ℂ) ∂μ).re = Z_r := by
          change RCLike.re (∫ u, ((r₁ u : ℝ) : ℂ) ∂μ) = Z_r
          rw [← integral_re hr1c]; rfl
        have him : (∫ u, ((r₁ u : ℝ) : ℂ) ∂μ).im = 0 := by
          have h1' : (∫ u, ((r₁ u : ℝ) : ℂ) ∂μ).im =
              RCLike.re (-Complex.I * ∫ u, ((r₁ u : ℝ) : ℂ) ∂μ) := by simp [Complex.mul_re]
          rw [h1', ← MeasureTheory.integral_const_mul, ← integral_re (hr1c.const_mul (-Complex.I))]
          refine MeasureTheory.integral_eq_zero_of_ae (Filter.Eventually.of_forall fun u => ?_)
          simp [Complex.mul_re]
        exact Complex.ext hre him
      rw [h_r1_cast]
      ring
    have h_norm_double :
        Z_r * ‖(∫ u, ((r₁ u : ℝ) : ℂ) * f u ∂μ) - (∫ v, ((r₂ v : ℝ) : ℂ) * f v ∂μ)‖ ≤
          Z_r ^ 2 * D := by
      have h_lhs : Z_r * ‖(∫ u, ((r₁ u : ℝ) : ℂ) * f u ∂μ) - (∫ v, ((r₂ v : ℝ) : ℂ) * f v ∂μ)‖ =
          ‖((Z_r : ℝ) : ℂ) * ((∫ u, ((r₁ u : ℝ) : ℂ) * f u ∂μ) - (∫ v, ((r₂ v : ℝ) : ℂ) * f v ∂μ))‖ := by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hZ_pos]
      rw [h_lhs, h_double]
      have h_int_r : MeasureTheory.Integrable (fun p : _ × _ => (r₁ p.1 * r₂ p.2) * D) (μ.prod μ) := by
        have h1 : MeasureTheory.Integrable (fun p : _ × _ => r₁ p.1 * r₂ p.2) (μ.prod μ) :=
          hr1_int_m.mul_prod hr2_int_m
        exact h1.mul_const D
      have h_int_norm : MeasureTheory.Integrable
          (fun p : _ × _ => ‖((r₁ p.1 * r₂ p.2 : ℝ) : ℂ) * (f p.1 - f p.2)‖) (μ.prod μ) := by
        refine h_int_r.mono' ?_ ?_
        · exact ((Complex.continuous_ofReal.measurable.comp
            ((hr1_m.comp measurable_fst).mul (hr2_m.comp measurable_snd))).mul
            ((hf_m.comp measurable_fst).sub
              (hf_m.comp measurable_snd))).stronglyMeasurable.aestronglyMeasurable.norm
        · refine Filter.Eventually.of_forall fun p => ?_
          rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _), norm_mul, Complex.norm_real,
            Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hr1_nn p.1) (hr2_nn p.2))]
          exact mul_le_mul_of_nonneg_left (hf_osc p.1 p.2) (mul_nonneg (hr1_nn p.1) (hr2_nn p.2))
      calc ‖∫ p, ((r₁ p.1 * r₂ p.2 : ℝ) : ℂ) * (f p.1 - f p.2) ∂(μ.prod μ)‖
          ≤ ∫ p, ‖((r₁ p.1 * r₂ p.2 : ℝ) : ℂ) * (f p.1 - f p.2)‖ ∂(μ.prod μ) :=
              MeasureTheory.norm_integral_le_integral_norm _
        _ ≤ ∫ p, (r₁ p.1 * r₂ p.2) * D ∂(μ.prod μ) := by
              refine MeasureTheory.integral_mono h_int_norm h_int_r fun p => ?_
              rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
                abs_of_nonneg (mul_nonneg (hr1_nn p.1) (hr2_nn p.2))]
              exact mul_le_mul_of_nonneg_left (hf_osc p.1 p.2)
                (mul_nonneg (hr1_nn p.1) (hr2_nn p.2))
        _ = (∫ p, r₁ p.1 * r₂ p.2 ∂(μ.prod μ)) * D := MeasureTheory.integral_mul_const _ _
        _ = Z_r ^ 2 * D := by
              rw [MeasureTheory.integral_prod _ (hr1_int_m.mul_prod hr2_int_m)]
              simp_rw [MeasureTheory.integral_const_mul, hZr_eq, MeasureTheory.integral_mul_const]
              change (Z_r * Z_r) * D = Z_r ^ 2 * D
              rw [sq]
    have h_div : ‖(∫ u, ((r₁ u : ℝ) : ℂ) * f u ∂μ) - (∫ v, ((r₂ v : ℝ) : ℂ) * f v ∂μ)‖ ≤
        Z_r * D := by
      have h1 : Z_r * ‖(∫ u, ((r₁ u : ℝ) : ℂ) * f u ∂μ) - (∫ v, ((r₂ v : ℝ) : ℂ) * f v ∂μ)‖ ≤
          Z_r * (Z_r * D) := by linarith [h_norm_double]
      exact le_of_mul_le_mul_left h1 hZ_pos
    exact h_div.trans (mul_le_mul_of_nonneg_right hZr_le hD_nn)

/-- Single-link conditional Boltzmann expectation `E_e f` on `cubicTorus4 Ls Lt`. -/
noncomputable def condGibbsExp (Ls Lt N : ℕ) [NeZero Ls] [NeZero Lt] (β : ℝ)
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (e : (cubicTorus4 Ls Lt).Link)
    (f : GaugeField (cubicTorus4 Ls Lt) (Matrix.specialUnitaryGroup (Fin N) ℂ) → ℂ)
    (U : GaugeField (cubicTorus4 Ls Lt) (Matrix.specialUnitaryGroup (Fin N) ℂ)) : ℂ :=
  let w_loc : Matrix.specialUnitaryGroup (Fin N) ℂ → ℝ := fun u =>
    Real.exp (-(β * ((plaqsTouching Ls Lt e).map
      (fun p => wilsonPlaquetteTerm p (Function.update U e u))).sum))
  let Z_loc : ℝ := ∫ u, w_loc u ∂(suHaar N)
  ((Z_loc⁻¹ : ℝ) : ℂ) * ∫ u, ((w_loc u : ℝ) : ℂ) * f (Function.update U e u) ∂(suHaar N)

theorem localPlaqSum_bounds (Ls Lt N : ℕ) [NeZero Ls] [NeZero Lt]
    (e : (cubicTorus4 Ls Lt).Link)
    (U : GaugeField (cubicTorus4 Ls Lt) (Matrix.specialUnitaryGroup (Fin N) ℂ)) :
    0 ≤ ((plaqsTouching Ls Lt e).map (fun p => wilsonPlaquetteTerm p U)).sum ∧
    ((plaqsTouching Ls Lt e).map (fun p => wilsonPlaquetteTerm p U)).sum ≤ 12 := by
  have h_gen : ∀ (ps : List (LatticePlaquette (cubicTorus4 Ls Lt))),
      0 ≤ (ps.map (fun p => wilsonPlaquetteTerm p U)).sum ∧
      (ps.map (fun p => wilsonPlaquetteTerm p U)).sum ≤ 2 * (ps.length : ℝ) := by
    intro ps
    induction ps with
    | nil => simp
    | cons p ps ih =>
      simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.cast_add, Nat.cast_one]
      have hp := wilsonPlaquetteTerm_bounds p U
      exact ⟨add_nonneg hp.1 ih.1, by linarith⟩
  have h1 := h_gen (plaqsTouching Ls Lt e)
  have hlen : ((plaqsTouching Ls Lt e).length : ℝ) ≤ 6 := by
    exact_mod_cast plaqsTouching_length_le Ls Lt e
  exact ⟨h1.1, h1.2.trans (by linarith)⟩

theorem condGibbsExp_tower (Ls Lt N : ℕ) [NeZero Ls] [NeZero Lt]
    (β : ℝ) (hβ : 0 ≤ β)
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (e : (cubicTorus4 Ls Lt).Link)
    (f : GaugeField (cubicTorus4 Ls Lt) (Matrix.specialUnitaryGroup (Fin N) ℂ) → ℂ)
    (hf_m : Measurable f) (M : ℝ) (hM : 0 ≤ M) (hf_bd : ∀ U, ‖f U‖ ≤ M) :
    cubic4Schwinger Ls Lt N β 1 ![condGibbsExp Ls Lt N β e f] =
      cubic4Schwinger Ls Lt N β 1 ![f] := by
  let G := Matrix.specialUnitaryGroup (Fin N) ℂ
  let G_4 := GaugeField (cubicTorus4 Ls Lt) G
  let μ_4 := spacetimeHaarMeasure Ls Lt N
  haveI := suHaar_prob N
  haveI := spacetimeHaarMeasure_prob Ls Lt N
  unfold cubic4Schwinger
  congr 1
  simp only [Fin.prod_univ_one, Matrix.cons_val_zero]
  let eqv := MeasurableEquiv.piEquivPiSubtypeProd (fun _ : (cubicTorus4 Ls Lt).Link => G)
    (fun e' => e' ≠ e)
  have mp := MeasureTheory.measurePreserving_piEquivPiSubtypeProd
    (fun _ : (cubicTorus4 Ls Lt).Link => suHaar N) (fun e' => e' ≠ e)
  haveI : Unique { e' : (cubicTorus4 Ls Lt).Link // ¬ (e' ≠ e) } :=
    ⟨⟨⟨e, not_not.mpr rfl⟩⟩, fun ⟨e', he'⟩ => by apply Subtype.ext; exact not_not.mp he'⟩
  let eqv_e : ({ e' : (cubicTorus4 Ls Lt).Link // ¬ (e' ≠ e) } → G) ≃ᵐ G :=
    { toFun := fun g => g default
      invFun := fun a _ => a
      left_inv := fun g => by funext i; rw [Unique.eq_default i]
      right_inv := fun _ => rfl
      measurable_toFun := measurable_pi_apply default
      measurable_invFun := measurable_pi_iff.mpr fun _ => measurable_id }
  let μ_off := MeasureTheory.Measure.pi (fun _ : { e' : (cubicTorus4 Ls Lt).Link // e' ≠ e } => suHaar N)
  let μ_e := MeasureTheory.Measure.pi (fun _ : { e' : (cubicTorus4 Ls Lt).Link // ¬ (e' ≠ e) } => suHaar N)
  haveI : MeasureTheory.IsProbabilityMeasure μ_off := by dsimp [μ_off]; infer_instance
  haveI : MeasureTheory.IsProbabilityMeasure μ_e := by dsimp [μ_e]; infer_instance
  have mp_e : MeasureTheory.MeasurePreserving eqv_e μ_e (suHaar N) := by
    refine ⟨eqv_e.measurable, ?_⟩
    ext s hs
    rw [MeasureTheory.Measure.map_apply eqv_e.measurable hs]
    have hpre : eqv_e ⁻¹' s = Set.pi Set.univ (fun _ => s) := by
      ext f
      simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, forall_true_left, eqv_e,
        MeasurableEquiv.coe_mk, Equiv.coe_fn_mk]
      exact ⟨fun h i => (Unique.eq_default i).symm ▸ h, fun h => h default⟩
    rw [hpre, MeasureTheory.Measure.pi_pi]
    simp [Finset.prod_const]
    rfl
  have h_split_act : ∀ U : G_4,
      wilsonAction β (cubic4Plaquettes Ls Lt) U =
        β * ((plaqsTouching Ls Lt e).map (fun p => wilsonPlaquetteTerm p U)).sum +
        β * ((plaqsNotTouching Ls Lt e).map (fun p => wilsonPlaquetteTerm p U)).sum := by
    intro U
    unfold wilsonAction plaqsTouching plaqsNotTouching
    rw [← mul_add]
    congr 1
    have h_part : ∀ (ps : List (LatticePlaquette (cubicTorus4 Ls Lt)))
        (P : LatticePlaquette (cubicTorus4 Ls Lt) → Bool),
        ((ps.filter P).map (fun p => wilsonPlaquetteTerm p U)).sum +
          ((ps.filter (fun p => !P p)).map (fun p => wilsonPlaquetteTerm p U)).sum =
          (ps.map (fun p => wilsonPlaquetteTerm p U)).sum := by
      intro ps P
      induction ps with
      | nil => simp
      | cons p ps ih =>
        by_cases hP : P p = true
        · simp only [List.filter_cons, hP, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
            List.map_cons, List.sum_cons]
          linarith
        · have hPf : P p = false := Bool.eq_false_iff.mpr hP
          simp only [List.filter_cons, hPf, Bool.false_eq_true, ↓reduceIte, Bool.not_false,
            List.map_cons, List.sum_cons]
          linarith
    exact (h_part _ _).symm
  have h_ext_indep : ∀ (U : G_4) (u : G),
      ((plaqsNotTouching Ls Lt e).map (fun p => wilsonPlaquetteTerm p (Function.update U e u))).sum =
      ((plaqsNotTouching Ls Lt e).map (fun p => wilsonPlaquetteTerm p U)).sum := by
    intro U u
    congr 1
    refine List.map_congr_left fun p hp => ?_
    rw [plaqsNotTouching, List.mem_filter] at hp
    have hnot : e ∉ p.loop.map Prod.fst := by
      intro hm; simp [hm] at hp
    refine wilsonPlaquetteTerm_depends_on_links p (Function.update U e u) U fun e' b hm => ?_
    have hne : e' ≠ e := fun heq => hnot (heq ▸ List.mem_map.mpr ⟨(e', b), hm, rfl⟩)
    exact Function.update_of_ne hne u U
  have h_upd_eq : ∀ (q1 : { e' : (cubicTorus4 Ls Lt).Link // e' ≠ e } → G) (q2 : { e' // ¬ (e' ≠ e) } → G),
      Function.update (eqv.symm (q1, q2)) e (eqv_e q2) = eqv.symm (q1, q2) := by
    intro q1 q2
    funext e'
    by_cases h : e' = e
    · rw [h, Function.update_self]
      change eqv_e q2 = (MeasurableEquiv.piEquivPiSubtypeProd
        (fun _ : (cubicTorus4 Ls Lt).Link => G) (fun e' => e' ≠ e)).symm (q1, q2) e
      simp [eqv_e]
      exact congrArg q2 (Subsingleton.elim _ _)
    · rw [Function.update_of_ne h]
  have h_upd_indep : ∀ (q1 : { e' : (cubicTorus4 Ls Lt).Link // e' ≠ e } → G)
      (q2 : { e' // ¬ (e' ≠ e) } → G) (u : G),
      Function.update (eqv.symm (q1, q2)) e u =
        eqv.symm (q1, (fun _ => u)) := by
    intro q1 q2 u
    funext e'
    by_cases h : e' = e
    · rw [h, Function.update_self]
      change u = (MeasurableEquiv.piEquivPiSubtypeProd
        (fun _ : (cubicTorus4 Ls Lt).Link => G) (fun e' => e' ≠ e)).symm (q1, fun _ => u) e
      simp
    · rw [Function.update_of_ne h]
      change (MeasurableEquiv.piEquivPiSubtypeProd
          (fun _ : (cubicTorus4 Ls Lt).Link => G) (fun e' => e' ≠ e)).symm (q1, q2) e' =
        (MeasurableEquiv.piEquivPiSubtypeProd
          (fun _ : (cubicTorus4 Ls Lt).Link => G) (fun e' => e' ≠ e)).symm (q1, fun _ => u) e'
      simp [h]
  have h_ce_meas : Measurable (condGibbsExp Ls Lt N β e f) := by
    have hm_w : Measurable (fun q : G_4 × G =>
        Real.exp (-(β * ((plaqsTouching Ls Lt e).map
          (fun p => wilsonPlaquetteTerm p (Function.update q.1 e q.2))).sum))) := by
      have h_upd_m : Measurable (fun q : G_4 × G => Function.update q.1 e q.2) :=
        measurable_pi_iff.mpr fun e' => by
          by_cases h : e' = e
          · subst h; simp only [Function.update_self]; exact measurable_snd
          · simp only [Function.update_of_ne h]; exact (measurable_pi_apply e').comp measurable_fst
      have h_sum_m : Measurable (fun q : G_4 × G =>
          ((plaqsTouching Ls Lt e).map (fun p => wilsonPlaquetteTerm p (Function.update q.1 e q.2))).sum) := by
        clear h_split_act h_ext_indep h_upd_eq h_upd_indep
        induction (plaqsTouching Ls Lt e) with
        | nil => simp [measurable_const]
        | cons p ps ih =>
          simp only [List.map_cons, List.sum_cons]
          exact ((measurable_cubic4_plaquette_term Ls Lt N p).comp h_upd_m).add ih
      exact Real.continuous_exp.measurable.comp (Measurable.neg (measurable_const.mul h_sum_m))
    have hm_Z : Measurable (fun U : G_4 =>
        ∫ u : G, Real.exp (-(β * ((plaqsTouching Ls Lt e).map
          (fun p => wilsonPlaquetteTerm p (Function.update U e u))).sum)) ∂(suHaar N)) :=
      MeasureTheory.StronglyMeasurable.measurable
        (MeasureTheory.StronglyMeasurable.integral_prod_right' hm_w.stronglyMeasurable)
    have hm_num : Measurable (fun U : G_4 =>
        ∫ u : G, ((Real.exp (-(β * ((plaqsTouching Ls Lt e).map
          (fun p => wilsonPlaquetteTerm p (Function.update U e u))).sum)) : ℝ) : ℂ) *
          f (Function.update U e u) ∂(suHaar N)) := by
      have h_upd_m : Measurable (fun q : G_4 × G => Function.update q.1 e q.2) :=
        measurable_pi_iff.mpr fun e' => by
          by_cases h : e' = e
          · subst h; simp only [Function.update_self]; exact measurable_snd
          · simp only [Function.update_of_ne h]; exact (measurable_pi_apply e').comp measurable_fst
      exact MeasureTheory.StronglyMeasurable.measurable
        (MeasureTheory.StronglyMeasurable.integral_prod_right'
          ((Complex.continuous_ofReal.measurable.comp hm_w).mul (hf_m.comp h_upd_m)).stronglyMeasurable)
    exact (Complex.continuous_ofReal.measurable.comp hm_Z.inv).mul hm_num
  change (∫ U, condGibbsExp Ls Lt N β e f U * ((cubic4WilsonWeight Ls Lt N β U : ℝ) : ℂ)
      ∂(MeasureTheory.Measure.pi fun _ => suHaar N)) =
    ∫ U, f U * ((cubic4WilsonWeight Ls Lt N β U : ℝ) : ℂ)
      ∂(MeasureTheory.Measure.pi fun _ => suHaar N)
  rw [← (mp.symm).integral_comp' (fun U => condGibbsExp Ls Lt N β e f U *
    ((cubic4WilsonWeight Ls Lt N β U : ℝ) : ℂ)),
    ← (mp.symm).integral_comp' (fun U => f U * ((cubic4WilsonWeight Ls Lt N β U : ℝ) : ℂ))]
  have h_int_lhs : MeasureTheory.Integrable
      (fun q : ({ e' : (cubicTorus4 Ls Lt).Link // e' ≠ e } → G) × ({ e' // ¬ (e' ≠ e) } → G) =>
        condGibbsExp Ls Lt N β e f (eqv.symm q) *
          ((cubic4WilsonWeight Ls Lt N β (eqv.symm q) : ℝ) : ℂ)) (μ_off.prod μ_e) := by
    refine (MeasureTheory.integrable_const M).mono'
      ((h_ce_meas.comp eqv.symm.measurable).mul
        (Complex.continuous_ofReal.measurable.comp
          ((measurable_cubic4WilsonWeight Ls Lt N β).comp eqv.symm.measurable))).stronglyMeasurable.aestronglyMeasurable
      (Filter.Eventually.of_forall fun q => ?_)
    have h_ce_bd : ‖condGibbsExp Ls Lt N β e f (eqv.symm q)‖ ≤ M := by
      dsimp [condGibbsExp]
      let w_loc : G → ℝ := fun u =>
        Real.exp (-(β * ((plaqsTouching Ls Lt e).map
          (fun p => wilsonPlaquetteTerm p (Function.update (eqv.symm q) e u))).sum))
      have hw_nn : ∀ u, 0 ≤ w_loc u := fun u => (Real.exp_pos _).le
      have hw_lb : ∀ u, Real.exp (-12 * β) ≤ w_loc u := fun u => by
        have hb := (localPlaqSum_bounds Ls Lt N e (Function.update (eqv.symm q) e u)).2
        have := mul_le_mul_of_nonneg_left hb hβ
        exact Real.exp_le_exp.mpr (by linarith)
      have hw_ub : ∀ u, w_loc u ≤ 1 := fun u => by
        have hb := (localPlaqSum_bounds Ls Lt N e (Function.update (eqv.symm q) e u)).1
        have := mul_nonneg hβ hb
        exact Real.exp_le_one_iff.mpr (by linarith)
      have hw_m : Measurable w_loc := by
        have h_upd_m : Measurable (fun u : G => Function.update (eqv.symm q) e u) :=
          measurable_pi_iff.mpr fun e' => by
            by_cases h : e' = e
            · subst h; simp only [Function.update_self]; exact measurable_id
            · simp only [Function.update_of_ne h]; exact measurable_const
        have h_sum_m : Measurable (fun u : G =>
            ((plaqsTouching Ls Lt e).map (fun p => wilsonPlaquetteTerm p (Function.update (eqv.symm q) e u))).sum) := by
          clear h_split_act h_ext_indep h_upd_eq h_upd_indep
          induction (plaqsTouching Ls Lt e) with
          | nil => simp [measurable_const]
          | cons p ps ih =>
            simp only [List.map_cons, List.sum_cons]
            exact ((measurable_cubic4_plaquette_term Ls Lt N p).comp h_upd_m).add ih
        exact Real.continuous_exp.measurable.comp (Measurable.neg (measurable_const.mul h_sum_m))
      have hw_int : MeasureTheory.Integrable w_loc (suHaar N) :=
        (MeasureTheory.integrable_const (1 : ℝ)).mono' hw_m.stronglyMeasurable.aestronglyMeasurable
          (Filter.Eventually.of_forall fun u => by
            rw [Real.norm_eq_abs, abs_of_nonneg (hw_nn u)]; exact hw_ub u)
      have hZ_pos : 0 < ∫ u, w_loc u ∂(suHaar N) := by
        calc 0 < Real.exp (-12 * β) := Real.exp_pos _
          _ = ∫ _u, Real.exp (-12 * β) ∂(suHaar N) := by simp [Measure.real, MeasureTheory.measure_univ]
          _ ≤ ∫ u, w_loc u ∂(suHaar N) :=
              MeasureTheory.integral_mono (MeasureTheory.integrable_const _) hw_int hw_lb
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr hZ_pos.le)]
      have hm_num : Measurable (fun u : G => ((w_loc u : ℝ) : ℂ) * f (Function.update (eqv.symm q) e u)) :=
        (Complex.continuous_ofReal.measurable.comp hw_m).mul
          (hf_m.comp (measurable_pi_iff.mpr fun e' => by
            by_cases h : e' = e
            · subst h; simp only [Function.update_self]; exact measurable_id
            · simp only [Function.update_of_ne h]; exact measurable_const))
      have h_num_int : MeasureTheory.Integrable
          (fun u => ‖((w_loc u : ℝ) : ℂ) * f (Function.update (eqv.symm q) e u)‖) (suHaar N) :=
        (hw_int.mul_const M).mono' hm_num.stronglyMeasurable.aestronglyMeasurable.norm
          (Filter.Eventually.of_forall fun u => by
            rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _), norm_mul, Complex.norm_real,
              Real.norm_eq_abs, abs_of_nonneg (hw_nn u)]
            exact mul_le_mul_of_nonneg_left (hf_bd _) (hw_nn u))
      calc (∫ u, w_loc u ∂(suHaar N))⁻¹ * ‖∫ u, ((w_loc u : ℝ) : ℂ) * f (Function.update (eqv.symm q) e u) ∂(suHaar N)‖
          ≤ (∫ u, w_loc u ∂(suHaar N))⁻¹ * ∫ u, ‖((w_loc u : ℝ) : ℂ) * f (Function.update (eqv.symm q) e u)‖ ∂(suHaar N) :=
              mul_le_mul_of_nonneg_left (MeasureTheory.norm_integral_le_integral_norm _) (inv_nonneg.mpr hZ_pos.le)
        _ ≤ (∫ u, w_loc u ∂(suHaar N))⁻¹ * ∫ u, w_loc u * M ∂(suHaar N) := by
              refine mul_le_mul_of_nonneg_left (MeasureTheory.integral_mono h_num_int (hw_int.mul_const M)
                fun u => by
                  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hw_nn u)]
                  exact mul_le_mul_of_nonneg_left (hf_bd _) (hw_nn u)) (inv_nonneg.mpr hZ_pos.le)
        _ = M := by
              rw [MeasureTheory.integral_mul_const, ← mul_assoc, inv_mul_cancel₀ hZ_pos.ne', one_mul]
    have hwb := cubic4WilsonWeight_bounds Ls Lt N β hβ (eqv.symm q)
    have hwnn : 0 ≤ cubic4WilsonWeight Ls Lt N β (eqv.symm q) := by
      unfold cubic4WilsonWeight; exact (Real.exp_pos _).le
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hwnn]
    exact (mul_le_mul h_ce_bd hwb.2 hwnn hM).trans_eq (mul_one M)
  have h_int_rhs : MeasureTheory.Integrable
      (fun q : ({ e' : (cubicTorus4 Ls Lt).Link // e' ≠ e } → G) × ({ e' // ¬ (e' ≠ e) } → G) =>
        f (eqv.symm q) * ((cubic4WilsonWeight Ls Lt N β (eqv.symm q) : ℝ) : ℂ)) (μ_off.prod μ_e) := by
    refine (MeasureTheory.integrable_const M).mono'
      ((hf_m.comp eqv.symm.measurable).mul
        (Complex.continuous_ofReal.measurable.comp
          ((measurable_cubic4WilsonWeight Ls Lt N β).comp eqv.symm.measurable))).stronglyMeasurable.aestronglyMeasurable
      (Filter.Eventually.of_forall fun q => ?_)
    have hwb := cubic4WilsonWeight_bounds Ls Lt N β hβ (eqv.symm q)
    have hwnn : 0 ≤ cubic4WilsonWeight Ls Lt N β (eqv.symm q) := by
      unfold cubic4WilsonWeight; exact (Real.exp_pos _).le
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hwnn]
    exact (mul_le_mul (hf_bd _) hwb.2 hwnn hM).trans_eq (mul_one M)
  rw [MeasureTheory.integral_prod _ h_int_lhs, MeasureTheory.integral_prod _ h_int_rhs]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun q1 => ?_)
  let U_ref : G_4 := eqv.symm (q1, fun _ => 1)
  let w_ext : ℝ := Real.exp (-(β * ((plaqsNotTouching Ls Lt e).map (fun p => wilsonPlaquetteTerm p U_ref)).sum))
  let w_loc : G → ℝ := fun u =>
    Real.exp (-(β * ((plaqsTouching Ls Lt e).map (fun p => wilsonPlaquetteTerm p (Function.update U_ref e u))).sum))
  have h_rhs_upd : ∀ q2 : { e' // ¬ (e' ≠ e) } → G,
      eqv.symm (q1, q2) = Function.update U_ref e (eqv_e q2) := by
    intro q2
    rw [← h_upd_eq q1 q2, h_upd_indep q1 q2, ← h_upd_indep q1 (fun _ => 1)]
  have h_w_split : ∀ q2 : { e' // ¬ (e' ≠ e) } → G,
      cubic4WilsonWeight Ls Lt N β (eqv.symm (q1, q2)) = w_ext * w_loc (eqv_e q2) := by
    intro q2
    have hU := h_rhs_upd q2
    rw [hU]
    unfold cubic4WilsonWeight
    rw [h_split_act, h_ext_indep, neg_add, Real.exp_add]
    dsimp [w_ext, w_loc]
    ring
  have h_ce_const : ∀ q2 : { e' // ¬ (e' ≠ e) } → G,
      condGibbsExp Ls Lt N β e f (eqv.symm (q1, q2)) = condGibbsExp Ls Lt N β e f U_ref := by
    intro q2
    have h_fn_eq : ∀ u : G, Function.update (eqv.symm (q1, q2)) e u = Function.update U_ref e u := by
      intro u
      rw [h_upd_indep q1 q2 u, h_upd_indep q1 (fun _ => 1) u]
    dsimp [condGibbsExp]
    simp_rw [h_fn_eq]
  simp_rw [h_ce_const, h_w_split]
  rw [MeasureTheory.integral_const_mul,
    mp_e.integral_comp' (fun u => ((w_ext * w_loc u : ℝ) : ℂ))]
  simp_rw [h_rhs_upd]
  rw [mp_e.integral_comp' (fun u => f (Function.update U_ref e u) * ((w_ext * w_loc u : ℝ) : ℂ))]
  have h_f_eq : ∀ u : G, eqv.symm (q1, fun _ => u) = Function.update U_ref e u := fun u =>
    (h_upd_indep q1 (fun _ => 1) u).symm
  have h_w_int_c : (∫ u, ((w_loc u : ℝ) : ℂ) ∂(suHaar N)) = ((∫ u, w_loc u ∂(suHaar N) : ℝ) : ℂ) := by
    have hw_m : Measurable w_loc := by
      have h_upd_m : Measurable (fun u : G => Function.update U_ref e u) :=
        measurable_pi_iff.mpr fun e' => by
          by_cases h : e' = e
          · subst h; simp only [Function.update_self]; exact measurable_id
          · simp only [Function.update_of_ne h]; exact measurable_const
      have h_sum_m : Measurable (fun u : G =>
          ((plaqsTouching Ls Lt e).map (fun p => wilsonPlaquetteTerm p (Function.update U_ref e u))).sum) := by
        clear h_split_act h_ext_indep h_upd_eq h_upd_indep
        induction (plaqsTouching Ls Lt e) with
        | nil => simp [measurable_const]
        | cons p ps ih =>
          simp only [List.map_cons, List.sum_cons]
          exact ((measurable_cubic4_plaquette_term Ls Lt N p).comp h_upd_m).add ih
      exact Real.continuous_exp.measurable.comp (Measurable.neg (measurable_const.mul h_sum_m))
    have hwc : MeasureTheory.Integrable (fun u => ((w_loc u : ℝ) : ℂ)) (suHaar N) :=
      integrable_of_measurable_bound (suHaar N) _ (Complex.continuous_ofReal.measurable.comp hw_m) 1
        fun u => by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.exp_pos _).le]
        have hb := (localPlaqSum_bounds Ls Lt N e (Function.update U_ref e u)).1
        have h_prod : 0 ≤ β * ((plaqsTouching Ls Lt e).map (fun p => wilsonPlaquetteTerm p (Function.update U_ref e u))).sum :=
          mul_nonneg hβ hb
        exact Real.exp_le_one_iff.mpr (by linarith)
    have hre : (∫ u, ((w_loc u : ℝ) : ℂ) ∂(suHaar N)).re = ∫ u, w_loc u ∂(suHaar N) := by
      change RCLike.re (∫ u, ((w_loc u : ℝ) : ℂ) ∂(suHaar N)) = _
      rw [← integral_re hwc]; rfl
    have him : (∫ u, ((w_loc u : ℝ) : ℂ) ∂(suHaar N)).im = 0 := by
      have h1' : (∫ u, ((w_loc u : ℝ) : ℂ) ∂(suHaar N)).im =
          RCLike.re (-Complex.I * ∫ u, ((w_loc u : ℝ) : ℂ) ∂(suHaar N)) := by simp [Complex.mul_re]
      rw [h1', ← MeasureTheory.integral_const_mul, ← integral_re (hwc.const_mul (-Complex.I))]
      refine MeasureTheory.integral_eq_zero_of_ae (Filter.Eventually.of_forall fun u => ?_)
      simp [Complex.mul_re]
    exact Complex.ext hre him
  have hZ_pos : 0 < ∫ u, w_loc u ∂(suHaar N) := by
    have hw_m : Measurable w_loc := by
      have h_upd_m : Measurable (fun u : G => Function.update U_ref e u) :=
        measurable_pi_iff.mpr fun e' => by
          by_cases h : e' = e
          · subst h; simp only [Function.update_self]; exact measurable_id
          · simp only [Function.update_of_ne h]; exact measurable_const
      have h_sum_m : Measurable (fun u : G =>
          ((plaqsTouching Ls Lt e).map (fun p => wilsonPlaquetteTerm p (Function.update U_ref e u))).sum) := by
        clear h_split_act h_ext_indep h_upd_eq h_upd_indep
        induction (plaqsTouching Ls Lt e) with
        | nil => simp [measurable_const]
        | cons p ps ih =>
          simp only [List.map_cons, List.sum_cons]
          exact ((measurable_cubic4_plaquette_term Ls Lt N p).comp h_upd_m).add ih
      exact Real.continuous_exp.measurable.comp (Measurable.neg (measurable_const.mul h_sum_m))
    have hwi : MeasureTheory.Integrable w_loc (suHaar N) :=
      (MeasureTheory.integrable_const (1 : ℝ)).mono' hw_m.stronglyMeasurable.aestronglyMeasurable
        (Filter.Eventually.of_forall fun u => by
          rw [Real.norm_eq_abs, abs_of_nonneg (Real.exp_pos _).le]
          have hb := (localPlaqSum_bounds Ls Lt N e (Function.update U_ref e u)).1
          have := mul_nonneg hβ hb
          exact Real.exp_le_one_iff.mpr (by linarith))
    calc 0 < Real.exp (-12 * β) := Real.exp_pos _
      _ = ∫ _u, Real.exp (-12 * β) ∂(suHaar N) := by simp [Measure.real, MeasureTheory.measure_univ]
      _ ≤ ∫ u, w_loc u ∂(suHaar N) := MeasureTheory.integral_mono (MeasureTheory.integrable_const _) hwi
            (fun u => by
              have hb := (localPlaqSum_bounds Ls Lt N e (Function.update U_ref e u)).2
              have := mul_le_mul_of_nonneg_left hb hβ
              exact Real.exp_le_exp.mpr (by linarith))
  have h_lhs_simp : (∫ u, ((w_ext * w_loc u : ℝ) : ℂ) ∂(suHaar N)) =
      ((w_ext : ℝ) : ℂ) * ((∫ u, w_loc u ∂(suHaar N) : ℝ) : ℂ) := by
    simp_rw [Complex.ofReal_mul, MeasureTheory.integral_const_mul, h_w_int_c]
  have h_rhs_simp : (∫ u, f (Function.update U_ref e u) * ((w_ext * w_loc u : ℝ) : ℂ) ∂(suHaar N)) =
      ((w_ext : ℝ) : ℂ) * ∫ u, ((w_loc u : ℝ) : ℂ) * f (Function.update U_ref e u) ∂(suHaar N) := by
    rw [← MeasureTheory.integral_const_mul]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun u => by push_cast; ring)
  rw [h_lhs_simp, h_rhs_simp]
  have hZ_ne : (∫ u, w_loc u ∂(suHaar N)) ≠ 0 := hZ_pos.ne'
  have h_canc : (((∫ u, w_loc u ∂(suHaar N))⁻¹ : ℝ) : ℂ) *
      ((∫ u, w_loc u ∂(suHaar N) : ℝ) : ℂ) = 1 := by
    rw [← Complex.ofReal_mul, inv_mul_cancel₀ hZ_ne, Complex.ofReal_one]
  calc condGibbsExp Ls Lt N β e f U_ref * (((w_ext : ℝ) : ℂ) * ((∫ u, w_loc u ∂(suHaar N) : ℝ) : ℂ))
      = (((w_ext : ℝ) : ℂ) * (∫ u, ((w_loc u : ℝ) : ℂ) * f (Function.update U_ref e u) ∂(suHaar N))) *
          ((((∫ u, w_loc u ∂(suHaar N))⁻¹ : ℝ) : ℂ) * ((∫ u, w_loc u ∂(suHaar N) : ℝ) : ℂ)) := by
        dsimp [condGibbsExp]; ring
    _ = ((w_ext : ℝ) : ℂ) * ∫ u, ((w_loc u : ℝ) : ℂ) * f (Function.update U_ref e u) ∂(suHaar N) := by
        rw [h_canc, mul_one]

/-- Dobrushin interdependence coefficient `C_{e, e'} = 1 - exp(-12 β)` on plaquette-adjacent links. -/
noncomputable def dobrushinCoeff (Ls Lt : ℕ) [NeZero Ls] [NeZero Lt] (β : ℝ)
    (e e' : (cubicTorus4 Ls Lt).Link) : ℝ :=
  if SharesPlaq4 Ls Lt e e' then 1 - Real.exp (-12 * β) else 0

theorem dobrushinCoeff_row_sum_le (Ls Lt : ℕ) [NeZero Ls] [NeZero Lt] (β : ℝ) (hβ : 0 ≤ β)
    (e : (cubicTorus4 Ls Lt).Link) :
    ∑ e' : (cubicTorus4 Ls Lt).Link, dobrushinCoeff Ls Lt β e e' ≤ 18 * (1 - Real.exp (-12 * β)) := by
  have h1c : 0 ≤ 1 - Real.exp (-12 * β) := by
    linarith [Real.exp_le_one_iff.mpr (by linarith : -12 * β ≤ 0)]
  have h_sum_eq : ∑ e' : (cubicTorus4 Ls Lt).Link, dobrushinCoeff Ls Lt β e e' =
      ((Finset.univ.filter (SharesPlaq4 Ls Lt e)).card : ℝ) * (1 - Real.exp (-12 * β)) := by
    dsimp [dobrushinCoeff]
    rw [← Finset.sum_filter (p := fun e' => SharesPlaq4 Ls Lt e e')]
    rw [Finset.sum_const, nsmul_eq_mul]
  rw [h_sum_eq]
  have hcard : ((Finset.univ.filter (SharesPlaq4 Ls Lt e)).card : ℝ) ≤ 18 := by
    exact_mod_cast sharesPlaq4_card_le Ls Lt e
  exact mul_le_mul_of_nonneg_right hcard h1c

noncomputable def condGibbsWeight {Ls Lt N : ℕ} [NeZero Ls] [NeZero Lt] (β : ℝ)
    (e : (cubicTorus4 Ls Lt).Link)
    (U : GaugeField (cubicTorus4 Ls Lt) (Matrix.specialUnitaryGroup (Fin N) ℂ))
    (u : Matrix.specialUnitaryGroup (Fin N) ℂ) : ℝ :=
  Real.exp (-(β * ((plaqsTouching Ls Lt e).map
    (fun p => wilsonPlaquetteTerm p (Function.update U e u))).sum))

theorem measurable_condGibbsWeight_pair (Ls Lt N : ℕ) [NeZero Ls] [NeZero Lt] (β : ℝ)
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (e : (cubicTorus4 Ls Lt).Link) :
    Measurable (fun q :
        GaugeField (cubicTorus4 Ls Lt) (Matrix.specialUnitaryGroup (Fin N) ℂ) ×
        Matrix.specialUnitaryGroup (Fin N) ℂ =>
      condGibbsWeight β e q.1 q.2) := by
  have h_upd_m : Measurable (fun q :
      GaugeField (cubicTorus4 Ls Lt) (Matrix.specialUnitaryGroup (Fin N) ℂ) ×
      Matrix.specialUnitaryGroup (Fin N) ℂ => Function.update q.1 e q.2) := by
    change Measurable (fun q : _ × _ =>
      fun e' : (cubicTorus4 Ls Lt).Link => Function.update q.1 e q.2 e')
    refine measurable_pi_iff.mpr fun e' => ?_
    by_cases h : e' = e
    · subst h; simp only [Function.update_self]; exact measurable_snd
    · simp only [Function.update_of_ne h]
      exact (measurable_pi_apply e').comp measurable_fst
  have h_sum_m : Measurable (fun q :
      GaugeField (cubicTorus4 Ls Lt) (Matrix.specialUnitaryGroup (Fin N) ℂ) ×
      Matrix.specialUnitaryGroup (Fin N) ℂ =>
      ((plaqsTouching Ls Lt e).map
        (fun p => wilsonPlaquetteTerm p (Function.update q.1 e q.2))).sum) := by
    induction (plaqsTouching Ls Lt e) with
    | nil => simp [measurable_const]
    | cons p ps ih =>
      simp only [List.map_cons, List.sum_cons]
      exact ((measurable_cubic4_plaquette_term Ls Lt N p).comp h_upd_m).add ih
  exact Real.continuous_exp.measurable.comp (Measurable.neg (measurable_const.mul h_sum_m))

theorem measurable_condGibbsWeight_right (Ls Lt N : ℕ) [NeZero Ls] [NeZero Lt] (β : ℝ)
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (e : (cubicTorus4 Ls Lt).Link)
    (U : GaugeField (cubicTorus4 Ls Lt) (Matrix.specialUnitaryGroup (Fin N) ℂ)) :
    Measurable (condGibbsWeight β e U) := by
  have h_upd_m : Measurable (fun u : Matrix.specialUnitaryGroup (Fin N) ℂ => Function.update U e u) :=
    measurable_pi_iff.mpr fun e' => by
      by_cases h : e' = e
      · subst h; simp only [Function.update_self]; exact measurable_id
      · simp only [Function.update_of_ne h]; exact measurable_const
  have h_sum_m : Measurable (fun u : Matrix.specialUnitaryGroup (Fin N) ℂ =>
      ((plaqsTouching Ls Lt e).map
        (fun p => wilsonPlaquetteTerm p (Function.update U e u))).sum) := by
    induction (plaqsTouching Ls Lt e) with
    | nil => simp [measurable_const]
    | cons p ps ih =>
      simp only [List.map_cons, List.sum_cons]
      exact ((measurable_cubic4_plaquette_term Ls Lt N p).comp h_upd_m).add ih
  exact Real.continuous_exp.measurable.comp (Measurable.neg (measurable_const.mul h_sum_m))

theorem condGibbsWeight_bounds {Ls Lt N : ℕ} [NeZero Ls] [NeZero Lt]
    (β : ℝ) (hβ : 0 ≤ β) (e : (cubicTorus4 Ls Lt).Link)
    (U : GaugeField (cubicTorus4 Ls Lt) (Matrix.specialUnitaryGroup (Fin N) ℂ))
    (u : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    Real.exp (-12 * β) ≤ condGibbsWeight β e U u ∧ condGibbsWeight β e U u ≤ 1 := by
  unfold condGibbsWeight
  have hb := localPlaqSum_bounds Ls Lt N e (Function.update U e u)
  exact ⟨Real.exp_le_exp.mpr (by nlinarith [hβ, hb.2]),
    Real.exp_le_one_iff.mpr (by nlinarith [hβ, hb.1])⟩

theorem condGibbsZ_bounds (Ls Lt N : ℕ) [NeZero Ls] [NeZero Lt]
    (β : ℝ) (hβ : 0 ≤ β)
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (e : (cubicTorus4 Ls Lt).Link)
    (U : GaugeField (cubicTorus4 Ls Lt) (Matrix.specialUnitaryGroup (Fin N) ℂ)) :
    Real.exp (-12 * β) ≤ ∫ u, condGibbsWeight β e U u ∂(suHaar N) ∧
      ∫ u, condGibbsWeight β e U u ∂(suHaar N) ≤ 1 := by
  haveI := suHaar_prob N
  have hm := measurable_condGibbsWeight_right Ls Lt N β e U
  have hwi : MeasureTheory.Integrable (condGibbsWeight β e U) (suHaar N) :=
    (MeasureTheory.integrable_const (1 : ℝ)).mono' hm.stronglyMeasurable.aestronglyMeasurable
      (Filter.Eventually.of_forall fun u => by
        rw [Real.norm_eq_abs, abs_of_nonneg (((Real.exp_pos _).trans_le (condGibbsWeight_bounds β hβ e U u).1).le)]
        exact (condGibbsWeight_bounds β hβ e U u).2)
  refine ⟨?_, ?_⟩
  · calc Real.exp (-12 * β) = ∫ _u, Real.exp (-12 * β) ∂(suHaar N) := by
          simp [Measure.real, MeasureTheory.measure_univ]
      _ ≤ ∫ u, condGibbsWeight β e U u ∂(suHaar N) :=
          MeasureTheory.integral_mono (MeasureTheory.integrable_const _) hwi
            (fun u => (condGibbsWeight_bounds β hβ e U u).1)
  · calc ∫ u, condGibbsWeight β e U u ∂(suHaar N) ≤ ∫ _u, (1 : ℝ) ∂(suHaar N) :=
          MeasureTheory.integral_mono hwi (MeasureTheory.integrable_const _)
            (fun u => (condGibbsWeight_bounds β hβ e U u).2)
      _ = 1 := by simp [Measure.real, MeasureTheory.measure_univ]

theorem measurable_condGibbsExp (Ls Lt N : ℕ) [NeZero Ls] [NeZero Lt] (β : ℝ)
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (e : (cubicTorus4 Ls Lt).Link)
    (f : GaugeField (cubicTorus4 Ls Lt) (Matrix.specialUnitaryGroup (Fin N) ℂ) → ℂ)
    (hf_m : Measurable f) :
    Measurable (condGibbsExp Ls Lt N β e f) := by
  haveI := suHaar_prob N
  have h_upd_m : Measurable (fun q :
      GaugeField (cubicTorus4 Ls Lt) (Matrix.specialUnitaryGroup (Fin N) ℂ) ×
      Matrix.specialUnitaryGroup (Fin N) ℂ => Function.update q.1 e q.2) := by
    change Measurable (fun q : _ × _ =>
      fun e' : (cubicTorus4 Ls Lt).Link => Function.update q.1 e q.2 e')
    refine measurable_pi_iff.mpr fun e' => ?_
    by_cases h : e' = e
    · subst h; simp only [Function.update_self]; exact measurable_snd
    · simp only [Function.update_of_ne h]
      exact (measurable_pi_apply e').comp measurable_fst
  have hm_w := measurable_condGibbsWeight_pair Ls Lt N β e
  have hm_Z : Measurable (fun U => ∫ u, condGibbsWeight β e U u ∂(suHaar N)) :=
    MeasureTheory.StronglyMeasurable.measurable
      (MeasureTheory.StronglyMeasurable.integral_prod_right' hm_w.stronglyMeasurable)
  have hm_num : Measurable (fun U =>
      ∫ u, ((condGibbsWeight β e U u : ℝ) : ℂ) * f (Function.update U e u) ∂(suHaar N)) :=
    MeasureTheory.StronglyMeasurable.measurable
      (MeasureTheory.StronglyMeasurable.integral_prod_right'
        ((Complex.continuous_ofReal.measurable.comp hm_w).mul
          (hf_m.comp h_upd_m)).stronglyMeasurable)
  exact (Complex.continuous_ofReal.measurable.comp hm_Z.inv).mul hm_num

theorem condGibbsExp_bound (Ls Lt N : ℕ) [NeZero Ls] [NeZero Lt]
    (β : ℝ) (hβ : 0 ≤ β)
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (e : (cubicTorus4 Ls Lt).Link)
    (f : GaugeField (cubicTorus4 Ls Lt) (Matrix.specialUnitaryGroup (Fin N) ℂ) → ℂ)
    (hf_m : Measurable f) (M : ℝ) (hM : 0 ≤ M) (hf_bd : ∀ U, ‖f U‖ ≤ M)
    (U : GaugeField (cubicTorus4 Ls Lt) (Matrix.specialUnitaryGroup (Fin N) ℂ)) :
    ‖condGibbsExp Ls Lt N β e f U‖ ≤ M := by
  haveI := suHaar_prob N
  have hw_m := measurable_condGibbsWeight_right Ls Lt N β e U
  have hZ_bds := condGibbsZ_bounds Ls Lt N β hβ e U
  have hZ_pos : 0 < ∫ u, condGibbsWeight β e U u ∂(suHaar N) := (Real.exp_pos _).trans_le hZ_bds.1
  have hwi : MeasureTheory.Integrable (condGibbsWeight β e U) (suHaar N) :=
    (MeasureTheory.integrable_const (1 : ℝ)).mono' hw_m.stronglyMeasurable.aestronglyMeasurable
      (Filter.Eventually.of_forall fun u => by
        rw [Real.norm_eq_abs, abs_of_nonneg (((Real.exp_pos _).trans_le (condGibbsWeight_bounds β hβ e U u).1).le)]
        exact (condGibbsWeight_bounds β hβ e U u).2)
  have hfU_m : Measurable (fun u => f (Function.update U e u)) :=
    hf_m.comp (measurable_pi_iff.mpr fun e' => by
      by_cases h : e' = e
      · subst h; simp only [Function.update_self]; exact measurable_id
      · simp only [Function.update_of_ne h]; exact measurable_const)
  have h_num_int : MeasureTheory.Integrable
      (fun u => ‖((condGibbsWeight β e U u : ℝ) : ℂ) * f (Function.update U e u)‖) (suHaar N) :=
    (hwi.mul_const M).mono'
      ((Complex.continuous_ofReal.measurable.comp hw_m).mul hfU_m).stronglyMeasurable.aestronglyMeasurable.norm
      (Filter.Eventually.of_forall fun u => by
        rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _), norm_mul, Complex.norm_real,
          Real.norm_eq_abs, abs_of_nonneg (((Real.exp_pos _).trans_le (condGibbsWeight_bounds β hβ e U u).1).le)]
        exact mul_le_mul_of_nonneg_left (hf_bd _) (Real.exp_pos _).le)
  have h_ce_eq : condGibbsExp Ls Lt N β e f U =
      (((∫ u, condGibbsWeight β e U u ∂(suHaar N))⁻¹ : ℝ) : ℂ) *
        ∫ u, ((condGibbsWeight β e U u : ℝ) : ℂ) * f (Function.update U e u) ∂(suHaar N) := rfl
  rw [h_ce_eq]
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr hZ_pos.le)]
  calc (∫ u, condGibbsWeight β e U u ∂(suHaar N))⁻¹ *
        ‖∫ u, ((condGibbsWeight β e U u : ℝ) : ℂ) * f (Function.update U e u) ∂(suHaar N)‖
      ≤ (∫ u, condGibbsWeight β e U u ∂(suHaar N))⁻¹ *
          ∫ u, ‖((condGibbsWeight β e U u : ℝ) : ℂ) * f (Function.update U e u)‖ ∂(suHaar N) :=
          mul_le_mul_of_nonneg_left (MeasureTheory.norm_integral_le_integral_norm _)
            (inv_nonneg.mpr hZ_pos.le)
    _ ≤ (∫ u, condGibbsWeight β e U u ∂(suHaar N))⁻¹ *
          ∫ u, condGibbsWeight β e U u * M ∂(suHaar N) :=
          mul_le_mul_of_nonneg_left (MeasureTheory.integral_mono h_num_int (hwi.mul_const M)
            fun u => by
              rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (((Real.exp_pos _).trans_le (condGibbsWeight_bounds β hβ e U u).1).le)]
              exact mul_le_mul_of_nonneg_left (hf_bd _) (Real.exp_pos _).le)
            (inv_nonneg.mpr hZ_pos.le)
    _ = M := by
          rw [MeasureTheory.integral_mul_const, ← mul_assoc, inv_mul_cancel₀ hZ_pos.ne', one_mul]

theorem condGibbsExp_osc_bound (Ls Lt N : ℕ) [NeZero Ls] [NeZero Lt]
    (β : ℝ) (hβ : 0 ≤ β)
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (e e' : (cubicTorus4 Ls Lt).Link)
    (f : GaugeField (cubicTorus4 Ls Lt) (Matrix.specialUnitaryGroup (Fin N) ℂ) → ℂ)
    (hf_m : Measurable f) (M : ℝ) (hM : 0 ≤ M) (hf_bd : ∀ U, ‖f U‖ ≤ M) :
    (e' = e → linkOsc (condGibbsExp Ls Lt N β e f) e' = 0) ∧
    (e' ≠ e → linkOsc (condGibbsExp Ls Lt N β e f) e' ≤
      linkOsc f e' + dobrushinCoeff Ls Lt β e e' * linkOsc f e) := by
  haveI := suHaar_prob N
  have h_ce_bd := condGibbsExp_bound Ls Lt N β hβ e f hf_m M hM hf_bd
  constructor
  · intro he_eq; rw [he_eq]
    refine le_antisymm ?_ (linkOsc_nonneg _ M h_ce_bd e)
    have hne : { r : ℝ | ∃ U V, (∀ e'', e'' ≠ e → U e'' = V e'') ∧ r =
      ‖condGibbsExp Ls Lt N β e f U - condGibbsExp Ls Lt N β e f V‖ }.Nonempty :=
      ⟨0, fun _ => 1, fun _ => 1, fun _ _ => rfl, by simp⟩
    refine csSup_le hne fun r ⟨U, V, hUV, hr⟩ => ?_
    rw [hr]
    have h_upd_eq : ∀ u, Function.update U e u = Function.update V e u := fun u => by
      funext e''; by_cases h : e'' = e
      · rw [h, Function.update_self, Function.update_self]
      · rw [Function.update_of_ne h, Function.update_of_ne h, hUV e'' h]
    dsimp [condGibbsExp]
    simp_rw [h_upd_eq]
    rw [sub_self, norm_zero]
  · intro hne
    have h_set_ne : { r : ℝ | ∃ U V, (∀ e'', e'' ≠ e' → U e'' = V e'') ∧ r =
      ‖condGibbsExp Ls Lt N β e f U - condGibbsExp Ls Lt N β e f V‖ }.Nonempty :=
      ⟨0, fun _ => 1, fun _ => 1, fun _ _ => rfl, by simp⟩
    refine csSup_le h_set_ne fun r ⟨U, V, hUV, hr⟩ => ?_
    rw [hr]
    let Z1 := ∫ u, condGibbsWeight β e U u ∂(suHaar N)
    let Z2 := ∫ u, condGibbsWeight β e V u ∂(suHaar N)
    let ρ1 : Matrix.specialUnitaryGroup (Fin N) ℂ → ℝ := fun u => Z1⁻¹ * condGibbsWeight β e U u
    let ρ2 : Matrix.specialUnitaryGroup (Fin N) ℂ → ℝ := fun u => Z2⁻¹ * condGibbsWeight β e V u
    have hZ1_bds := condGibbsZ_bounds Ls Lt N β hβ e U
    have hZ2_bds := condGibbsZ_bounds Ls Lt N β hβ e V
    have hZ1_pos : 0 < Z1 := (Real.exp_pos _).trans_le hZ1_bds.1
    have hZ2_pos : 0 < Z2 := (Real.exp_pos _).trans_le hZ2_bds.1
    have hwU_m := measurable_condGibbsWeight_right Ls Lt N β e U
    have hwV_m := measurable_condGibbsWeight_right Ls Lt N β e V
    have hfU_m : Measurable (fun u => f (Function.update U e u)) :=
      hf_m.comp (measurable_pi_iff.mpr fun e'' => by
        by_cases h_eq : e'' = e
        · subst h_eq; simp only [Function.update_self]; exact measurable_id
        · simp only [Function.update_of_ne h_eq]; exact measurable_const)
    have hfV_m : Measurable (fun u => f (Function.update V e u)) :=
      hf_m.comp (measurable_pi_iff.mpr fun e'' => by
        by_cases h_eq : e'' = e
        · subst h_eq; simp only [Function.update_self]; exact measurable_id
        · simp only [Function.update_of_ne h_eq]; exact measurable_const)
    have hρ1_bd : ∀ u, ρ1 u ≤ Z1⁻¹ := fun u =>
      mul_le_of_le_one_right (inv_nonneg.mpr hZ1_pos.le) (condGibbsWeight_bounds β hβ e U u).2
    have hρ2_bd : ∀ u, ρ2 u ≤ Z2⁻¹ := fun u =>
      mul_le_of_le_one_right (inv_nonneg.mpr hZ2_pos.le) (condGibbsWeight_bounds β hβ e V u).2
    have hρ1_nn : ∀ u, 0 ≤ ρ1 u := fun u =>
      mul_nonneg (inv_nonneg.mpr hZ1_pos.le) (Real.exp_pos _).le
    have hρ2_nn : ∀ u, 0 ≤ ρ2 u := fun u =>
      mul_nonneg (inv_nonneg.mpr hZ2_pos.le) (Real.exp_pos _).le
    have h_ce_split : condGibbsExp Ls Lt N β e f U - condGibbsExp Ls Lt N β e f V =
        (∫ u, ((ρ1 u : ℝ) : ℂ) * (f (Function.update U e u) - f (Function.update V e u)) ∂(suHaar N)) +
        (∫ u, ((ρ1 u - ρ2 u : ℝ) : ℂ) * f (Function.update V e u) ∂(suHaar N)) := by
      have hi_A := integrable_of_measurable_bound (suHaar N)
        (fun u => ((ρ1 u : ℝ) : ℂ) * f (Function.update U e u))
        ((Complex.continuous_ofReal.measurable.comp (hwU_m.const_mul _)).mul hfU_m) (Z1⁻¹ * M) fun u => by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hρ1_nn u)]
        exact mul_le_mul (hρ1_bd u) (hf_bd _) (norm_nonneg _) (inv_nonneg.mpr hZ1_pos.le)
      have hi_B := integrable_of_measurable_bound (suHaar N)
        (fun u => ((ρ2 u : ℝ) : ℂ) * f (Function.update V e u))
        ((Complex.continuous_ofReal.measurable.comp (hwV_m.const_mul _)).mul hfV_m) (Z2⁻¹ * M) fun u => by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hρ2_nn u)]
        exact mul_le_mul (hρ2_bd u) (hf_bd _) (norm_nonneg _) (inv_nonneg.mpr hZ2_pos.le)
      have hi_C := integrable_of_measurable_bound (suHaar N)
        (fun u => ((ρ1 u : ℝ) : ℂ) * (f (Function.update U e u) - f (Function.update V e u)))
        ((Complex.continuous_ofReal.measurable.comp (hwU_m.const_mul _)).mul (hfU_m.sub hfV_m)) (Z1⁻¹ * (2 * M)) fun u => by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hρ1_nn u)]
        have h_diff_bd : ‖f (Function.update U e u) - f (Function.update V e u)‖ ≤ 2 * M := by
          calc ‖f (Function.update U e u) - f (Function.update V e u)‖
              ≤ ‖f (Function.update U e u)‖ + ‖f (Function.update V e u)‖ := norm_sub_le _ _
            _ ≤ M + M := add_le_add (hf_bd _) (hf_bd _)
            _ = 2 * M := by ring
        exact mul_le_mul (hρ1_bd u) h_diff_bd (norm_nonneg _) (inv_nonneg.mpr hZ1_pos.le)
      have hi_D := integrable_of_measurable_bound (suHaar N)
        (fun u => ((ρ1 u - ρ2 u : ℝ) : ℂ) * f (Function.update V e u))
        ((Complex.continuous_ofReal.measurable.comp ((hwU_m.const_mul _).sub (hwV_m.const_mul _))).mul hfV_m) ((Z1⁻¹ + Z2⁻¹) * M) fun u => by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
        have h_rho_bd : |ρ1 u - ρ2 u| ≤ Z1⁻¹ + Z2⁻¹ := by
          calc |ρ1 u - ρ2 u| ≤ |ρ1 u| + |ρ2 u| := abs_sub _ _
            _ = ρ1 u + ρ2 u := by rw [abs_of_nonneg (hρ1_nn u), abs_of_nonneg (hρ2_nn u)]
            _ ≤ Z1⁻¹ + Z2⁻¹ := add_le_add (hρ1_bd u) (hρ2_bd u)
        exact mul_le_mul h_rho_bd (hf_bd _) (norm_nonneg _) (add_nonneg (inv_nonneg.mpr hZ1_pos.le) (inv_nonneg.mpr hZ2_pos.le))
      dsimp [condGibbsExp]
      change ((Z1⁻¹ : ℝ) : ℂ) * ∫ u, ((condGibbsWeight β e U u : ℝ) : ℂ) *
          f (Function.update U e u) ∂(suHaar N) -
        ((Z2⁻¹ : ℝ) : ℂ) * ∫ u, ((condGibbsWeight β e V u : ℝ) : ℂ) *
          f (Function.update V e u) ∂(suHaar N) = _
      rw [← MeasureTheory.integral_const_mul, ← MeasureTheory.integral_const_mul]
      have h_eq1 : (fun a => ((Z1⁻¹ : ℝ) : ℂ) * (((condGibbsWeight β e U a : ℝ) : ℂ) *
            f (Function.update U e a))) =
          fun u => ((ρ1 u : ℝ) : ℂ) * f (Function.update U e u) := by
        funext u; dsimp [ρ1]; push_cast; ring
      have h_eq2 : (fun a => ((Z2⁻¹ : ℝ) : ℂ) * (((condGibbsWeight β e V a : ℝ) : ℂ) *
            f (Function.update V e a))) =
          fun u => ((ρ2 u : ℝ) : ℂ) * f (Function.update V e u) := by
        funext u; dsimp [ρ2]; push_cast; ring
      rw [h_eq1, h_eq2]
      rw [← MeasureTheory.integral_sub hi_A hi_B, ← MeasureTheory.integral_add hi_C hi_D]
      refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
      push_cast; ring
    have h_term1_bd :
        ‖∫ u, ((ρ1 u : ℝ) : ℂ) * (f (Function.update U e u) - f (Function.update V e u)) ∂(suHaar N)‖ ≤
          linkOsc f e' := by
      have hi_diff : MeasureTheory.Integrable
          (fun u => ‖((ρ1 u : ℝ) : ℂ) * (f (Function.update U e u) - f (Function.update V e u))‖)
          (suHaar N) :=
        (MeasureTheory.integrable_const (Z1⁻¹ * (2 * M))).mono'
          ((Complex.continuous_ofReal.measurable.comp (hwU_m.const_mul _)).mul
            (hfU_m.sub hfV_m)).stronglyMeasurable.aestronglyMeasurable.norm
          (Filter.Eventually.of_forall fun u => by
            rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _), norm_mul, Complex.norm_real,
              Real.norm_eq_abs, abs_of_nonneg (hρ1_nn u)]
            exact mul_le_mul (hρ1_bd u)
              ((norm_sub_le _ _).trans (by linarith [hf_bd (Function.update U e u), hf_bd (Function.update V e u)]))
              (norm_nonneg _) (inv_nonneg.mpr hZ1_pos.le))
      have h_pt_osc : ∀ u, ‖f (Function.update U e u) - f (Function.update V e u)‖ ≤ linkOsc f e' :=
        fun u => norm_sub_le_linkOsc f M hf_bd e' fun e'' he'' => by
          by_cases h_e : e'' = e
          · subst h_e; simp
          · simp [Function.update_of_ne h_e, hUV e'' he'']
      have h_int_r1 : MeasureTheory.Integrable (fun u => ρ1 u * linkOsc f e') (suHaar N) :=
        (MeasureTheory.integrable_const (Z1⁻¹ * (2 * M))).mono'
          ((hwU_m.const_mul _).mul_const _).stronglyMeasurable.aestronglyMeasurable
          (Filter.Eventually.of_forall fun u => by
            rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg
              (hρ1_nn u) (linkOsc_nonneg f M hf_bd e'))]
            exact mul_le_mul (hρ1_bd u) (linkOsc_le_two_mul f M hM hf_bd e')
              (linkOsc_nonneg f M hf_bd e') (inv_nonneg.mpr hZ1_pos.le))
      calc ‖∫ u, ((ρ1 u : ℝ) : ℂ) * (f (Function.update U e u) - f (Function.update V e u)) ∂(suHaar N)‖
          ≤ ∫ u, ‖((ρ1 u : ℝ) : ℂ) * (f (Function.update U e u) - f (Function.update V e u))‖ ∂(suHaar N) :=
              MeasureTheory.norm_integral_le_integral_norm _
        _ ≤ ∫ u, ρ1 u * linkOsc f e' ∂(suHaar N) :=
              MeasureTheory.integral_mono hi_diff h_int_r1 fun u => by
                rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
                  abs_of_nonneg (hρ1_nn u)]
                exact mul_le_mul_of_nonneg_left (h_pt_osc u) (hρ1_nn u)
        _ = (∫ u, ρ1 u ∂(suHaar N)) * linkOsc f e' := MeasureTheory.integral_mul_const _ _
        _ = linkOsc f e' := by
              have hρ1_i : ∫ u, ρ1 u ∂(suHaar N) = 1 := by
                dsimp [ρ1]; rw [MeasureTheory.integral_const_mul, inv_mul_cancel₀ hZ1_pos.ne']
              rw [hρ1_i, one_mul]
    have h_term2_bd :
        ‖∫ u, ((ρ1 u - ρ2 u : ℝ) : ℂ) * f (Function.update V e u) ∂(suHaar N)‖ ≤
          dobrushinCoeff Ls Lt β e e' * linkOsc f e := by
      by_cases hadj : SharesPlaq4 Ls Lt e e'
      · dsimp [dobrushinCoeff]; rw [if_pos hadj]
        refine condDensity_tv_bound (fun u => f (Function.update V e u)) hfV_m
          (linkOsc f e) (linkOsc_nonneg f M hf_bd e)
          (fun u v => norm_sub_le_linkOsc f M hf_bd e fun e'' he'' => by
            simp [Function.update_of_ne he''])
          M (fun u => hf_bd _) ρ1 ρ2 (hwU_m.const_mul _) (hwV_m.const_mul _)
          (Real.exp (-12 * β)) (Real.exp_pos _).le (Real.exp_le_one_iff.mpr (by linarith))
          (fun u => by
            dsimp [ρ1]
            calc Real.exp (-12 * β) = 1 * Real.exp (-12 * β) := (one_mul _).symm
              _ ≤ Z1⁻¹ * condGibbsWeight β e U u := mul_le_mul ((one_le_inv₀ hZ1_pos).mpr hZ1_bds.2)
                  (condGibbsWeight_bounds β hβ e U u).1 (Real.exp_pos _).le (inv_nonneg.mpr hZ1_pos.le))
          (fun u => by
            dsimp [ρ2]
            calc Real.exp (-12 * β) = 1 * Real.exp (-12 * β) := (one_mul _).symm
              _ ≤ Z2⁻¹ * condGibbsWeight β e V u := mul_le_mul ((one_le_inv₀ hZ2_pos).mpr hZ2_bds.2)
                  (condGibbsWeight_bounds β hβ e V u).1 (Real.exp_pos _).le (inv_nonneg.mpr hZ2_pos.le))
          (fun u => (hρ1_bd u).trans (inv_anti₀ (Real.exp_pos _) hZ1_bds.1))
          (fun u => (hρ2_bd u).trans (inv_anti₀ (Real.exp_pos _) hZ2_bds.1))
          (by dsimp [ρ1]; rw [MeasureTheory.integral_const_mul, inv_mul_cancel₀ hZ1_pos.ne'])
          (by dsimp [ρ2]; rw [MeasureTheory.integral_const_mul, inv_mul_cancel₀ hZ2_pos.ne'])
      · have hw_eq : ∀ u, condGibbsWeight β e U u = condGibbsWeight β e V u := fun u => by
          dsimp [condGibbsWeight]
          rw [show (plaqsTouching Ls Lt e).map (fun p => wilsonPlaquetteTerm p (Function.update U e u)) =
              (plaqsTouching Ls Lt e).map (fun p => wilsonPlaquetteTerm p (Function.update V e u)) from
            List.map_congr_left fun p hp => by
              rw [plaqsTouching, List.mem_filter] at hp
              have he_p : e ∈ p.loop.map Prod.fst := of_decide_eq_true hp.2
              have hne_p : e' ∉ p.loop.map Prod.fst := fun hmem => hadj ⟨hne.symm, p, hp.1, he_p, hmem⟩
              refine wilsonPlaquetteTerm_depends_on_links p _ _ fun e'' b hm => ?_
              by_cases h_e : e'' = e
              · rw [h_e, Function.update_self, Function.update_self]
              · have h_e' : e'' ≠ e' := fun heq => hne_p (heq ▸ List.mem_map.mpr ⟨(e'', b), hm, rfl⟩)
                rw [Function.update_of_ne h_e, Function.update_of_ne h_e, hUV e'' h_e']]
        have hρ_eq : ∀ u, ρ1 u - ρ2 u = 0 := fun u => by
          have hZ_eq : Z1 = Z2 := by dsimp [Z1, Z2]; simp_rw [hw_eq]
          dsimp [ρ1, ρ2]; rw [hZ_eq, hw_eq u, sub_self]
        simp_rw [hρ_eq, Complex.ofReal_zero, zero_mul, MeasureTheory.integral_zero, norm_zero]
        dsimp [dobrushinCoeff]; rw [if_neg hadj, zero_mul]
    rw [h_ce_split]
    exact (norm_add_le _ _).trans (add_le_add h_term1_bd h_term2_bd)

theorem norm_sub_le_sum_linkOsc {Ls Lt N : ℕ} [NeZero Ls] [NeZero Lt]
    (h : GaugeField (cubicTorus4 Ls Lt) (Matrix.specialUnitaryGroup (Fin N) ℂ) → ℂ)
    (M : ℝ) (hbd : ∀ U, ‖h U‖ ≤ M) (s : Finset (cubicTorus4 Ls Lt).Link) :
    ∀ U V, (∀ e ∉ s, U e = V e) → ‖h U - h V‖ ≤ ∑ e ∈ s, linkOsc h e := by
  induction s using Finset.induction_on with
  | empty =>
    intro U V hUV
    have heq : U = V := funext fun e => hUV e (Finset.notMem_empty e)
    subst heq; simp
  | @insert a s ha ih =>
    intro U V hUV
    let W := Function.update V a (U a)
    have hUW : ∀ e ∉ s, U e = W e := by
      intro e he
      by_cases hea : e = a
      · subst hea; simp [W]
      · simp [W, Function.update_of_ne hea, hUV e (by simp [hea, he])]
    have hWV : ∀ e, e ≠ a → W e = V e := fun e hea => Function.update_of_ne hea (U a) V
    rw [Finset.sum_insert ha]
    calc ‖h U - h V‖ = ‖(h U - h W) + (h W - h V)‖ := by rw [sub_add_sub_cancel]
      _ ≤ ‖h U - h W‖ + ‖h W - h V‖ := norm_add_le _ _
      _ ≤ ∑ e ∈ s, linkOsc h e + linkOsc h a :=
          add_le_add (ih U W hUW) (norm_sub_le_linkOsc h M hbd a hWV)
      _ = linkOsc h a + ∑ e ∈ s, linkOsc h e := add_comm _ _

theorem condGibbsExp_mul_left_of_osc_zero (Ls Lt N : ℕ) [NeZero Ls] [NeZero Lt]
    (β : ℝ)
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (e : (cubicTorus4 Ls Lt).Link)
    (f h : GaugeField (cubicTorus4 Ls Lt) (Matrix.specialUnitaryGroup (Fin N) ℂ) → ℂ)
    (M_f : ℝ) (hf_bd : ∀ U, ‖f U‖ ≤ M_f) (hf_e : linkOsc f e = 0)
    (U : GaugeField (cubicTorus4 Ls Lt) (Matrix.specialUnitaryGroup (Fin N) ℂ)) :
    condGibbsExp Ls Lt N β e (fun V => f V * h V) U =
      f U * condGibbsExp Ls Lt N β e h U := by
  have hf_const : ∀ u : Matrix.specialUnitaryGroup (Fin N) ℂ,
      f (Function.update U e u) = f U := fun u => by
    have hle := norm_sub_le_linkOsc f M_f hf_bd e (U := Function.update U e u) (V := U)
      (fun e' he' => Function.update_of_ne he' u U)
    rw [hf_e] at hle
    exact sub_eq_zero.mp (norm_le_zero_iff.mp hle)
  dsimp [condGibbsExp]
  have h_fn : (fun u => ((condGibbsWeight β e U u : ℝ) : ℂ) *
        (f (Function.update U e u) * h (Function.update U e u))) =
      fun u => f U * (((condGibbsWeight β e U u : ℝ) : ℂ) * h (Function.update U e u)) := by
    funext u; rw [hf_const u]; ring
  change _ * ∫ u, ((condGibbsWeight β e U u : ℝ) : ℂ) *
      (f (Function.update U e u) * h (Function.update U e u)) ∂(suHaar N) =
    f U * (_ * ∫ u, ((condGibbsWeight β e U u : ℝ) : ℂ) * h (Function.update U e u) ∂(suHaar N))
  rw [h_fn, MeasureTheory.integral_const_mul]
  ring

theorem cubic4Schwinger_two_eq_one_mul (Ls Lt N : ℕ) [NeZero Ls] [NeZero Lt] (β : ℝ)
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (f h : GaugeField (cubicTorus4 Ls Lt) (Matrix.specialUnitaryGroup (Fin N) ℂ) → ℂ) :
    cubic4Schwinger Ls Lt N β 2 ![f, h] =
      cubic4Schwinger Ls Lt N β 1 ![fun U => f U * h U] := by
  unfold cubic4Schwinger
  congr 1
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun U => ?_)
  simp [Fin.prod_univ_two]

theorem condGibbsExp_cov_invariant (Ls Lt N : ℕ) [NeZero Ls] [NeZero Lt]
    (β : ℝ) (hβ : 0 ≤ β)
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (e : (cubicTorus4 Ls Lt).Link)
    (f h : GaugeField (cubicTorus4 Ls Lt) (Matrix.specialUnitaryGroup (Fin N) ℂ) → ℂ)
    (hf_m : Measurable f) (hh_m : Measurable h)
    (M_f M_h : ℝ) (hMf : 0 ≤ M_f) (hMh : 0 ≤ M_h)
    (hf_bd : ∀ U, ‖f U‖ ≤ M_f) (hh_bd : ∀ U, ‖h U‖ ≤ M_h)
    (hf_e : linkOsc f e = 0) :
    cubic4Schwinger Ls Lt N β 2 ![f, condGibbsExp Ls Lt N β e h] -
      cubic4Schwinger Ls Lt N β 1 ![f] *
        cubic4Schwinger Ls Lt N β 1 ![condGibbsExp Ls Lt N β e h] =
    cubic4Schwinger Ls Lt N β 2 ![f, h] -
      cubic4Schwinger Ls Lt N β 1 ![f] * cubic4Schwinger Ls Lt N β 1 ![h] := by
  have h1 := condGibbsExp_tower Ls Lt N β hβ e h hh_m M_h hMh hh_bd
  have h2 : cubic4Schwinger Ls Lt N β 2 ![f, condGibbsExp Ls Lt N β e h] =
      cubic4Schwinger Ls Lt N β 2 ![f, h] := by
    rw [cubic4Schwinger_two_eq_one_mul, cubic4Schwinger_two_eq_one_mul]
    have h_eq : (fun U => f U * condGibbsExp Ls Lt N β e h U) =
        condGibbsExp Ls Lt N β e (fun U => f U * h U) := by
      funext U
      exact (condGibbsExp_mul_left_of_osc_zero Ls Lt N β e f h M_f hf_bd hf_e U).symm
    rw [h_eq]
    exact condGibbsExp_tower Ls Lt N β hβ e (fun U => f U * h U) (hf_m.mul hh_m)
      (M_f * M_h) (mul_nonneg hMf hMh) (fun U => by
        rw [norm_mul]; exact mul_le_mul (hf_bd U) (hh_bd U) (norm_nonneg _) hMf)
  rw [h1, h2]

noncomputable def setOsc {Ls Lt N : ℕ} [NeZero Ls] [NeZero Lt]
    (S : Finset (cubicTorus4 Ls Lt).Link)
    (h : GaugeField (cubicTorus4 Ls Lt) (Matrix.specialUnitaryGroup (Fin N) ℂ) → ℂ) : ℝ :=
  sSup { r : ℝ | ∃ U V, (∀ e ∉ S, U e = V e) ∧ r = ‖h U - h V‖ }

theorem setOsc_nonneg {Ls Lt N : ℕ} [NeZero Ls] [NeZero Lt]
    (S : Finset (cubicTorus4 Ls Lt).Link)
    (h : GaugeField (cubicTorus4 Ls Lt) (Matrix.specialUnitaryGroup (Fin N) ℂ) → ℂ)
    (M : ℝ) (hbd : ∀ U, ‖h U‖ ≤ M) :
    0 ≤ setOsc S h := by
  have h0 : (0 : ℝ) ∈ { r : ℝ | ∃ U V, (∀ e ∉ S, U e = V e) ∧ r = ‖h U - h V‖ } :=
    ⟨fun _ => 1, fun _ => 1, fun _ _ => rfl, by simp⟩
  have hbdd : BddAbove { r : ℝ | ∃ U V, (∀ e ∉ S, U e = V e) ∧ r = ‖h U - h V‖ } :=
    ⟨2 * M, fun r ⟨U, V, _, hr⟩ => hr ▸ (norm_sub_le _ _).trans (by linarith [hbd U, hbd V])⟩
  exact le_csSup hbdd h0

theorem setOsc_le_two_mul {Ls Lt N : ℕ} [NeZero Ls] [NeZero Lt]
    (S : Finset (cubicTorus4 Ls Lt).Link)
    (h : GaugeField (cubicTorus4 Ls Lt) (Matrix.specialUnitaryGroup (Fin N) ℂ) → ℂ)
    (M : ℝ) (hbd : ∀ U, ‖h U‖ ≤ M) :
    setOsc S h ≤ 2 * M := by
  have hne : { r : ℝ | ∃ U V, (∀ e ∉ S, U e = V e) ∧ r = ‖h U - h V‖ }.Nonempty :=
    ⟨0, fun _ => 1, fun _ => 1, fun _ _ => rfl, by simp⟩
  refine csSup_le hne fun r ⟨U, V, _, hr⟩ => ?_
  exact hr ▸ (norm_sub_le _ _).trans (by linarith [hbd U, hbd V])

theorem norm_sub_le_setOsc {Ls Lt N : ℕ} [NeZero Ls] [NeZero Lt]
    (S : Finset (cubicTorus4 Ls Lt).Link)
    (h : GaugeField (cubicTorus4 Ls Lt) (Matrix.specialUnitaryGroup (Fin N) ℂ) → ℂ)
    (M : ℝ) (hbd : ∀ U, ‖h U‖ ≤ M)
    {U V : GaugeField (cubicTorus4 Ls Lt) (Matrix.specialUnitaryGroup (Fin N) ℂ)}
    (hUV : ∀ e ∉ S, U e = V e) :
    ‖h U - h V‖ ≤ setOsc S h := by
  have hbdd : BddAbove { r : ℝ | ∃ U V, (∀ e ∉ S, U e = V e) ∧ r = ‖h U - h V‖ } :=
    ⟨2 * M, fun r ⟨U', V', _, hr⟩ => hr ▸ (norm_sub_le _ _).trans (by linarith [hbd U', hbd V'])⟩
  exact le_csSup hbdd ⟨U, V, hUV, rfl⟩

theorem setOsc_zero_of_disjoint {Ls Lt N : ℕ} [NeZero Ls] [NeZero Lt]
    (S : Finset (cubicTorus4 Ls Lt).Link)
    (h : GaugeField (cubicTorus4 Ls Lt) (Matrix.specialUnitaryGroup (Fin N) ℂ) → ℂ)
    (M : ℝ) (hbd : ∀ U, ‖h U‖ ≤ M)
    (h_disj : ∀ e ∈ S, linkOsc h e = 0) :
    setOsc S h = 0 := by
  refine le_antisymm ?_ (setOsc_nonneg S h M hbd)
  have hne : { r : ℝ | ∃ U V, (∀ e ∉ S, U e = V e) ∧ r = ‖h U - h V‖ }.Nonempty :=
    ⟨0, fun _ => 1, fun _ => 1, fun _ _ => rfl, by simp⟩
  refine csSup_le hne fun r ⟨U, V, hUV, hr⟩ => ?_
  rw [hr]
  calc ‖h U - h V‖ ≤ ∑ e ∈ S, linkOsc h e := norm_sub_le_sum_linkOsc h M hbd S U V hUV
    _ = 0 := Finset.sum_eq_zero h_disj

theorem condGibbsExp_setOsc_bound (Ls Lt N : ℕ) [NeZero Ls] [NeZero Lt]
    (β : ℝ) (hβ : 0 ≤ β)
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (S_f : Finset (cubicTorus4 Ls Lt).Link)
    (e : (cubicTorus4 Ls Lt).Link)
    (h : GaugeField (cubicTorus4 Ls Lt) (Matrix.specialUnitaryGroup (Fin N) ℂ) → ℂ)
    (hh_m : Measurable h) (M : ℝ) (hM : 0 ≤ M) (hh_bd : ∀ U, ‖h U‖ ≤ M) :
    setOsc S_f (condGibbsExp Ls Lt N β e h) ≤
      setOsc S_f h +
        (if ∃ e' ∈ S_f, SharesPlaq4 Ls Lt e e' then 1 - Real.exp (-12 * β) else 0) *
          linkOsc h e := by
  haveI := suHaar_prob N
  have hne : { r : ℝ | ∃ U V, (∀ e' ∉ S_f, U e' = V e') ∧
      r = ‖condGibbsExp Ls Lt N β e h U - condGibbsExp Ls Lt N β e h V‖ }.Nonempty :=
    ⟨0, fun _ => 1, fun _ => 1, fun _ _ => rfl, by simp⟩
  refine csSup_le hne fun r ⟨U, V, hUV, hr⟩ => ?_
  rw [hr]
  let Z1 := ∫ u, condGibbsWeight β e U u ∂(suHaar N)
  let Z2 := ∫ u, condGibbsWeight β e V u ∂(suHaar N)
  let ρ1 : Matrix.specialUnitaryGroup (Fin N) ℂ → ℝ := fun u => Z1⁻¹ * condGibbsWeight β e U u
  let ρ2 : Matrix.specialUnitaryGroup (Fin N) ℂ → ℝ := fun u => Z2⁻¹ * condGibbsWeight β e V u
  have hZ1_bds := condGibbsZ_bounds Ls Lt N β hβ e U
  have hZ2_bds := condGibbsZ_bounds Ls Lt N β hβ e V
  have hZ1_pos : 0 < Z1 := (Real.exp_pos _).trans_le hZ1_bds.1
  have hZ2_pos : 0 < Z2 := (Real.exp_pos _).trans_le hZ2_bds.1
  have hwU_m := measurable_condGibbsWeight_right Ls Lt N β e U
  have hwV_m := measurable_condGibbsWeight_right Ls Lt N β e V
  have hhU_m : Measurable (fun u => h (Function.update U e u)) :=
    hh_m.comp (measurable_pi_iff.mpr fun e'' => by
      by_cases h_eq : e'' = e
      · subst h_eq; simp only [Function.update_self]; exact measurable_id
      · simp only [Function.update_of_ne h_eq]; exact measurable_const)
  have hhV_m : Measurable (fun u => h (Function.update V e u)) :=
    hh_m.comp (measurable_pi_iff.mpr fun e'' => by
      by_cases h_eq : e'' = e
      · subst h_eq; simp only [Function.update_self]; exact measurable_id
      · simp only [Function.update_of_ne h_eq]; exact measurable_const)
  have hρ1_bd : ∀ u, ρ1 u ≤ Z1⁻¹ := fun u =>
    mul_le_of_le_one_right (inv_nonneg.mpr hZ1_pos.le) (condGibbsWeight_bounds β hβ e U u).2
  have hρ2_bd : ∀ u, ρ2 u ≤ Z2⁻¹ := fun u =>
    mul_le_of_le_one_right (inv_nonneg.mpr hZ2_pos.le) (condGibbsWeight_bounds β hβ e V u).2
  have hρ1_nn : ∀ u, 0 ≤ ρ1 u := fun u =>
    mul_nonneg (inv_nonneg.mpr hZ1_pos.le) (Real.exp_pos _).le
  have hρ2_nn : ∀ u, 0 ≤ ρ2 u := fun u =>
    mul_nonneg (inv_nonneg.mpr hZ2_pos.le) (Real.exp_pos _).le
  have h_ce_split : condGibbsExp Ls Lt N β e h U - condGibbsExp Ls Lt N β e h V =
      (∫ u, ((ρ1 u : ℝ) : ℂ) * (h (Function.update U e u) - h (Function.update V e u)) ∂(suHaar N)) +
      (∫ u, ((ρ1 u - ρ2 u : ℝ) : ℂ) * h (Function.update V e u) ∂(suHaar N)) := by
    have hi_A := integrable_of_measurable_bound (suHaar N)
      (fun u => ((ρ1 u : ℝ) : ℂ) * h (Function.update U e u))
      ((Complex.continuous_ofReal.measurable.comp (hwU_m.const_mul _)).mul hhU_m) (Z1⁻¹ * M) fun u => by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hρ1_nn u)]
      exact mul_le_mul (hρ1_bd u) (hh_bd _) (norm_nonneg _) (inv_nonneg.mpr hZ1_pos.le)
    have hi_B := integrable_of_measurable_bound (suHaar N)
      (fun u => ((ρ2 u : ℝ) : ℂ) * h (Function.update V e u))
      ((Complex.continuous_ofReal.measurable.comp (hwV_m.const_mul _)).mul hhV_m) (Z2⁻¹ * M) fun u => by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hρ2_nn u)]
      exact mul_le_mul (hρ2_bd u) (hh_bd _) (norm_nonneg _) (inv_nonneg.mpr hZ2_pos.le)
    have hi_C := integrable_of_measurable_bound (suHaar N)
      (fun u => ((ρ1 u : ℝ) : ℂ) * (h (Function.update U e u) - h (Function.update V e u)))
      ((Complex.continuous_ofReal.measurable.comp (hwU_m.const_mul _)).mul (hhU_m.sub hhV_m)) (Z1⁻¹ * (2 * M)) fun u => by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hρ1_nn u)]
      have h_diff_bd : ‖h (Function.update U e u) - h (Function.update V e u)‖ ≤ 2 * M := by
        calc ‖h (Function.update U e u) - h (Function.update V e u)‖
            ≤ ‖h (Function.update U e u)‖ + ‖h (Function.update V e u)‖ := norm_sub_le _ _
          _ ≤ M + M := add_le_add (hh_bd _) (hh_bd _)
          _ = 2 * M := by ring
      exact mul_le_mul (hρ1_bd u) h_diff_bd (norm_nonneg _) (inv_nonneg.mpr hZ1_pos.le)
    have hi_D := integrable_of_measurable_bound (suHaar N)
      (fun u => ((ρ1 u - ρ2 u : ℝ) : ℂ) * h (Function.update V e u))
      ((Complex.continuous_ofReal.measurable.comp ((hwU_m.const_mul _).sub (hwV_m.const_mul _))).mul hhV_m) ((Z1⁻¹ + Z2⁻¹) * M) fun u => by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      have h_rho_bd : |ρ1 u - ρ2 u| ≤ Z1⁻¹ + Z2⁻¹ := by
        calc |ρ1 u - ρ2 u| ≤ |ρ1 u| + |ρ2 u| := abs_sub _ _
          _ = ρ1 u + ρ2 u := by rw [abs_of_nonneg (hρ1_nn u), abs_of_nonneg (hρ2_nn u)]
          _ ≤ Z1⁻¹ + Z2⁻¹ := add_le_add (hρ1_bd u) (hρ2_bd u)
      exact mul_le_mul h_rho_bd (hh_bd _) (norm_nonneg _) (add_nonneg (inv_nonneg.mpr hZ1_pos.le) (inv_nonneg.mpr hZ2_pos.le))
    dsimp [condGibbsExp]
    change ((Z1⁻¹ : ℝ) : ℂ) * ∫ u, ((condGibbsWeight β e U u : ℝ) : ℂ) *
        h (Function.update U e u) ∂(suHaar N) -
      ((Z2⁻¹ : ℝ) : ℂ) * ∫ u, ((condGibbsWeight β e V u : ℝ) : ℂ) *
        h (Function.update V e u) ∂(suHaar N) = _
    rw [← MeasureTheory.integral_const_mul, ← MeasureTheory.integral_const_mul]
    have h_eq1 : (fun a => ((Z1⁻¹ : ℝ) : ℂ) * (((condGibbsWeight β e U a : ℝ) : ℂ) *
          h (Function.update U e a))) =
        fun u => ((ρ1 u : ℝ) : ℂ) * h (Function.update U e u) := by
      funext u; dsimp [ρ1]; push_cast; ring
    have h_eq2 : (fun a => ((Z2⁻¹ : ℝ) : ℂ) * (((condGibbsWeight β e V a : ℝ) : ℂ) *
          h (Function.update V e a))) =
        fun u => ((ρ2 u : ℝ) : ℂ) * h (Function.update V e u) := by
      funext u; dsimp [ρ2]; push_cast; ring
    rw [h_eq1, h_eq2]
    rw [← MeasureTheory.integral_sub hi_A hi_B, ← MeasureTheory.integral_add hi_C hi_D]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
    push_cast; ring
  have h_term1_bd :
      ‖∫ u, ((ρ1 u : ℝ) : ℂ) * (h (Function.update U e u) - h (Function.update V e u)) ∂(suHaar N)‖ ≤
        setOsc S_f h := by
    have hi_diff : MeasureTheory.Integrable
        (fun u => ‖((ρ1 u : ℝ) : ℂ) * (h (Function.update U e u) - h (Function.update V e u))‖)
        (suHaar N) :=
      (MeasureTheory.integrable_const (Z1⁻¹ * (2 * M))).mono'
        ((Complex.continuous_ofReal.measurable.comp (hwU_m.const_mul _)).mul
          (hhU_m.sub hhV_m)).stronglyMeasurable.aestronglyMeasurable.norm
        (Filter.Eventually.of_forall fun u => by
          rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _), norm_mul, Complex.norm_real,
            Real.norm_eq_abs, abs_of_nonneg (hρ1_nn u)]
          exact mul_le_mul (hρ1_bd u)
            ((norm_sub_le _ _).trans (by linarith [hh_bd (Function.update U e u), hh_bd (Function.update V e u)]))
            (norm_nonneg _) (inv_nonneg.mpr hZ1_pos.le))
    have h_pt_osc : ∀ u, ‖h (Function.update U e u) - h (Function.update V e u)‖ ≤ setOsc S_f h :=
      fun u => norm_sub_le_setOsc S_f h M hh_bd fun e'' he'' => by
        by_cases h_e : e'' = e
        · subst h_e; simp
        · simp [Function.update_of_ne h_e, hUV e'' he'']
    have h_int_r1 : MeasureTheory.Integrable (fun u => ρ1 u * setOsc S_f h) (suHaar N) :=
      (MeasureTheory.integrable_const (Z1⁻¹ * (2 * M))).mono'
        ((hwU_m.const_mul _).mul_const _).stronglyMeasurable.aestronglyMeasurable
        (Filter.Eventually.of_forall fun u => by
          rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg
            (hρ1_nn u) (setOsc_nonneg S_f h M hh_bd))]
          exact mul_le_mul (hρ1_bd u) (setOsc_le_two_mul S_f h M hh_bd)
            (setOsc_nonneg S_f h M hh_bd) (inv_nonneg.mpr hZ1_pos.le))
    calc ‖∫ u, ((ρ1 u : ℝ) : ℂ) * (h (Function.update U e u) - h (Function.update V e u)) ∂(suHaar N)‖
        ≤ ∫ u, ‖((ρ1 u : ℝ) : ℂ) * (h (Function.update U e u) - h (Function.update V e u))‖ ∂(suHaar N) :=
            MeasureTheory.norm_integral_le_integral_norm _
      _ ≤ ∫ u, ρ1 u * setOsc S_f h ∂(suHaar N) :=
            MeasureTheory.integral_mono hi_diff h_int_r1 fun u => by
              rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
                abs_of_nonneg (hρ1_nn u)]
              exact mul_le_mul_of_nonneg_left (h_pt_osc u) (hρ1_nn u)
      _ = (∫ u, ρ1 u ∂(suHaar N)) * setOsc S_f h := MeasureTheory.integral_mul_const _ _
      _ = setOsc S_f h := by
            have hρ1_i : ∫ u, ρ1 u ∂(suHaar N) = 1 := by
              dsimp [ρ1]; rw [MeasureTheory.integral_const_mul, inv_mul_cancel₀ hZ1_pos.ne']
            rw [hρ1_i, one_mul]
  have h_term2_bd :
      ‖∫ u, ((ρ1 u - ρ2 u : ℝ) : ℂ) * h (Function.update V e u) ∂(suHaar N)‖ ≤
        (if ∃ e' ∈ S_f, SharesPlaq4 Ls Lt e e' then 1 - Real.exp (-12 * β) else 0) * linkOsc h e := by
    by_cases hadj : ∃ e' ∈ S_f, SharesPlaq4 Ls Lt e e'
    · rw [if_pos hadj]
      refine condDensity_tv_bound (fun u => h (Function.update V e u)) hhV_m
        (linkOsc h e) (linkOsc_nonneg h M hh_bd e)
        (fun u v => norm_sub_le_linkOsc h M hh_bd e fun e'' he'' => by
          simp [Function.update_of_ne he''])
        M (fun u => hh_bd _) ρ1 ρ2 (hwU_m.const_mul _) (hwV_m.const_mul _)
        (Real.exp (-12 * β)) (Real.exp_pos _).le (Real.exp_le_one_iff.mpr (by linarith))
        (fun u => by
          dsimp [ρ1]
          calc Real.exp (-12 * β) = 1 * Real.exp (-12 * β) := (one_mul _).symm
            _ ≤ Z1⁻¹ * condGibbsWeight β e U u := mul_le_mul ((one_le_inv₀ hZ1_pos).mpr hZ1_bds.2)
                (condGibbsWeight_bounds β hβ e U u).1 (Real.exp_pos _).le (inv_nonneg.mpr hZ1_pos.le))
        (fun u => by
          dsimp [ρ2]
          calc Real.exp (-12 * β) = 1 * Real.exp (-12 * β) := (one_mul _).symm
            _ ≤ Z2⁻¹ * condGibbsWeight β e V u := mul_le_mul ((one_le_inv₀ hZ2_pos).mpr hZ2_bds.2)
                (condGibbsWeight_bounds β hβ e V u).1 (Real.exp_pos _).le (inv_nonneg.mpr hZ2_pos.le))
        (fun u => (hρ1_bd u).trans (inv_anti₀ (Real.exp_pos _) hZ1_bds.1))
        (fun u => (hρ2_bd u).trans (inv_anti₀ (Real.exp_pos _) hZ2_bds.1))
        (by dsimp [ρ1]; rw [MeasureTheory.integral_const_mul, inv_mul_cancel₀ hZ1_pos.ne'])
        (by dsimp [ρ2]; rw [MeasureTheory.integral_const_mul, inv_mul_cancel₀ hZ2_pos.ne'])
    · rw [if_neg hadj, zero_mul]
      have hw_eq : ∀ u, condGibbsWeight β e U u = condGibbsWeight β e V u := fun u => by
        dsimp [condGibbsWeight]
        rw [show (plaqsTouching Ls Lt e).map (fun p => wilsonPlaquetteTerm p (Function.update U e u)) =
            (plaqsTouching Ls Lt e).map (fun p => wilsonPlaquetteTerm p (Function.update V e u)) from
          List.map_congr_left fun p hp => by
            rw [plaqsTouching, List.mem_filter] at hp
            have he_p : e ∈ p.loop.map Prod.fst := of_decide_eq_true hp.2
            refine wilsonPlaquetteTerm_depends_on_links p _ _ fun e'' b hm => ?_
            by_cases h_e : e'' = e
            · rw [h_e, Function.update_self, Function.update_self]
            · have he''_p : e'' ∈ p.loop.map Prod.fst := List.mem_map.mpr ⟨(e'', b), hm, rfl⟩
              have he''_not : e'' ∉ S_f := fun hmem => hadj ⟨e'', hmem, ⟨Ne.symm h_e, p, hp.1, he_p, he''_p⟩⟩
              rw [Function.update_of_ne h_e, Function.update_of_ne h_e, hUV e'' he''_not]]
      have hρ_eq : ∀ u, ρ1 u - ρ2 u = 0 := fun u => by
        have hZ_eq : Z1 = Z2 := by dsimp [Z1, Z2]; simp_rw [hw_eq]
        dsimp [ρ1, ρ2]; rw [hZ_eq, hw_eq u, sub_self]
      simp_rw [hρ_eq, Complex.ofReal_zero, zero_mul, MeasureTheory.integral_zero, norm_zero]
      exact le_rfl
  rw [h_ce_split]
  exact (norm_add_le _ _).trans (add_le_add h_term1_bd h_term2_bd)

theorem plaqDist4_eq_zero_iff {Ls Lt : ℕ} [NeZero Ls] [NeZero Lt]
    {S : Finset (cubicTorus4 Ls Lt).Link} {e : (cubicTorus4 Ls Lt).Link}
    (h_reach : ∃ k, ∃ e₀ ∈ S, PlaqWalk Ls Lt k e e₀) :
    plaqDist4 Ls Lt S e = 0 ↔ e ∈ S := by
  classical
  constructor
  · intro h0
    dsimp [plaqDist4] at h0
    rw [dif_pos h_reach] at h0
    have hspec := Nat.find_spec h_reach
    rw [h0] at hspec
    rcases hspec with ⟨e₀, he₀, hw⟩
    cases hw
    exact he₀
  · exact plaqDist4_mem

theorem plaqDist4_eq_one_of_adj {Ls Lt : ℕ} [NeZero Ls] [NeZero Lt]
    {S : Finset (cubicTorus4 Ls Lt).Link} {e : (cubicTorus4 Ls Lt).Link}
    (he : e ∉ S) (h_reach : ∃ k, ∃ e₀ ∈ S, PlaqWalk Ls Lt k e e₀)
    (hadj : ∃ e' ∈ S, SharesPlaq4 Ls Lt e e') :
    plaqDist4 Ls Lt S e = 1 := by
  classical
  rcases hadj with ⟨e', he', hsh⟩
  have hle1 : plaqDist4 Ls Lt S e ≤ 1 := by
    dsimp [plaqDist4]; rw [dif_pos h_reach]
    exact Nat.find_min' h_reach ⟨e', he', PlaqWalk.step hsh (PlaqWalk.zero e')⟩
  have hne0 : plaqDist4 Ls Lt S e ≠ 0 :=
    fun h0 => he ((plaqDist4_eq_zero_iff h_reach).mp h0)
  omega

noncomputable def dobrushinWeight (Ls Lt : ℕ) [NeZero Ls] [NeZero Lt] (β : ℝ)
    (S_f : Finset (cubicTorus4 Ls Lt).Link) (e : (cubicTorus4 Ls Lt).Link) : ℝ :=
  (Real.sqrt (18 * (1 - Real.exp (-12 * β)))) ^ (plaqDist4 Ls Lt S_f e)

noncomputable def dobrushinPhiExt (Ls Lt N : ℕ) [NeZero Ls] [NeZero Lt] (β : ℝ)
    (S_f : Finset (cubicTorus4 Ls Lt).Link)
    (h : GaugeField (cubicTorus4 Ls Lt) (Matrix.specialUnitaryGroup (Fin N) ℂ) → ℂ) : ℝ :=
  ∑ e ∈ Finset.univ \ S_f, dobrushinWeight Ls Lt β S_f e * linkOsc h e

noncomputable def dobrushinPsiSharp (Ls Lt N : ℕ) [NeZero Ls] [NeZero Lt] (β : ℝ)
    (S_f : Finset (cubicTorus4 Ls Lt).Link)
    (h : GaugeField (cubicTorus4 Ls Lt) (Matrix.specialUnitaryGroup (Fin N) ℂ) → ℂ) : ℝ :=
  let α := 18 * (1 - Real.exp (-12 * β))
  let ρ := Real.sqrt α
  let c := 1 - Real.exp (-12 * β)
  setOsc S_f h + (c / (ρ * (1 - ρ))) * dobrushinPhiExt Ls Lt N β S_f h

theorem dobrushin_lyapunov_step (Ls Lt N : ℕ) [NeZero Ls] [NeZero Lt]
    (β : ℝ) (hβ : 0 ≤ β)
    (h_dob : 18 * (1 - Real.exp (-12 * β)) < 1)
    (h_pos : 0 < 18 * (1 - Real.exp (-12 * β)))
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (S_f : Finset (cubicTorus4 Ls Lt).Link)
    (e : (cubicTorus4 Ls Lt).Link) (he_not : e ∉ S_f)
    (h : GaugeField (cubicTorus4 Ls Lt) (Matrix.specialUnitaryGroup (Fin N) ℂ) → ℂ)
    (hh_m : Measurable h) (M_g : ℝ) (hMg : 0 ≤ M_g) (hh_bd : ∀ U, ‖h U‖ ≤ M_g)
    (h_reach : ∀ e' : (cubicTorus4 Ls Lt).Link, ∃ k, ∃ e₀ ∈ S_f, PlaqWalk Ls Lt k e' e₀) :
    let ρ := Real.sqrt (18 * (1 - Real.exp (-12 * β)))
    let h' := condGibbsExp Ls Lt N β e h
    dobrushinPhiExt Ls Lt N β S_f h' ≤
      dobrushinPhiExt Ls Lt N β S_f h - (1 - ρ) * (dobrushinWeight Ls Lt β S_f e * linkOsc h e) ∧
    dobrushinPsiSharp Ls Lt N β S_f h' ≤ dobrushinPsiSharp Ls Lt N β S_f h := by
  let α := 18 * (1 - Real.exp (-12 * β))
  let ρ := Real.sqrt α
  let c := 1 - Real.exp (-12 * β)
  have hρ_pos : 0 < ρ := Real.sqrt_pos.mpr h_pos
  have hρ_lt1 : ρ < 1 := by
    calc ρ < Real.sqrt 1 := Real.sqrt_lt_sqrt h_pos.le h_dob
      _ = 1 := Real.sqrt_one
  have h1ρ_pos : 0 < 1 - ρ := by linarith
  have hρ_sq : ρ * ρ = α := Real.mul_self_sqrt h_pos.le
  have hc_nn : 0 ≤ c := by
    linarith [Real.exp_le_one_iff.mpr (by linarith : -12 * β ≤ 0)]
  have hw_pos : ∀ e', 0 < dobrushinWeight Ls Lt β S_f e' := fun e' =>
    pow_pos hρ_pos _
  have he : e ∈ Finset.univ \ S_f := Finset.mem_sdiff.mpr ⟨Finset.mem_univ e, he_not⟩
  have hd_ge1 : 1 ≤ plaqDist4 Ls Lt S_f e := by
    have hne0 : plaqDist4 Ls Lt S_f e ≠ 0 :=
      fun h0 => he_not ((plaqDist4_eq_zero_iff (h_reach e)).mp h0)
    omega
  let h' := condGibbsExp Ls Lt N β e h
  have h_osc_self : linkOsc h' e = 0 :=
    (condGibbsExp_osc_bound Ls Lt N β hβ e e h hh_m M_g hMg hh_bd).1 rfl
  have h_erase_split : dobrushinPhiExt Ls Lt N β S_f h' =
      ∑ e' ∈ (Finset.univ \ S_f).erase e, dobrushinWeight Ls Lt β S_f e' * linkOsc h' e' := by
    dsimp [dobrushinPhiExt]
    rw [← Finset.add_sum_erase (Finset.univ \ S_f)
      (fun e' => dobrushinWeight Ls Lt β S_f e' * linkOsc h' e') he,
      h_osc_self, mul_zero, zero_add]
  have h_erase_eq : ∑ e' ∈ (Finset.univ \ S_f).erase e,
        dobrushinWeight Ls Lt β S_f e' * linkOsc h e' =
      dobrushinPhiExt Ls Lt N β S_f h - dobrushinWeight Ls Lt β S_f e * linkOsc h e := by
    dsimp [dobrushinPhiExt]
    rw [← Finset.add_sum_erase (Finset.univ \ S_f)
      (fun e' => dobrushinWeight Ls Lt β S_f e' * linkOsc h e') he]
    ring
  have h_sum_other :
      ∑ e' ∈ (Finset.univ \ S_f).erase e, dobrushinWeight Ls Lt β S_f e' * linkOsc h' e' ≤
        (dobrushinPhiExt Ls Lt N β S_f h - dobrushinWeight Ls Lt β S_f e * linkOsc h e) +
        (∑ e' ∈ (Finset.univ \ S_f).erase e,
          dobrushinWeight Ls Lt β S_f e' * dobrushinCoeff Ls Lt β e e') * linkOsc h e := by
    rw [← h_erase_eq, Finset.sum_mul, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun e' he' => ?_
    have hne : e' ≠ e := (Finset.mem_erase.mp he').1
    have h_osc := (condGibbsExp_osc_bound Ls Lt N β hβ e e' h hh_m M_g hMg hh_bd).2 hne
    calc dobrushinWeight Ls Lt β S_f e' * linkOsc h' e'
        ≤ dobrushinWeight Ls Lt β S_f e' * (linkOsc h e' + dobrushinCoeff Ls Lt β e e' * linkOsc h e) :=
            mul_le_mul_of_nonneg_left h_osc (hw_pos e').le
      _ = dobrushinWeight Ls Lt β S_f e' * linkOsc h e' +
            dobrushinWeight Ls Lt β S_f e' * dobrushinCoeff Ls Lt β e e' * linkOsc h e := by ring
  have h_adj_sum :
      ∑ e' ∈ (Finset.univ \ S_f).erase e,
        dobrushinWeight Ls Lt β S_f e' * dobrushinCoeff Ls Lt β e e' ≤
      ρ * dobrushinWeight Ls Lt β S_f e := by
    have h_each : ∀ e',
        dobrushinWeight Ls Lt β S_f e' * dobrushinCoeff Ls Lt β e e' ≤
          ρ⁻¹ * dobrushinWeight Ls Lt β S_f e * dobrushinCoeff Ls Lt β e e' := by
      intro e'
      by_cases hadj : SharesPlaq4 Ls Lt e e'
      · have h_sub_le : plaqDist4 Ls Lt S_f e - 1 ≤ plaqDist4 Ls Lt S_f e' := by
          have := plaqDist4_adj_le S_f hadj (h_reach e'); omega
        have h_w_le : dobrushinWeight Ls Lt β S_f e' ≤ ρ ^ (plaqDist4 Ls Lt S_f e - 1) :=
          pow_le_pow_of_le_one hρ_pos.le hρ_lt1.le h_sub_le
        have h_pow_eq : ρ ^ (plaqDist4 Ls Lt S_f e - 1) = ρ⁻¹ * dobrushinWeight Ls Lt β S_f e := by
          have h1 : ρ * ρ ^ (plaqDist4 Ls Lt S_f e - 1) = dobrushinWeight Ls Lt β S_f e := by
            dsimp [dobrushinWeight]; rw [← pow_succ', Nat.sub_add_cancel hd_ge1]
          rw [← h1, ← mul_assoc, inv_mul_cancel₀ hρ_pos.ne', one_mul]
        exact mul_le_mul_of_nonneg_right (h_w_le.trans_eq h_pow_eq)
          (by dsimp [dobrushinCoeff]; rw [if_pos hadj]; exact hc_nn)
      · have hc0 : dobrushinCoeff Ls Lt β e e' = 0 := by dsimp [dobrushinCoeff]; rw [if_neg hadj]
        rw [hc0, mul_zero, mul_zero]
    calc ∑ e' ∈ (Finset.univ \ S_f).erase e,
          dobrushinWeight Ls Lt β S_f e' * dobrushinCoeff Ls Lt β e e'
        ≤ ∑ e' : (cubicTorus4 Ls Lt).Link,
            dobrushinWeight Ls Lt β S_f e' * dobrushinCoeff Ls Lt β e e' :=
            Finset.sum_le_univ_sum_of_nonneg fun e' =>
              mul_nonneg (hw_pos e').le (by
                dsimp [dobrushinCoeff]; split_ifs <;> [exact hc_nn; exact le_rfl])
      _ ≤ ∑ e' : (cubicTorus4 Ls Lt).Link,
            ρ⁻¹ * dobrushinWeight Ls Lt β S_f e * dobrushinCoeff Ls Lt β e e' :=
            Finset.sum_le_sum fun e' _ => h_each e'
      _ = ρ⁻¹ * dobrushinWeight Ls Lt β S_f e *
            ∑ e' : (cubicTorus4 Ls Lt).Link, dobrushinCoeff Ls Lt β e e' := by
            rw [← Finset.mul_sum]
      _ ≤ ρ⁻¹ * dobrushinWeight Ls Lt β S_f e * α :=
            mul_le_mul_of_nonneg_left (dobrushinCoeff_row_sum_le Ls Lt β hβ e)
              (mul_nonneg (inv_nonneg.mpr hρ_pos.le) (hw_pos e).le)
      _ = ρ * dobrushinWeight Ls Lt β S_f e := by rw [← hρ_sq]; field_simp [hρ_pos.ne']
  have h_Phi_drop : dobrushinPhiExt Ls Lt N β S_f h' ≤
      dobrushinPhiExt Ls Lt N β S_f h - (1 - ρ) * (dobrushinWeight Ls Lt β S_f e * linkOsc h e) := by
    rw [h_erase_split]
    calc ∑ e' ∈ (Finset.univ \ S_f).erase e, dobrushinWeight Ls Lt β S_f e' * linkOsc h' e'
        ≤ (dobrushinPhiExt Ls Lt N β S_f h - dobrushinWeight Ls Lt β S_f e * linkOsc h e) +
            (ρ * dobrushinWeight Ls Lt β S_f e) * linkOsc h e :=
            h_sum_other.trans (add_le_add_right
              (mul_le_mul_of_nonneg_right h_adj_sum (linkOsc_nonneg h M_g hh_bd e)) _)
      _ = dobrushinPhiExt Ls Lt N β S_f h -
            (1 - ρ) * (dobrushinWeight Ls Lt β S_f e * linkOsc h e) := by ring
  have h_set_drop : setOsc S_f h' ≤
      setOsc S_f h + (c / ρ) * (dobrushinWeight Ls Lt β S_f e * linkOsc h e) := by
    have h1 := condGibbsExp_setOsc_bound Ls Lt N β hβ S_f e h hh_m M_g hMg hh_bd
    by_cases hadj : ∃ e' ∈ S_f, SharesPlaq4 Ls Lt e e'
    · have hwe : dobrushinWeight Ls Lt β S_f e = ρ := by
        dsimp [dobrushinWeight]
        rw [plaqDist4_eq_one_of_adj he_not (h_reach e) hadj, pow_one]
      rw [if_pos hadj] at h1
      have h_eq : c * linkOsc h e = (c / ρ) * (dobrushinWeight Ls Lt β S_f e * linkOsc h e) := by
        rw [hwe]; field_simp [hρ_pos.ne']
      rwa [h_eq] at h1
    · rw [if_neg hadj, zero_mul, add_zero] at h1
      have hnn : 0 ≤ (c / ρ) * (dobrushinWeight Ls Lt β S_f e * linkOsc h e) :=
        mul_nonneg (div_nonneg hc_nn hρ_pos.le)
          (mul_nonneg (hw_pos e).le (linkOsc_nonneg h M_g hh_bd e))
      linarith
  have h_Psi_drop : dobrushinPsiSharp Ls Lt N β S_f h' ≤ dobrushinPsiSharp Ls Lt N β S_f h := by
    dsimp [dobrushinPsiSharp]
    have h_mul_drop : (c / (ρ * (1 - ρ))) * dobrushinPhiExt Ls Lt N β S_f h' ≤
        (c / (ρ * (1 - ρ))) * (dobrushinPhiExt Ls Lt N β S_f h -
          (1 - ρ) * (dobrushinWeight Ls Lt β S_f e * linkOsc h e)) :=
      mul_le_mul_of_nonneg_left h_Phi_drop (div_nonneg hc_nn (mul_nonneg hρ_pos.le h1ρ_pos.le))
    have h_cancel : (c / (ρ * (1 - ρ))) *
        ((1 - ρ) * (dobrushinWeight Ls Lt β S_f e * linkOsc h e)) =
        (c / ρ) * (dobrushinWeight Ls Lt β S_f e * linkOsc h e) := by
      field_simp [hρ_pos.ne', h1ρ_pos.ne']
    linarith
  exact ⟨h_Phi_drop, h_Psi_drop⟩

theorem dobrushin_greedy_elim (Ls Lt N : ℕ) [NeZero Ls] [NeZero Lt]
    (β : ℝ) (hβ : 0 ≤ β)
    (h_dob : 18 * (1 - Real.exp (-12 * β)) < 1)
    (h_pos : 0 < 18 * (1 - Real.exp (-12 * β)))
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (S_f : Finset (cubicTorus4 Ls Lt).Link)
    (f g : GaugeField (cubicTorus4 Ls Lt) (Matrix.specialUnitaryGroup (Fin N) ℂ) → ℂ)
    (hf_m : Measurable f) (M_f M_g : ℝ) (hMf : 0 ≤ M_f) (hMg : 0 ≤ M_g)
    (hf_bd : ∀ U, ‖f U‖ ≤ M_f) (hf_supp : ∀ e, e ∉ S_f → linkOsc f e = 0)
    (h_reach : ∀ e : (cubicTorus4 Ls Lt).Link, ∃ k, ∃ e₀ ∈ S_f, PlaqWalk Ls Lt k e e₀)
    (δ : ℝ) (hδ : 0 < δ) :
    ∀ (k : ℕ) (h : GaugeField (cubicTorus4 Ls Lt) (Matrix.specialUnitaryGroup (Fin N) ℂ) → ℂ),
      Measurable h → (∀ U, ‖h U‖ ≤ M_g) →
      (cubic4Schwinger Ls Lt N β 2 ![f, h] -
        cubic4Schwinger Ls Lt N β 1 ![f] * cubic4Schwinger Ls Lt N β 1 ![h] =
       cubic4Schwinger Ls Lt N β 2 ![f, g] -
        cubic4Schwinger Ls Lt N β 1 ![f] * cubic4Schwinger Ls Lt N β 1 ![g]) →
      dobrushinPsiSharp Ls Lt N β S_f h ≤ dobrushinPsiSharp Ls Lt N β S_f g →
      dobrushinPhiExt Ls Lt N β S_f h ≤
        (k : ℝ) * ((1 - Real.sqrt (18 * (1 - Real.exp (-12 * β)))) * δ) →
      ∃ h', Measurable h' ∧ (∀ U, ‖h' U‖ ≤ M_g) ∧
        (cubic4Schwinger Ls Lt N β 2 ![f, h'] -
          cubic4Schwinger Ls Lt N β 1 ![f] * cubic4Schwinger Ls Lt N β 1 ![h'] =
         cubic4Schwinger Ls Lt N β 2 ![f, g] -
          cubic4Schwinger Ls Lt N β 1 ![f] * cubic4Schwinger Ls Lt N β 1 ![g]) ∧
        dobrushinPsiSharp Ls Lt N β S_f h' ≤ dobrushinPsiSharp Ls Lt N β S_f g ∧
        ∀ e ∈ Finset.univ \ S_f, dobrushinWeight Ls Lt β S_f e * linkOsc h' e < δ := by
  intro k
  induction k with
  | zero =>
    intro h hm hbd hcov hpsi hPhi
    refine ⟨h, hm, hbd, hcov, hpsi, fun e he => ?_⟩
    have h_le : dobrushinWeight Ls Lt β S_f e * linkOsc h e ≤ dobrushinPhiExt Ls Lt N β S_f h :=
      Finset.single_le_sum (fun e' _ =>
        mul_nonneg (pow_nonneg (Real.sqrt_nonneg _) _) (linkOsc_nonneg h M_g hbd e')) he
    simp only [Nat.cast_zero, zero_mul] at hPhi
    exact lt_of_le_of_lt (h_le.trans hPhi) hδ
  | succ k ih =>
    intro h hm hbd hcov hpsi hPhi
    by_cases h_all : ∀ e ∈ Finset.univ \ S_f, dobrushinWeight Ls Lt β S_f e * linkOsc h e < δ
    · exact ⟨h, hm, hbd, hcov, hpsi, h_all⟩
    · push_neg at h_all
      rcases h_all with ⟨e, he, h_ge⟩
      have he_not : e ∉ S_f := (Finset.mem_sdiff.mp he).2
      have h_drop := dobrushin_lyapunov_step Ls Lt N β hβ h_dob h_pos S_f e he_not h hm M_g hMg hbd h_reach
      let ρ := Real.sqrt (18 * (1 - Real.exp (-12 * β)))
      have h1ρ_nn : 0 ≤ 1 - ρ := by
        have hlt : ρ < 1 := by
          calc ρ < Real.sqrt 1 := Real.sqrt_lt_sqrt h_pos.le h_dob
            _ = 1 := Real.sqrt_one
        linarith
      have h_sub_ge : (1 - ρ) * δ ≤ (1 - ρ) * (dobrushinWeight Ls Lt β S_f e * linkOsc h e) :=
        mul_le_mul_of_nonneg_left h_ge h1ρ_nn
      have h_next_Phi : dobrushinPhiExt Ls Lt N β S_f (condGibbsExp Ls Lt N β e h) ≤
          (k : ℝ) * ((1 - ρ) * δ) := by
        have h_cast : ((k + 1 : ℕ) : ℝ) * ((1 - ρ) * δ) =
            (k : ℝ) * ((1 - ρ) * δ) + (1 - ρ) * δ := by push_cast; ring
        linarith [h_drop.1, hPhi, h_cast]
      have h_cov' :
          cubic4Schwinger Ls Lt N β 2 ![f, condGibbsExp Ls Lt N β e h] -
            cubic4Schwinger Ls Lt N β 1 ![f] *
              cubic4Schwinger Ls Lt N β 1 ![condGibbsExp Ls Lt N β e h] =
          cubic4Schwinger Ls Lt N β 2 ![f, g] -
            cubic4Schwinger Ls Lt N β 1 ![f] * cubic4Schwinger Ls Lt N β 1 ![g] := by
        rw [condGibbsExp_cov_invariant Ls Lt N β hβ e f h hf_m hm M_f M_g hMf hMg hf_bd hbd
          (hf_supp e he_not), hcov]
      exact ih (condGibbsExp Ls Lt N β e h)
        (measurable_condGibbsExp Ls Lt N β e h hm)
        (condGibbsExp_bound Ls Lt N β hβ e h hm M_g hMg hbd)
        h_cov' (h_drop.2.trans hpsi) h_next_Phi

theorem dobrushin_cov_bound_of_osc (Ls Lt N : ℕ) [NeZero Ls] [NeZero Lt]
    (β : ℝ) (hβ : 0 ≤ β)
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (S_f : Finset (cubicTorus4 Ls Lt).Link)
    (f h : GaugeField (cubicTorus4 Ls Lt) (Matrix.specialUnitaryGroup (Fin N) ℂ) → ℂ)
    (hf_m : Measurable f) (hh_m : Measurable h)
    (M_f M_g : ℝ) (hMf : 0 ≤ M_f)
    (hf_bd : ∀ U, ‖f U‖ ≤ M_f) (hh_bd : ∀ U, ‖h U‖ ≤ M_g) :
    ‖cubic4Schwinger Ls Lt N β 2 ![f, h] -
      cubic4Schwinger Ls Lt N β 1 ![f] * cubic4Schwinger Ls Lt N β 1 ![h]‖ ≤
      M_f * (setOsc S_f h + ∑ e ∈ Finset.univ \ S_f, linkOsc h e) := by
  let G_4 := GaugeField (cubicTorus4 Ls Lt) (Matrix.specialUnitaryGroup (Fin N) ℂ)
  let μ_4 := spacetimeHaarMeasure Ls Lt N
  haveI := suHaar_prob N
  haveI := spacetimeHaarMeasure_prob Ls Lt N
  let Z := cubic4PartitionFn Ls Lt N β
  have hZ_pos : 0 < Z := cubic4PartitionFn_pos Ls Lt N β hβ
  let w4 := cubic4WilsonWeight Ls Lt N β
  have hMg : 0 ≤ M_g := (norm_nonneg (h (fun _ => 1))).trans (hh_bd (fun _ => 1))
  have hw4_m : Measurable w4 := measurable_cubic4WilsonWeight Ls Lt N β
  have hw4_nn : ∀ U, 0 ≤ w4 U := fun U => by unfold w4 cubic4WilsonWeight; exact (Real.exp_pos _).le
  have hw4_le1 : ∀ U, w4 U ≤ 1 := fun U => (cubic4WilsonWeight_bounds Ls Lt N β hβ U).2
  have hZc_eq : ((Z : ℝ) : ℂ) = ∫ U, ((w4 U : ℝ) : ℂ) ∂μ_4 := by
    have hwc := integrable_of_measurable_bound μ_4 (fun U => ((w4 U : ℝ) : ℂ))
      (Complex.continuous_ofReal.measurable.comp hw4_m) 1
      fun U => by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hw4_nn U)]; exact hw4_le1 U
    have hre : (∫ U, ((w4 U : ℝ) : ℂ) ∂μ_4).re = Z := by
      change RCLike.re (∫ U, ((w4 U : ℝ) : ℂ) ∂μ_4) = Z; rw [← integral_re hwc]; rfl
    have him : (∫ U, ((w4 U : ℝ) : ℂ) ∂μ_4).im = 0 := by
      have h1 : (∫ U, ((w4 U : ℝ) : ℂ) ∂μ_4).im =
          RCLike.re (-Complex.I * ∫ U, ((w4 U : ℝ) : ℂ) ∂μ_4) := by simp [Complex.mul_re]
      rw [h1, ← MeasureTheory.integral_const_mul, ← integral_re (hwc.const_mul (-Complex.I))]
      refine MeasureTheory.integral_eq_zero_of_ae (Filter.Eventually.of_forall fun U => ?_)
      simp [Complex.mul_re]
    exact Complex.ext hre.symm him.symm
  have h_double :
      ((Z : ℝ) : ℂ) * ((Z : ℝ) : ℂ) *
        (cubic4Schwinger Ls Lt N β 2 ![f, h] -
          cubic4Schwinger Ls Lt N β 1 ![f] * cubic4Schwinger Ls Lt N β 1 ![h]) =
        ∫ U, ∫ V, f U * (h U - h V) * ((w4 U * w4 V : ℝ) : ℂ) ∂μ_4 ∂μ_4 := by
    have h_Z_mul : ∀ (q : G_4 → ℂ),
        ((Z : ℝ) : ℂ) * cubic4Schwinger Ls Lt N β 1 ![q] =
          ∫ U, q U * ((w4 U : ℝ) : ℂ) ∂μ_4 := by
      intro q
      unfold cubic4Schwinger
      simp only [Fin.prod_univ_one, Matrix.cons_val_zero]
      change ((Z : ℝ) : ℂ) * (((Z : ℝ) : ℂ)⁻¹ *
          ∫ U, q U * ((w4 U : ℝ) : ℂ) ∂μ_4) = _
      rw [← mul_assoc, mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr hZ_pos.ne'), one_mul]
    have h_Z_mul2 :
        ((Z : ℝ) : ℂ) * cubic4Schwinger Ls Lt N β 2 ![f, h] =
          ∫ U, f U * h U * ((w4 U : ℝ) : ℂ) ∂μ_4 := by
      rw [cubic4Schwinger_two_eq_one_mul]; exact h_Z_mul _
    have h_lhs_id :
        ((Z : ℝ) : ℂ) * ((Z : ℝ) : ℂ) *
          (cubic4Schwinger Ls Lt N β 2 ![f, h] -
            cubic4Schwinger Ls Lt N β 1 ![f] * cubic4Schwinger Ls Lt N β 1 ![h]) =
          ((Z : ℝ) : ℂ) * (∫ U, f U * h U * ((w4 U : ℝ) : ℂ) ∂μ_4) -
            (∫ U, f U * ((w4 U : ℝ) : ℂ) ∂μ_4) * (∫ V, h V * ((w4 V : ℝ) : ℂ) ∂μ_4) := by
      rw [← h_Z_mul f, ← h_Z_mul h, ← h_Z_mul2]; ring
    have h_in : ∀ U : G_4,
        (∫ V, f U * (h U - h V) * ((w4 U * w4 V : ℝ) : ℂ) ∂μ_4) =
          (f U * h U * ((w4 U : ℝ) : ℂ)) * ((Z : ℝ) : ℂ) -
            (f U * ((w4 U : ℝ) : ℂ)) * (∫ V, h V * ((w4 V : ℝ) : ℂ) ∂μ_4) := by
      intro U
      have hi1 := integrable_of_measurable_bound μ_4
        (fun V => (f U * h U * ((w4 U : ℝ) : ℂ)) * ((w4 V : ℝ) : ℂ))
        (measurable_const.mul (Complex.continuous_ofReal.measurable.comp hw4_m))
        (M_f * M_g) fun V => by
        rw [norm_mul, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
          Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (hw4_nn U), abs_of_nonneg (hw4_nn V)]
        have h1 : ‖f U‖ * ‖h U‖ ≤ M_f * M_g :=
          mul_le_mul (hf_bd U) (hh_bd U) (norm_nonneg _) hMf
        have h2 : ‖f U‖ * ‖h U‖ * w4 U ≤ M_f * M_g :=
          (mul_le_of_le_one_right (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (hw4_le1 U)).trans h1
        exact (mul_le_of_le_one_right (mul_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (hw4_nn U)) (hw4_le1 V)).trans h2
      have hi2 := integrable_of_measurable_bound μ_4
        (fun V => (f U * ((w4 U : ℝ) : ℂ)) * (h V * ((w4 V : ℝ) : ℂ)))
        (measurable_const.mul (hh_m.mul (Complex.continuous_ofReal.measurable.comp hw4_m)))
        (M_f * M_g) fun V => by
        rw [norm_mul, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
          Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (hw4_nn U), abs_of_nonneg (hw4_nn V)]
        have h1 : ‖f U‖ * w4 U ≤ M_f :=
          (mul_le_of_le_one_right (norm_nonneg _) (hw4_le1 U)).trans (hf_bd U)
        have h2 : ‖h V‖ * w4 V ≤ M_g :=
          (mul_le_of_le_one_right (norm_nonneg _) (hw4_le1 V)).trans (hh_bd V)
        exact mul_le_mul h1 h2 (mul_nonneg (norm_nonneg _) (hw4_nn V)) hMf
      have h_fn : (fun V => f U * (h U - h V) * ((w4 U * w4 V : ℝ) : ℂ)) =
          fun V => (f U * h U * ((w4 U : ℝ) : ℂ)) * ((w4 V : ℝ) : ℂ) -
            (f U * ((w4 U : ℝ) : ℂ)) * (h V * ((w4 V : ℝ) : ℂ)) := by
        funext V; push_cast; ring
      rw [h_fn, MeasureTheory.integral_sub hi1 hi2, MeasureTheory.integral_const_mul,
        MeasureTheory.integral_const_mul, ← hZc_eq]
    have ho1 := integrable_of_measurable_bound μ_4
      (fun U => (f U * h U * ((w4 U : ℝ) : ℂ)) * ((Z : ℝ) : ℂ))
      (((hf_m.mul hh_m).mul (Complex.continuous_ofReal.measurable.comp hw4_m)).mul measurable_const)
      (M_f * M_g * Z) fun U => by
      rw [norm_mul, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
        Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (hw4_nn U), abs_of_nonneg hZ_pos.le]
      have h1 : ‖f U‖ * ‖h U‖ ≤ M_f * M_g :=
        mul_le_mul (hf_bd U) (hh_bd U) (norm_nonneg _) hMf
      have h2 : ‖f U‖ * ‖h U‖ * w4 U ≤ M_f * M_g :=
        (mul_le_of_le_one_right (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (hw4_le1 U)).trans h1
      exact mul_le_mul_of_nonneg_right h2 hZ_pos.le
    have ho2 := integrable_of_measurable_bound μ_4
      (fun U => (f U * ((w4 U : ℝ) : ℂ)) * (∫ V, h V * ((w4 V : ℝ) : ℂ) ∂μ_4))
      ((hf_m.mul (Complex.continuous_ofReal.measurable.comp hw4_m)).mul measurable_const)
      (M_f * M_g) fun U => by
      have hiV : ‖∫ V, h V * ((w4 V : ℝ) : ℂ) ∂μ_4‖ ≤ M_g := by
        have h_iV := integrable_of_measurable_bound μ_4
          (fun V => h V * ((w4 V : ℝ) : ℂ))
          (hh_m.mul (Complex.continuous_ofReal.measurable.comp hw4_m)) M_g fun V => by
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hw4_nn V)]
          exact (mul_le_of_le_one_right (norm_nonneg _) (hw4_le1 V)).trans (hh_bd V)
        calc ‖∫ V, h V * ((w4 V : ℝ) : ℂ) ∂μ_4‖
            ≤ ∫ V, ‖h V * ((w4 V : ℝ) : ℂ)‖ ∂μ_4 := MeasureTheory.norm_integral_le_integral_norm _
          _ ≤ ∫ _V, M_g ∂μ_4 := MeasureTheory.integral_mono h_iV.norm (MeasureTheory.integrable_const _)
                fun V => by
                  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hw4_nn V)]
                  exact (mul_le_of_le_one_right (norm_nonneg _) (hw4_le1 V)).trans (hh_bd V)
          _ = M_g := by simp [Measure.real, MeasureTheory.measure_univ]
      rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hw4_nn U)]
      exact mul_le_mul ((mul_le_of_le_one_right (norm_nonneg _) (hw4_le1 U)).trans (hf_bd U))
        hiV (norm_nonneg _) hMf
    rw [h_lhs_id]
    simp_rw [h_in]
    rw [MeasureTheory.integral_sub ho1 ho2, MeasureTheory.integral_mul_const,
      MeasureTheory.integral_mul_const]
    ring
  let D_h : ℝ := setOsc S_f h + ∑ e ∈ Finset.univ \ S_f, linkOsc h e
  have hD_h_nn : 0 ≤ D_h :=
    add_nonneg (setOsc_nonneg S_f h M_g hh_bd)
      (Finset.sum_nonneg fun e _ => linkOsc_nonneg h M_g hh_bd e)
  have h_osc_UV : ∀ U V : G_4, ‖h U - h V‖ ≤ D_h := fun U V => by
    let W : G_4 := fun e => if e ∈ S_f then U e else V e
    have hUW : ∀ e ∉ Finset.univ \ S_f, U e = W e := fun e he => by
      have he_sf : e ∈ S_f := by
        by_contra hns; exact he (Finset.mem_sdiff.mpr ⟨Finset.mem_univ e, hns⟩)
      simp [W, he_sf]
    have hWV : ∀ e ∉ S_f, W e = V e := fun e he => by simp [W, he]
    calc ‖h U - h V‖ = ‖(h U - h W) + (h W - h V)‖ := by rw [sub_add_sub_cancel]
      _ ≤ ‖h U - h W‖ + ‖h W - h V‖ := norm_add_le _ _
      _ ≤ (∑ e ∈ Finset.univ \ S_f, linkOsc h e) + setOsc S_f h :=
          add_le_add (norm_sub_le_sum_linkOsc h M_g hh_bd (Finset.univ \ S_f) U W hUW)
            (norm_sub_le_setOsc S_f h M_g hh_bd hWV)
      _ = D_h := add_comm _ _
  have hw_int : MeasureTheory.Integrable w4 μ_4 :=
    (MeasureTheory.integrable_const (1 : ℝ)).mono' hw4_m.stronglyMeasurable.aestronglyMeasurable
      (Filter.Eventually.of_forall fun U => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hw4_nn U)]; exact hw4_le1 U)
  have h_int_V_norm : ∀ U : G_4,
      ‖∫ V, f U * (h U - h V) * ((w4 U * w4 V : ℝ) : ℂ) ∂μ_4‖ ≤ M_f * D_h * (w4 U * Z) := by
    intro U
    have h_iV := integrable_of_measurable_bound μ_4
      (fun V => f U * (h U - h V) * ((w4 U * w4 V : ℝ) : ℂ))
      ((measurable_const.mul (measurable_const.sub hh_m)).mul
        (Complex.continuous_ofReal.measurable.comp (measurable_const.mul hw4_m)))
      (M_f * D_h) fun V => by
      rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (mul_nonneg (hw4_nn U) (hw4_nn V))]
      have h1 : ‖f U‖ * ‖h U - h V‖ ≤ M_f * D_h :=
        mul_le_mul (hf_bd U) (h_osc_UV U V) (norm_nonneg _) hMf
      have h2 : ‖f U‖ * ‖h U - h V‖ * w4 U ≤ M_f * D_h :=
        (mul_le_of_le_one_right (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (hw4_le1 U)).trans h1
      rw [← mul_assoc]
      exact (mul_le_of_le_one_right (mul_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (hw4_nn U)) (hw4_le1 V)).trans h2
    calc ‖∫ V, f U * (h U - h V) * ((w4 U * w4 V : ℝ) : ℂ) ∂μ_4‖
        ≤ ∫ V, ‖f U * (h U - h V) * ((w4 U * w4 V : ℝ) : ℂ)‖ ∂μ_4 :=
            MeasureTheory.norm_integral_le_integral_norm _
      _ ≤ ∫ V, (M_f * D_h * w4 U) * w4 V ∂μ_4 :=
            MeasureTheory.integral_mono h_iV.norm (hw_int.const_mul _) fun V => by
              rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
                abs_of_nonneg (mul_nonneg (hw4_nn U) (hw4_nn V))]
              calc ‖f U‖ * ‖h U - h V‖ * (w4 U * w4 V)
                  ≤ (M_f * D_h) * (w4 U * w4 V) :=
                      mul_le_mul_of_nonneg_right (mul_le_mul (hf_bd U) (h_osc_UV U V)
                        (norm_nonneg _) hMf) (mul_nonneg (hw4_nn U) (hw4_nn V))
                _ = (M_f * D_h * w4 U) * w4 V := by ring
      _ = (M_f * D_h * w4 U) * Z := MeasureTheory.integral_const_mul _ _
      _ = M_f * D_h * (w4 U * Z) := by ring
  have h_outer_m : Measurable
      (fun U => ∫ V, f U * (h U - h V) * ((w4 U * w4 V : ℝ) : ℂ) ∂μ_4) := by
    have hm_prod : Measurable (fun q : G_4 × G_4 =>
        f q.1 * (h q.1 - h q.2) * ((w4 q.1 * w4 q.2 : ℝ) : ℂ)) :=
      ((hf_m.comp measurable_fst).mul
        ((hh_m.comp measurable_fst).sub (hh_m.comp measurable_snd))).mul
        (Complex.continuous_ofReal.measurable.comp
          ((hw4_m.comp measurable_fst).mul (hw4_m.comp measurable_snd)))
    exact MeasureTheory.StronglyMeasurable.measurable
      (MeasureTheory.StronglyMeasurable.integral_prod_right' hm_prod.stronglyMeasurable)
  have h_outer_int := integrable_of_measurable_bound μ_4
    (fun U => ∫ V, f U * (h U - h V) * ((w4 U * w4 V : ℝ) : ℂ) ∂μ_4)
    h_outer_m (M_f * D_h * Z) fun U =>
    (h_int_V_norm U).trans (mul_le_mul_of_nonneg_left
      (mul_le_of_le_one_left hZ_pos.le (hw4_le1 U)) (mul_nonneg hMf hD_h_nn))
  have h_tot : (Z * Z) * ‖cubic4Schwinger Ls Lt N β 2 ![f, h] -
        cubic4Schwinger Ls Lt N β 1 ![f] * cubic4Schwinger Ls Lt N β 1 ![h]‖ ≤
      (Z * Z) * (M_f * D_h) := by
    have h_lhs_norm : (Z * Z) * ‖cubic4Schwinger Ls Lt N β 2 ![f, h] -
          cubic4Schwinger Ls Lt N β 1 ![f] * cubic4Schwinger Ls Lt N β 1 ![h]‖ =
        ‖((Z : ℝ) : ℂ) * ((Z : ℝ) : ℂ) *
          (cubic4Schwinger Ls Lt N β 2 ![f, h] -
            cubic4Schwinger Ls Lt N β 1 ![f] * cubic4Schwinger Ls Lt N β 1 ![h])‖ := by
      rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hZ_pos, mul_assoc]
    rw [h_lhs_norm, h_double]
    calc ‖∫ U, ∫ V, f U * (h U - h V) * ((w4 U * w4 V : ℝ) : ℂ) ∂μ_4 ∂μ_4‖
        ≤ ∫ U, ‖∫ V, f U * (h U - h V) * ((w4 U * w4 V : ℝ) : ℂ) ∂μ_4‖ ∂μ_4 :=
            MeasureTheory.norm_integral_le_integral_norm _
      _ ≤ ∫ U, (M_f * D_h * Z) * w4 U ∂μ_4 :=
            MeasureTheory.integral_mono h_outer_int.norm (hw_int.const_mul _) fun U =>
              (h_int_V_norm U).trans_eq (by ring)
      _ = (M_f * D_h * Z) * Z := MeasureTheory.integral_const_mul _ _
      _ = (Z * Z) * (M_f * D_h) := by ring
  exact le_of_mul_le_mul_left h_tot (mul_pos hZ_pos hZ_pos)

/--
**Volume-independent strong-coupling exponential clustering (`Dobrushin` regime)**:
for all `Ls, Lt ≥ 1`, `N ≥ 2`, and `0 ≤ β` satisfying `α = 18 * (1 - exp (-12 * β)) < 1`,
every pair of bounded measurable gauge-field observables `f, g` supported on link sets `S_f, S_g`
at plaquette graph distance `D ≥ 1` (`∀ e_f ∈ S_f, ∀ e_g ∈ S_g, D ≤ d(e_f, e_g)`) satisfies
`‖S^{(2)}(f, g) - S^{(1)}(f) S^{(1)}(g)‖ ≤ C(β) * |S_g| * M_f * M_g * α^(D / 2)`,
with both `C(β)` and `m(β) = -½ log α > 0` completely independent of `Ls` and `Lt`.
-/
theorem cubic4Schwinger_strong_coupling_clustering (Ls Lt N : ℕ) [NeZero Ls] [NeZero Lt]
    (β : ℝ) (hβ : 0 ≤ β)
    (h_dob : 18 * (1 - Real.exp (-12 * β)) < 1)
    (h_pos : 0 < 18 * (1 - Real.exp (-12 * β)))
    [MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    [BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (S_f S_g : Finset (cubicTorus4 Ls Lt).Link)
    (f g : GaugeField (cubicTorus4 Ls Lt) (Matrix.specialUnitaryGroup (Fin N) ℂ) → ℂ)
    (hf_m : Measurable f) (hg_m : Measurable g)
    (M_f M_g : ℝ) (hMf : 0 ≤ M_f) (hMg : 0 ≤ M_g)
    (hf_bd : ∀ U, ‖f U‖ ≤ M_f) (hg_bd : ∀ U, ‖g U‖ ≤ M_g)
    (hf_supp : ∀ e, e ∉ S_f → linkOsc f e = 0)
    (hg_supp : ∀ e, e ∉ S_g → linkOsc g e = 0)
    (D : ℕ) (hD_pos : 1 ≤ D)
    (h_dist : ∀ e ∈ S_g, D ≤ plaqDist4 Ls Lt S_f e)
    (h_reach : ∀ e : (cubicTorus4 Ls Lt).Link,
      ∃ k, ∃ e₀ ∈ S_f, PlaqWalk Ls Lt k e e₀) :
    let α := 18 * (1 - Real.exp (-12 * β))
    ‖cubic4Schwinger Ls Lt N β 2 ![f, g] -
      cubic4Schwinger Ls Lt N β 1 ![f] * cubic4Schwinger Ls Lt N β 1 ![g]‖ ≤
      (2 * (1 - Real.exp (-12 * β)) / (Real.sqrt α * (1 - Real.sqrt α))) *
        (S_g.card : ℝ) * M_f * M_g * (Real.sqrt α) ^ D := by
  intro α
  let ρ : ℝ := Real.sqrt α
  let c : ℝ := 1 - Real.exp (-12 * β)
  have hρ_pos : 0 < ρ := Real.sqrt_pos.mpr h_pos
  have hρ_lt1 : ρ < 1 := by
    calc ρ < Real.sqrt 1 := Real.sqrt_lt_sqrt h_pos.le h_dob
      _ = 1 := Real.sqrt_one
  have h1ρ_pos : 0 < 1 - ρ := by linarith
  have hc_nn : 0 ≤ c := by
    linarith [Real.exp_le_one_iff.mpr (by linarith : -12 * β ≤ 0)]
  have h_Psi_g : dobrushinPsiSharp Ls Lt N β S_f g ≤
      (2 * c / (ρ * (1 - ρ))) * (S_g.card : ℝ) * M_g * ρ ^ D := by
    have h_set_g : setOsc S_f g = 0 := by
      refine setOsc_zero_of_disjoint S_f g M_g hg_bd fun e he => ?_
      apply hg_supp
      intro he_g
      have h1 := h_dist e he_g
      rw [plaqDist4_mem he] at h1
      omega
    have h_Phi_g : dobrushinPhiExt Ls Lt N β S_f g ≤ 2 * (S_g.card : ℝ) * M_g * ρ ^ D := by
      dsimp [dobrushinPhiExt]
      have h_each : ∀ e ∈ Finset.univ \ S_f,
          dobrushinWeight Ls Lt β S_f e * linkOsc g e ≤
            if e ∈ S_g then 2 * M_g * ρ ^ D else 0 := by
        intro e _
        by_cases he_g : e ∈ S_g
        · rw [if_pos he_g]
          have hw_le : dobrushinWeight Ls Lt β S_f e ≤ ρ ^ D :=
            pow_le_pow_of_le_one hρ_pos.le hρ_lt1.le (h_dist e he_g)
          calc dobrushinWeight Ls Lt β S_f e * linkOsc g e
              ≤ ρ ^ D * (2 * M_g) := mul_le_mul hw_le (linkOsc_le_two_mul g M_g hMg hg_bd e)
                  (linkOsc_nonneg g M_g hg_bd e) (pow_nonneg hρ_pos.le D)
            _ = 2 * M_g * ρ ^ D := by ring
        · rw [if_neg he_g, hg_supp e he_g, mul_zero]
      calc ∑ e ∈ Finset.univ \ S_f, dobrushinWeight Ls Lt β S_f e * linkOsc g e
          ≤ ∑ e ∈ Finset.univ \ S_f, (if e ∈ S_g then 2 * M_g * ρ ^ D else 0) :=
              Finset.sum_le_sum h_each
        _ = ∑ _e ∈ (Finset.univ \ S_f) ∩ S_g, (2 * M_g * ρ ^ D) := by
              rw [← Finset.sum_filter, Finset.filter_mem_eq_inter]
        _ ≤ ∑ _e ∈ S_g, (2 * M_g * ρ ^ D) :=
              Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_right
                (fun _ _ _ => mul_nonneg (mul_nonneg zero_le_two hMg) (pow_nonneg hρ_pos.le D))
        _ = 2 * (S_g.card : ℝ) * M_g * ρ ^ D := by
              rw [Finset.sum_const, nsmul_eq_mul]; ring
    dsimp [dobrushinPsiSharp]
    rw [h_set_g, zero_add]
    calc (c / (ρ * (1 - ρ))) * dobrushinPhiExt Ls Lt N β S_f g
        ≤ (c / (ρ * (1 - ρ))) * (2 * (S_g.card : ℝ) * M_g * ρ ^ D) :=
            mul_le_mul_of_nonneg_left h_Phi_g (div_nonneg hc_nn (mul_nonneg hρ_pos.le h1ρ_pos.le))
      _ = (2 * c / (ρ * (1 - ρ))) * (S_g.card : ℝ) * M_g * ρ ^ D := by ring
  apply le_of_forall_pos_le_add
  intro ε hε
  let d_max : ℕ := Finset.univ.sup (plaqDist4 Ls Lt S_f)
  let w_min : ℝ := ρ ^ d_max
  have hw_min_pos : 0 < w_min := pow_pos hρ_pos d_max
  have hw_ge_min : ∀ e, w_min ≤ dobrushinWeight Ls Lt β S_f e := fun e => by
    dsimp [w_min, dobrushinWeight]
    exact pow_le_pow_of_le_one hρ_pos.le hρ_lt1.le (Finset.le_sup (Finset.mem_univ e))
  let δ : ℝ := (ε * w_min) / ((M_f + 1) * (((Finset.univ \ S_f).card : ℝ) + 1))
  have hδ_pos : 0 < δ := by positivity
  let k : ℕ := Nat.ceil (dobrushinPhiExt Ls Lt N β S_f g / ((1 - ρ) * δ))
  have hk_ge : dobrushinPhiExt Ls Lt N β S_f g ≤ (k : ℝ) * ((1 - ρ) * δ) :=
    (div_le_iff₀ (mul_pos h1ρ_pos hδ_pos)).mp
      (Nat.le_ceil (dobrushinPhiExt Ls Lt N β S_f g / ((1 - ρ) * δ)))
  obtain ⟨h', hh'_m, hh'_bd, h'_cov, h'_psi, h'_small⟩ :=
    dobrushin_greedy_elim Ls Lt N β hβ h_dob h_pos S_f f g hf_m M_f M_g hMf hMg hf_bd hf_supp
      h_reach δ hδ_pos k g hg_m hg_bd rfl le_rfl hk_ge
  have h_ext_sum_le : M_f * ∑ e ∈ Finset.univ \ S_f, linkOsc h' e ≤ ε := by
    have h_each : ∀ e ∈ Finset.univ \ S_f, linkOsc h' e ≤ δ / w_min := fun e he => by
      have h1 : w_min * linkOsc h' e ≤ dobrushinWeight Ls Lt β S_f e * linkOsc h' e :=
        mul_le_mul_of_nonneg_right (hw_ge_min e) (linkOsc_nonneg h' M_g hh'_bd e)
      exact (le_div_iff₀ hw_min_pos).mpr (by rw [mul_comm]; exact h1.trans (h'_small e he).le)
    have h_sum_le : ∑ e ∈ Finset.univ \ S_f, linkOsc h' e ≤
        ((Finset.univ \ S_f).card : ℝ) * (δ / w_min) := by
      calc ∑ e ∈ Finset.univ \ S_f, linkOsc h' e
          ≤ ∑ _e ∈ Finset.univ \ S_f, (δ / w_min) := Finset.sum_le_sum h_each
        _ = ((Finset.univ \ S_f).card : ℝ) * (δ / w_min) := by simp [Finset.sum_const, nsmul_eq_mul]
    have h_prod_le : M_f * (((Finset.univ \ S_f).card : ℝ) * (δ / w_min)) ≤ ε := by
      dsimp [δ]
      have h_eq : M_f * (((Finset.univ \ S_f).card : ℝ) *
          ((ε * w_min / ((M_f + 1) * (((Finset.univ \ S_f).card : ℝ) + 1))) / w_min)) =
          ε * (M_f / (M_f + 1)) *
            (((Finset.univ \ S_f).card : ℝ) / (((Finset.univ \ S_f).card : ℝ) + 1)) := by
        field_simp [hw_min_pos.ne']
      rw [h_eq]
      have hm1 : M_f / (M_f + 1) ≤ 1 := (div_le_one (by linarith)).mpr (by linarith)
      have hc1 : ((Finset.univ \ S_f).card : ℝ) / (((Finset.univ \ S_f).card : ℝ) + 1) ≤ 1 :=
        (div_le_one (by positivity)).mpr (by linarith)
      calc ε * (M_f / (M_f + 1)) *
            (((Finset.univ \ S_f).card : ℝ) / (((Finset.univ \ S_f).card : ℝ) + 1))
          ≤ ε * 1 * 1 := mul_le_mul (mul_le_mul_of_nonneg_left hm1 hε.le) hc1
              (div_nonneg (Nat.cast_nonneg _) (by positivity)) (mul_nonneg hε.le zero_le_one)
        _ = ε := by ring
    exact (mul_le_mul_of_nonneg_left h_sum_le hMf).trans h_prod_le
  have h_set_le : setOsc S_f h' ≤ (2 * c / (ρ * (1 - ρ))) * (S_g.card : ℝ) * M_g * ρ ^ D := by
    have hPhi_nn : 0 ≤ dobrushinPhiExt Ls Lt N β S_f h' :=
      Finset.sum_nonneg fun e _ =>
        mul_nonneg (pow_nonneg hρ_pos.le _) (linkOsc_nonneg h' M_g hh'_bd e)
    have h_nn : 0 ≤ (c / (ρ * (1 - ρ))) * dobrushinPhiExt Ls Lt N β S_f h' :=
      mul_nonneg (div_nonneg hc_nn (mul_nonneg hρ_pos.le h1ρ_pos.le)) hPhi_nn
    have h1 : setOsc S_f h' ≤ dobrushinPsiSharp Ls Lt N β S_f h' := by
      dsimp [dobrushinPsiSharp]; linarith
    exact h1.trans (h'_psi.trans h_Psi_g)
  calc ‖cubic4Schwinger Ls Lt N β 2 ![f, g] -
        cubic4Schwinger Ls Lt N β 1 ![f] * cubic4Schwinger Ls Lt N β 1 ![g]‖
      = ‖cubic4Schwinger Ls Lt N β 2 ![f, h'] -
          cubic4Schwinger Ls Lt N β 1 ![f] * cubic4Schwinger Ls Lt N β 1 ![h']‖ := by
          rw [h'_cov]
    _ ≤ M_f * (setOsc S_f h' + ∑ e ∈ Finset.univ \ S_f, linkOsc h' e) :=
          dobrushin_cov_bound_of_osc Ls Lt N β hβ S_f f h' hf_m hh'_m M_f M_g hMf hf_bd hh'_bd
    _ = M_f * setOsc S_f h' + M_f * ∑ e ∈ Finset.univ \ S_f, linkOsc h' e := by ring
    _ ≤ M_f * ((2 * c / (ρ * (1 - ρ))) * (S_g.card : ℝ) * M_g * ρ ^ D) + ε :=
          add_le_add (mul_le_mul_of_nonneg_left h_set_le hMf) h_ext_sum_le
    _ = (2 * (1 - Real.exp (-12 * β)) / (Real.sqrt α * (1 - Real.sqrt α))) *
          (S_g.card : ℝ) * M_f * M_g * (Real.sqrt α) ^ D + ε := by
          dsimp [c, ρ]; ring

end StrongCouplingDobrushin

end YangMills
