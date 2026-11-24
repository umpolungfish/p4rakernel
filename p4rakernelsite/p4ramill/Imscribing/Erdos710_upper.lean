import Mathlib

open Finset Filter Asymptotics

namespace Erdos710

def HasIn (n lo hi : ℕ) : Prop :=
  ∃ a : ℕ → ℕ, Set.InjOn a (Icc 1 n : Finset ℕ) ∧
    ∀ k ∈ Icc 1 n, lo < a k ∧ a k < hi ∧ k ∣ a k

noncomputable def f (n : ℕ) : ℕ := sInf {L | HasIn n n (n + L)}

noncomputable def C : ℝ := 2 / Real.sqrt (Real.exp 1)

noncomputable def g (n : ℕ) : ℝ :=
  (n : ℝ) * Real.sqrt (Real.log n / Real.log (Real.log n))

theorem C_pos : 0 < C := by
  unfold C
  positivity

theorem g_nonneg (n : ℕ) : 0 ≤ g n := by
  unfold g
  positivity

/-! ## Hall reformulation -/

/-- Neighbours of `k` in the divisibility graph on the window `(m, m+L)`. -/
def target (n m L : ℕ) (k : Icc 1 n) : Finset ℕ :=
  (Ioo m (m + L)).filter (fun h => k.1 ∣ h)

theorem hasIn_iff_hall (n m L : ℕ) :
    HasIn n m (m + L) ↔
      ∀ s : Finset (Icc 1 n), s.card ≤ (s.biUnion (target n m L)).card := by
  rw [Finset.all_card_le_biUnion_card_iff_exists_injective (target n m L)]
  constructor
  · rintro ⟨a, ha, h⟩
    refine ⟨fun x => a x.1, ?_, ?_⟩
    · intro x y hxy
      exact Subtype.ext (ha x.2 y.2 hxy)
    · intro x
      obtain ⟨h1, h2, h3⟩ := h x.1 x.2
      simp only [target, mem_filter, mem_Ioo]
      exact ⟨⟨h1, h2⟩, h3⟩
  · rintro ⟨g', hg, h⟩
    refine ⟨fun k => if hk : k ∈ Icc 1 n then g' ⟨k, hk⟩ else 0, ?_, ?_⟩
    · intro x hx y hy hxy
      have hx' : x ∈ Icc 1 n := hx
      have hy' : y ∈ Icc 1 n := hy
      simp only [dif_pos hx', dif_pos hy'] at hxy
      exact congrArg Subtype.val (hg hxy)
    · intro k hk
      have := h ⟨k, hk⟩
      simp only [target, mem_filter, mem_Ioo] at this
      dsimp only
      rw [dif_pos hk]
      exact ⟨this.1.1, this.1.2, this.2⟩

/-- Hall's condition for the window `(n, n + L)`. -/
def HallAt (n L : ℕ) : Prop :=
  ∀ s : Finset (Icc 1 n), s.card ≤ (s.biUnion (target n n L)).card

theorem f_le_of_hall {n L : ℕ} (h : HallAt n L) : f n ≤ L :=
  Nat.sInf_le ((hasIn_iff_hall n n L).mpr h)

/-! ## The scale `g` dominates `n` -/

theorem g_ge {n : ℕ} (hn : 16 ≤ n) : (n : ℝ) ≤ g n := by
  have h16 : (16 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hlog16 : 1 < Real.log 16 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num)]
    have := Real.exp_one_lt_d9
    linarith
  have hx : 1 < Real.log n :=
    lt_of_lt_of_le hlog16 (Real.log_le_log (by norm_num) h16)
  have hpos : 0 < Real.log (Real.log n) := Real.log_pos hx
  have hle : Real.log (Real.log n) ≤ Real.log n := by
    have := Real.log_le_sub_one_of_pos (by linarith : 0 < Real.log n)
    linarith
  have hratio : 1 ≤ Real.log n / Real.log (Real.log n) :=
    (one_le_div hpos).mpr hle
  have hs : 1 ≤ Real.sqrt (Real.log n / Real.log (Real.log n)) := by
    rw [show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
    exact Real.sqrt_le_sqrt hratio
  unfold g
  nlinarith

/-! ## Reduction of the upper bound to a global Hall condition -/

def LowerBound : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop, (C - ε) * g n ≤ (f n : ℝ)

def UpperBound : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop, (f n : ℝ) ≤ (C + ε) * g n

/-- THE OPEN STATEMENT. For every `ε > 0` and all large `n`, Hall's condition
holds for the divisibility graph on `{1..n}` versus `(n, n + ⌈(C+ε) g n⌉)`. -/
def HallGlobal : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop, HallAt n ⌈(C + ε) * g n⌉₊

theorem upper_of_hall (H : HallGlobal) : UpperBound := by
  intro ε hε
  have hε2 : 0 < ε / 2 := by linarith
  filter_upwards [H (ε / 2) hε2, eventually_ge_atTop (max 16 ⌈2 / ε⌉₊)]
    with n hH hN
  have h16 : 16 ≤ n := le_trans (le_max_left _ _) hN
  have hceil : ⌈2 / ε⌉₊ ≤ n := le_trans (le_max_right _ _) hN
  have hf : (f n : ℝ) ≤ (⌈(C + ε / 2) * g n⌉₊ : ℝ) := by
    exact_mod_cast f_le_of_hall hH
  have hg0 := g_nonneg n
  have hnonneg : 0 ≤ (C + ε / 2) * g n :=
    mul_nonneg (by linarith [C_pos]) hg0
  have hlt : (⌈(C + ε / 2) * g n⌉₊ : ℝ) < (C + ε / 2) * g n + 1 :=
    Nat.ceil_lt_add_one hnonneg
  have h2n : 2 / ε ≤ (n : ℝ) := le_trans (Nat.le_ceil _) (by exact_mod_cast hceil)
  have h1 : 1 ≤ (ε / 2) * (n : ℝ) := by
    have : 2 / ε * (ε / 2) = 1 := by field_simp
    nlinarith [mul_le_mul_of_nonneg_right h2n hε2.le]
  have hgn := g_ge h16
  have h3 : 1 ≤ (ε / 2) * g n := le_trans h1 (mul_le_mul_of_nonneg_left hgn hε2.le)
  nlinarith

/-! ## Final assembly -/

theorem asymptotic (lower : LowerBound) (upper : UpperBound) :
    IsEquivalent atTop (fun n : ℕ => (f n : ℝ)) (fun n : ℕ => C * g n) := by
  rw [IsEquivalent, isLittleO_iff]
  intro δ hδ
  have hε : 0 < δ * C := mul_pos hδ C_pos
  filter_upwards [lower (δ * C) hε, upper (δ * C) hε] with n h1 h2
  simp only [Pi.sub_apply, Real.norm_eq_abs]
  have hg : 0 ≤ C * g n := mul_nonneg C_pos.le (g_nonneg n)
  rw [abs_of_nonneg hg, abs_le]
  constructor <;> nlinarith [h1, h2, g_nonneg n, C_pos]

theorem erdos_710 (lower : LowerBound) (hall : HallGlobal) :
    IsEquivalent atTop (fun n : ℕ => (f n : ℝ)) (fun n : ℕ => C * g n) :=
  asymptotic lower (upper_of_hall hall)

end Erdos710

#print axioms Erdos710.erdos_710
