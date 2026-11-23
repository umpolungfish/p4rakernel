import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Card
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic

namespace Imscribing.Paraconsistent.Uroboraeus

/-! ## Part 1: The Sixteen_3 Trilattice Structure -/

inductive EpistemicAtom : Type
  | T  -- constructively proven
  | F  -- constructively refuted
  | t  -- non-constructively acceptable
  | f  -- non-constructively rejectable
  deriving DecidableEq, Repr

instance : Fintype EpistemicAtom where
  elems := {.T, .F, .t, .f}
  complete x := by cases x <;> simp

abbrev Sixteen3 := Finset EpistemicAtom

theorem sixteen3_card : Fintype.card Sixteen3 = 16 := by
  decide

def le_i (x y : Sixteen3) : Prop := x ⊆ y

def le_t (x y : Sixteen3) : Prop :=
  (x ∩ {.T, .t}) ⊆ (y ∩ {.T, .t}) ∧ (y ∩ {.F, .f}) ⊆ (x ∩ {.F, .f})

def le_f (x y : Sixteen3) : Prop :=
  (x ∩ {.F, .f}) ⊆ (y ∩ {.F, .f}) ∧ (y ∩ {.T, .t}) ⊆ (x ∩ {.T, .t})

def le_c (x y : Sixteen3) : Prop :=
  (x ∩ {.T, .F}) ⊆ (y ∩ {.T, .F}) ∧ (y ∩ {.t, .f}) ⊆ (x ∩ {.t, .f})

def VoidState : Sixteen3 := ∅
def TrueState : Sixteen3 := {.T}
def FalseState : Sixteen3 := {.F}
def GlutState : Sixteen3 := {.T, .F}
def TotalB : Sixteen3 := Finset.univ

theorem order_independence :
    (∃ x y : Sixteen3, le_i x y ∧ ¬ le_t x y) ∧
    (∃ x y : Sixteen3, le_t x y ∧ ¬ le_i x y) ∧
    (∃ x y : Sixteen3, le_i x y ∧ ¬ le_f x y) ∧
    (∃ x y : Sixteen3, le_t x y ∧ ¬ le_f x y) := by
  refine ⟨⟨∅, {.F}, ?_, ?_⟩, ⟨{.F}, ∅, ?_, ?_⟩, ⟨∅, {.T}, ?_, ?_⟩, ⟨∅, {.T}, ?_, ?_⟩⟩ <;>
    simp only [le_i, le_t, le_f] <;> decide

/-! ## Part 2: Re-entry Operator, Frobenius Closure (μ ∘ δ = id), and Walk W -/

def Inc (x : Sixteen3) : Sixteen3 := x ∪ {.T, .F}

def IncStep (A B : Sixteen3) : Sixteen3 :=
  (A ∩ {.T, .t}) ∪ (B ∩ {.F, .f})

theorem distinction_axiom (x : Sixteen3) : Inc (Inc x) ≠ VoidState := by
  unfold Inc VoidState
  intro h
  have hmem : EpistemicAtom.T ∈ (x ∪ {.T, .F}) ∪ {.T, .F} := by simp
  rw [h] at hmem
  simp at hmem

theorem non_commutative_reentry :
    IncStep TrueState FalseState ≠ IncStep FalseState TrueState := by
  unfold IncStep TrueState FalseState
  decide

theorem reentry_idempotency (x : Sixteen3) : Inc (Inc x) = Inc x := by
  unfold Inc
  ext a; simp [or_comm, or_assoc]

theorem fixed_point_mandate : Inc TotalB = TotalB := by
  unfold Inc TotalB
  ext a; simp

def delta (x : Sixteen3) : Sixteen3 × Sixteen3 × Sixteen3 :=
  (x ∩ {.T}, x ∩ {.F}, x ∩ {.t, .f})

def mu (p : Sixteen3 × Sixteen3 × Sixteen3) : Sixteen3 :=
  p.1 ∪ p.2.1 ∪ p.2.2

theorem frobenius_closure (x : Sixteen3) : mu (delta x) = x := by
  unfold mu delta
  ext a
  cases a <;> simp

inductive B4PlusVoid : Type
  | Void | N | T | F | B
  deriving DecidableEq

def totalityProjection (x : Sixteen3) : B4PlusVoid :=
  if x = ∅ then .Void
  else if x = TotalB then .B
  else if .T ∈ x ∧ .F ∈ x then .B
  else if .T ∈ x then .T
  else if .F ∈ x then .F
  else .N

theorem totality_surjective : Function.Surjective totalityProjection := by
  intro y
  cases y with
  | Void => exact ⟨∅, by decide⟩
  | N    => exact ⟨{.t}, by decide⟩
  | T    => exact ⟨{.T}, by decide⟩
  | F    => exact ⟨{.F}, by decide⟩
  | B    => exact ⟨TotalB, by decide⟩

theorem totality_not_injective : ¬ Function.Injective totalityProjection := by
  intro hinj
  have h : totalityProjection {.T, .F} = totalityProjection TotalB := by decide
  have heq : ({.T, .F} : Sixteen3) = TotalB := hinj h
  revert heq; decide

def walkStep (x : Sixteen3) : Sixteen3 :=
  if .T ∉ x then insert .T x
  else if .F ∉ x then insert .F x
  else if .t ∉ x then insert .t x
  else if .f ∉ x then insert .f x
  else x

theorem walkStep_monotone {x : Sixteen3} (hx : x ≠ TotalB) :
    le_i x (walkStep x) ∧ x ≠ walkStep x := by
  unfold walkStep le_i
  by_cases hT : .T ∉ x
  · simp [hT]; intro h; exact hT (h ▸ Finset.mem_insert_self _ _)
  · by_cases hF : .F ∉ x
    · simp [hT, hF]; intro h; exact hF (h ▸ Finset.mem_insert_self _ _)
    · by_cases ht : .t ∉ x
      · simp [hT, hF, ht]; intro h; exact ht (h ▸ Finset.mem_insert_self _ _)
      · by_cases hf : .f ∉ x
        · simp [hT, hF, ht, hf]; intro h; exact hf (h ▸ Finset.mem_insert_self _ _)
        · exfalso
          apply hx
          ext a; cases a <;> simp_all [TotalB]

theorem walkStep_fixed_at_totalB : walkStep TotalB = TotalB := by
  unfold walkStep TotalB; decide

/-! ## Part 3: Operational Tuple M = ⟨S, ≤_t, ≤_f, ≤_i, Inc, μ, δ, W⟩ -/

structure UroboraeusModel (S : Type*) where
  le_i : S → S → Prop
  le_t : S → S → Prop
  le_f : S → S → Prop
  Inc  : S → S
  mu   : S × S × S → S
  delta : S → S × S × S
  W    : S → S
  Total : S
  Void  : S
  distinction   : ∀ x, Inc (Inc x) ≠ Void
  reentry_idem  : ∀ x, Inc (Inc x) = Inc x
  fixed_point   : Inc Total = Total
  frob_id       : ∀ x, mu (delta x) = x
  walk_mono     : ∀ x, x ≠ Total → le_i x (W x) ∧ x ≠ W x
  walk_terminal : W Total = Total

def sixteen3Model : UroboraeusModel Sixteen3 where
  le_i := le_i
  le_t := le_t
  le_f := le_f
  Inc := Inc
  mu := mu
  delta := delta
  W := walkStep
  Total := TotalB
  Void := VoidState
  distinction := distinction_axiom
  reentry_idem := reentry_idempotency
  fixed_point := fixed_point_mandate
  frob_id := frobenius_closure
  walk_mono := fun _ hx => walkStep_monotone hx
  walk_terminal := walkStep_fixed_at_totalB

/-! ## Part 4: Static Pinning Obstruction vs. Process Holding at d = 2048 -/

noncomputable def omega_d (d : ℕ) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I / (d : ℂ))

theorem evalf_character_obstruction (n : ℕ) (hn : 1 < n) :
    ¬ ∃ r : ℝ, omega_d (2^n) = (r : ℂ) := by
  rintro ⟨r, hr⟩
  have him : (omega_d (2^n)).im = ((r : ℂ)).im := congrArg Complex.im hr
  simp only [Complex.ofReal_im] at him
  have h4 : 4 ≤ 2^n := by
    calc 4 = 2^2 := by norm_num
      _ ≤ 2^n := Nat.pow_le_pow_right (by decide) hn
  have hd_gt : (2 : ℝ) < ((2^n : ℕ) : ℝ) := by
    exact_mod_cast (by linarith : 2 < 2^n)
  have hd_pos : (0 : ℝ) < ((2^n : ℕ) : ℝ) := by positivity
  have harg_pos : 0 < 2 * Real.pi / ((2^n : ℕ) : ℝ) := by positivity
  have harg_lt : 2 * Real.pi / ((2^n : ℕ) : ℝ) < Real.pi := by
    rw [div_lt_iff₀ hd_pos]
    nlinarith [Real.pi_pos]
  have him_eq : (omega_d (2^n)).im = Real.sin (2 * Real.pi / ((2^n : ℕ) : ℝ)) := by
    unfold omega_d
    set θ : ℝ := 2 * Real.pi / ((2^n : ℕ) : ℝ)
    have harg : 2 * Real.pi * Complex.I / ((2^n : ℕ) : ℂ) = (θ : ℂ) * Complex.I := by
      dsimp [θ]; push_cast; ring
    rw [harg, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
    simp only [Complex.add_im, Complex.ofReal_im, Complex.ofReal_re, Complex.mul_im,
      Complex.I_im, Complex.I_re]
    ring
  rw [him_eq] at him
  have hsin_pos : 0 < Real.sin (2 * Real.pi / ((2^n : ℕ) : ℝ)) :=
    Real.sin_pos_of_pos_of_lt_pi harg_pos harg_lt
  linarith

def StaticPinningHypothesis (n : ℕ) : Prop :=
  ∃ r : ℝ, omega_d (2^n) = (r : ℂ)

theorem static_pinning_collapse (n : ℕ) (hn : 1 < n) :
    StaticPinningHypothesis n → False :=
  evalf_character_obstruction n hn

structure ProcessHolding2048 (StarkExists : Prop) where
  cl8nk_roundtrip : ∀ x : Sixteen3, sixteen3Model.mu (sixteen3Model.delta x) = x
  cl8nk_fixed_pt  : sixteen3Model.Inc TotalB = TotalB
  cl9nk_obstruct  : ¬ StaticPinningHypothesis 11
  dialetheic_node : (StarkExists → StarkExists) ∧ ¬ StaticPinningHypothesis 11

theorem process_holding_2048_exists (StarkExists : Prop) :
    Nonempty (ProcessHolding2048 StarkExists) :=
  ⟨{
    cl8nk_roundtrip := sixteen3Model.frob_id
    cl8nk_fixed_pt  := sixteen3Model.fixed_point
    cl9nk_obstruct  := static_pinning_collapse 11 (by decide)
    dialetheic_node := ⟨id, static_pinning_collapse 11 (by decide)⟩
  }⟩

end Imscribing.Paraconsistent.Uroboraeus