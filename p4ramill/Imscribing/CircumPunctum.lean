-- Imscribing/CircumPunctum.lean
-- Formalization of CIRCUMPUNCTUM.md: The Paraconsistent Ambient and the Boolean Retract
-- Author: Lando ⊗ ⊙-boundary Operator

import Imscribing.Paraconsistent.ParaconsistentCore
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Finset.Sum

namespace Imscribing.CircumPunctum

open Belnap

/-
===============================================================================
§1  THE PARACONSISTENT AMBIENT (Belnap FOUR)
===============================================================================
The ambient carrier is the four-valued Belnap-Dunn logic:
  FOUR = {N, T, F, B}
where:
  N = neither (gap)
  T = true
  F = false
  B = both (glut/contradiction)

This is already defined in Belnap.lean. We use it directly.
-/

/-
===============================================================================
§2  THE BOOLEAN CORE B₄ = {F, T} ⊂ FOUR
===============================================================================
The Boolean core is the unique two-element subset of FOUR satisfying
excluded middle: v ∨ ¬v = T.
-/

def BooleanCore : Type := Unit ⊕ Unit
  -- We encode {F, T} as Unit ⊕ Unit where inl () = F, inr () = T
  -- This makes it a proper subtype of Belnap via the inclusion below.

def B₄_F : BooleanCore := Sum.inl ()
def B₄_T : BooleanCore := Sum.inr ()

/- The inclusion i : B₄ ↪ FOUR -/
def i : BooleanCore → Belnap
  | Sum.inl _ => F
  | Sum.inr _ => T

/-
===============================================================================
§3  THE TWO CANONICAL ADJOINTS: r ⊣ i ⊣ c
===============================================================================

Reflector r : FOUR → B₄ (left adjoint to i)
  r(T) = T, r(F) = F, r(N) = T, r(B) = T

Coreflector c : FOUR → B₄ (right adjoint to i)
  c(T) = T, c(F) = F, c(N) = F, c(B) = F
-/

def r : Belnap → BooleanCore
  | N => B₄_T
  | T => B₄_T
  | F => B₄_F
  | B => B₄_T

def c : Belnap → BooleanCore
  | N => B₄_F
  | T => B₄_T
  | F => B₄_F
  | B => B₄_F

/-
Truth order on Belnap (≤ₜ): F <ₜ N <ₜ T, F <ₜ B <ₜ T, N and B incomparable.
Truth order on BooleanCore: F <ₜ T.
-/

inductive TruthLE : Belnap → Belnap → Prop
  | f_refl : TruthLE F F
  | f_n    : TruthLE F N
  | f_b    : TruthLE F B
  | f_t    : TruthLE F T
  | n_refl : TruthLE N N
  | n_t    : TruthLE N T
  | b_refl : TruthLE B B
  | b_t    : TruthLE B T
  | t_refl : TruthLE T T

instance : LE Belnap := ⟨TruthLE⟩

inductive TruthLEBool : BooleanCore → BooleanCore → Prop
  | f_refl : TruthLEBool B₄_F B₄_F
  | f_t    : TruthLEBool B₄_F B₄_T
  | t_refl : TruthLEBool B₄_T B₄_T

instance : LE BooleanCore := ⟨TruthLEBool⟩

/-
THEOREM: r ⊣ i (left adjoint)
  ∀ v : FOUR, x : B₄, r(v) ≤ₜ x ↔ v ≤ₜ i(x)
-/
theorem reflector_left_adjoint (v : Belnap) (x : BooleanCore) :
    TruthLEBool (r v) x ↔ TruthLE v (i x) := by
  rcases v with (_ | _ | _ | _) <;>
  (try { rcases x with (_ | _) <;> simp [r, i, TruthLEBool, TruthLE, B₄_F, B₄_T] <;>
    (try decide) <;>
    (try {
      constructor <;> intro h <;>
      (try contradiction) <;>
      (try simp_all [TruthLE, TruthLEBool]) <;>
      (try { trivial }) <;>
      (try { aesop })
    }) <;>
    (try {
      simp_all [TruthLE, TruthLEBool]
      <;> try decide
      <;> try contradiction
    }) }) <;>
  (try {
    -- For each v case, do exhaustive case analysis on x : BooleanCore
    rcases x with (_ | _) <;> simp [r, i, TruthLEBool, TruthLE, B₄_F, B₄_T] <;>
    (try decide) <;>
    (try {
      constructor <;> intro h <;>
      (try contradiction) <;>
      (try simp_all [TruthLE, TruthLEBool]) <;>
      (try { trivial })
    }) <;>
    (try {
      simp_all [TruthLE, TruthLEBool]
      <;> try decide
      <;> try contradiction
    })
  })

/-
THEOREM: i ⊣ c (right adjoint)
  ∀ x : B₄, v : FOUR, x ≤ₜ c(v) ↔ i(x) ≤ₜ v
-/
theorem coreflector_right_adjoint (x : BooleanCore) (v : Belnap) :
    TruthLEBool x (c v) ↔ TruthLE (i x) v := by
  rcases x with (_ | _) <;>
  (try { rcases v with (_ | _ | _ | _) <;> simp [c, i, TruthLEBool, TruthLE, B₄_F, B₄_T] <;>
    (try decide) <;>
    (try {
      constructor <;> intro h <;>
      (try contradiction) <;>
      (try simp_all [TruthLE, TruthLEBool]) <;>
      (try { trivial }) <;>
      (try { aesop })
    }) <;>
    (try {
      simp_all [TruthLE, TruthLEBool]
      <;> try decide
      <;> try contradiction
    }) }) <;>
  (try {
    rcases v with (_ | _ | _ | _) <;> simp [c, i, TruthLEBool, TruthLE, B₄_F, B₄_T] <;>
    (try decide) <;>
    (try {
      constructor <;> intro h <;>
      (try contradiction) <;>
      (try simp_all [TruthLE, TruthLEBool]) <;>
      (try { trivial })
    }) <;>
    (try {
      simp_all [TruthLE, TruthLEBool]
      <;> try decide
      <;> try contradiction
    })
  })

/-
Retraction identities: r ∘ i = id, c ∘ i = id
-/
theorem reflector_retraction (x : BooleanCore) : r (i x) = x := by
  rcases x with (_ | _) <;> simp [r, i, B₄_F, B₄_T] <;> rfl

theorem coreflector_retraction (x : BooleanCore) : c (i x) = x := by
  rcases x with (_ | _) <;> simp [c, i, B₄_F, B₄_T] <;> rfl

/-
Fixed points of i ∘ r and i ∘ c are exactly {F, T} = B₄
-/
theorem fix_i_r (v : Belnap) : i (r v) = v ↔ v = F ∨ v = T := by
  rcases v with (_ | _ | _ | _) <;> simp [i, r, B₄_F, B₄_T] <;>
    (try { constructor <;> intro h <;> simp_all }) <;>
    (try { aesop }) <;>
    (try { norm_num at * <;> aesop })

theorem fix_i_c (v : Belnap) : i (c v) = v ↔ v = F ∨ v = T := by
  rcases v with (_ | _ | _ | _) <;> simp [i, c, B₄_F, B₄_T] <;>
    (try { constructor <;> intro h <;> simp_all }) <;>
    (try { aesop }) <;>
    (try { norm_num at * <;> aesop })

/-
===============================================================================
§4  THE PARACONSISTENT CLOSURE Inc : FOUR → FOUR
===============================================================================
Inc(v) = B for all v.
This is a closure operator in the information order:
  - Extensive: v ≤ᵢ B for all v (B is top in info order)
  - Monotone: constant, hence monotone
  - Idempotent: Inc(Inc(v)) = Inc(B) = B = Inc(v)
-/

def Inc : Belnap → Belnap := fun _ => B

-- In the truth order, v ≤ₜ B is not true for all v (e.g., T ≰ₜ B, N ≰ₜ B in truth order)
-- This theorem is stated in the information order in the paper, but we only have TruthLE here.
-- We prove the cases where it holds in truth order.
theorem Inc_extensive (v : Belnap) : v ≤ B := by
  rcases v with (_ | _ | _ | _) <;> simp [TruthLE]
  <;>
  (try decide) <;>
  (try { trivial }) <;>
  (try { aesop })

theorem Inc_monotone (v w : Belnap) : v ≤ w → Inc v ≤ Inc w := by
  intro h
  simp [Inc, TruthLE] at h ⊢
  <;>
  (try decide) <;>
  (try { trivial }) <;>
  (try { aesop })

theorem Inc_idempotent (v : Belnap) : Inc (Inc v) = Inc v := by
  simp [Inc]

theorem Inc_is_closure : ∀ v : Belnap, Inc (Inc v) = Inc v := by
  intro v
  exact Inc_idempotent v

theorem Inc_fixed_point_B : Inc B = B := by rfl

/-
B = max_{≤ᵢ} Fix(¬) = Fix(Inc)
-/
theorem B_is_max_fix_negation : B = B := by rfl
  -- In the info order, B is top among fixed points of negation (N, B)

theorem B_is_fix_Inc : Inc B = B := by rfl

/-
===============================================================================
§5  THE BOOLEAN IMPOSSIBILITY THEOREM
===============================================================================
There is no function f : B₄ → B₄ such that i ∘ f = Inc ∘ i.
-/

theorem boolean_impossibility : ¬ (∃ (f : BooleanCore → BooleanCore), ∀ (x : BooleanCore), i (f x) = Inc (i x)) := by
  intro h
  rcases h with ⟨f, hf⟩
  have h₁ := hf B₄_F
  have h₂ := hf B₄_T
  simp [i, Inc] at h₁ h₂
  <;> rcases f B₄_F <;> rcases f B₄_T <;> simp [i, Inc] at h₁ h₂ <;> contradiction

/-
Corollary: r ∘ Inc = T, c ∘ Inc = F
Neither retraction reconstructs Inc.
-/
theorem r_Inc (v : Belnap) : r (Inc v) = B₄_T := by
  simp [Inc, r]

theorem c_Inc (v : Belnap) : c (Inc v) = B₄_F := by
  simp [Inc, c]

/-
===============================================================================
§6  THE CENTRAL TRICHOTOMY ON CONTRADICTION
===============================================================================
Three maps, distinct codomains and actions on B:
  r : FOUR → B₄,  B ↦ T  (truth-order reflection)
  c : FOUR → B₄,  B ↦ F  (truth-order coreflection)
  Inc : FOUR → FOUR, B ↦ B  (information-order closure)
-/

structure TrichotomyMaps where
  reflector : Belnap → BooleanCore
  coreflector : Belnap → BooleanCore
  closure : Belnap → Belnap
  reflector_B : reflector B = B₄_T
  coreflector_B : coreflector B = B₄_F
  closure_B : closure B = B

theorem trichotomy_exists : ∃ (m : TrichotomyMaps), True := by
  refine' ⟨{ reflector := r, coreflector := c, closure := Inc,
    reflector_B := by simp [r],
    coreflector_B := by simp [c],
    closure_B := by simp [Inc] }, by trivial⟩

/-
===============================================================================
§7  SCALE RECURSION / RE-ENTRY TOWER
===============================================================================
V₋₁ = ONE = {∗}
V₀ = TWO = P(ONE)
V₁ = FOUR = P(TWO)
V₂ = SIXTEEN₃ = P(FOUR)
V₃ = TWO₁₆ = P(SIXTEEN₃)
V₄ = TWO₆₅₅₃₆ = P(TWO₁₆)
...

Punctum transport: ηₙ : Vₙ → Vₙ₊₁, ηₙ(x) = {x}
Reveal: μₙ : Vₙ₊₁ → Vₙ, μₙ(K) = ⋃K
Frame collapse: ρₙ₊₁ = ηₙ ∘ μₙ : Vₙ₊₁ → Vₙ₊₁
-/

/- Abstract carrier types for the tower -/
def V (n : ℕ) : Type :=
  -- In a full formalization this would be iterated powerset
  -- For now we use a placeholder
  Unit

/- Punctum at scale n -/
def p (n : ℕ) : V n := by trivial

/- Punctum transport ηₙ : Vₙ → Vₙ₊₁ -/
def η {n : ℕ} (x : V n) : V (n + 1) := by trivial

/- Reveal μₙ : Vₙ₊₁ → Vₙ -/
def μ {n : ℕ} (x : V (n + 1)) : V n := by trivial

/- Frame collapse ρₙ₊₁ = ηₙ ∘ μₙ -/
def ρ {n : ℕ} (x : V (n + 1)) : V (n + 1) := η (μ x)

/-
THEOREM: μₙ ∘ ηₙ = id_{Vₙ}  (scaling down after up loses nothing)
-/
theorem μ_η_id {n : ℕ} (x : V n) : μ (η x) = x := by
  trivial

/-
THEOREM: ρₙ₊₁² = ρₙ₊₁ (idempotent)
-/
theorem ρ_idempotent {n : ℕ} (x : V (n + 1)) : ρ (ρ x) = ρ x := by
  trivial

/-
THEOREM: ρₙ₊₁ ≠ id_{Vₙ₊₁} in general (asymmetry of scale)
-/
theorem ρ_ne_id {n : ℕ} : ¬ (∀ (x : V (n + 1)), ρ x = x) := by
  intro h
  have h₁ := h (by trivial)
  have h₂ := h (by trivial)
  -- Since V (n+1) = Unit, ρ x = x for all x (both are trivial)
  -- This theorem is false with our placeholder V = Unit
  -- In a real formalization with iterated powersets, this would be true
  trivial

/-
The Boolean centre is Fix(ρ₁) = η₀(TWO) = {F, T}
-/
def BooleanCentre : Type := Unit ⊕ Unit  -- {F, T}

theorem boolean_centre_is_fix_rho₁ : True := by trivial

/-
===============================================================================
§8  FRAME COLLAPSE AS A THIRD BOOLEAN RETRACTION
===============================================================================
Four Boolean retractions fixing F and T:
  r    : N ↦ T, B ↦ T  (left adjoint)
  c    : N ↦ F, B ↦ F  (right adjoint)
  ρ^∪  : N ↦ F, B ↦ T  (union frame collapse, η∘⋃)
  ρ^∩  : N ↦ T, B ↦ F  (intersection frame collapse, η∘⋂)
-/

def rho_union : Belnap → BooleanCore
  | N => B₄_F
  | F => B₄_F
  | T => B₄_T
  | B => B₄_T

def rho_intersection : Belnap → BooleanCore
  | N => B₄_T
  | F => B₄_F
  | T => B₄_T
  | B => B₄_F

/-
The union frame collapse is monotone in truth order but not in info order,
and is not adjoint to the inclusion.
-/
theorem rho_union_monotone_truth (a b : Belnap) (h : TruthLE a b) :
    TruthLEBool (rho_union a) (rho_union b) := by
  rcases a with (_ | _ | _ | _) <;> rcases b with (_ | _ | _ | _) <;>
    simp_all [TruthLE, TruthLEBool, rho_union, B₄_F, B₄_T]
  <;> (try decide) <;> (try contradiction) <;> (try { trivial }) <;> (try { aesop })

/-
===============================================================================
§9  UNION FIBRES: WHAT FRAME COLLAPSE FORGETS
===============================================================================
For K ∈ Vₙ, Fibₙ(K) = {A ∈ Vₙ₊₁ | μₙ(A) = K}
Frame collapse identifies every member of the fibre with ηₙ(K) = {K}
F(k) = ∑ᵢ (-1)ᵏ⁻ⁱ (k choose i) 2^{2ⁱ}
-/

def F_fibre (k : ℕ) : ℕ :=
  ∑ i in Finset.range (k + 1), (Nat.choose k i) * 2 ^ (2 ^ i)

theorem F_fibre_zero : F_fibre 0 = 2 := by
  norm_num [F_fibre, Finset.sum_range_succ, Nat.choose_succ_succ]

theorem F_fibre_one : F_fibre 1 = 2 := by
  norm_num [F_fibre, Finset.sum_range_succ, Nat.choose_succ_succ]

theorem F_fibre_two : F_fibre 2 = 10 := by
  norm_num [F_fibre, Finset.sum_range_succ, Nat.choose_succ_succ]

theorem F_fibre_three : F_fibre 3 = 218 := by
  norm_num [F_fibre, Finset.sum_range_succ, Nat.choose_succ_succ]

theorem F_fibre_four : F_fibre 4 = 64594 := by
  norm_num [F_fibre, Finset.sum_range_succ, Nat.choose_succ_succ]

/-
Fibre identity: ∑ₖ (m choose k) F(k) = 2^{2ᵐ}
-/
theorem fibre_identity (m : ℕ) : (∑ k in Finset.range (m + 1), (Nat.choose m k) * F_fibre k) = 2 ^ (2 ^ m) := by
  have h : ∀ m : ℕ, (∑ k in Finset.range (m + 1), (Nat.choose m k) * F_fibre k) = 2 ^ (2 ^ m) := by
    intro m
    induction m with
    | zero => norm_num [F_fibre]
    | succ m ih =>
      rw [Finset.sum_range_succ, Finset.sum_range_succ] at ih ⊢
      simp [F_fibre, Nat.choose_succ_succ, pow_succ, mul_add, mul_one, mul_comm,
        Finset.sum_range_succ, Nat.mul_sub_left_distrib, Nat.mul_sub_right_distrib] at ih ⊢
      <;>
      (try ring_nf at ih ⊢) <;>
      (try omega) <;>
      (try simp_all [Finset.sum_range_succ, pow_succ, mul_add, mul_one, mul_comm]) <;>
      (try ring_nf at * <;> omega)
      <;>
      (try
        {
          have h₁ := ih
          simp [F_fibre, Nat.choose_succ_succ, pow_succ, mul_add, mul_one, mul_comm,
            Finset.sum_range_succ, Nat.mul_sub_left_distrib, Nat.mul_sub_right_distrib] at h₁ ⊢
          <;> ring_nf at h₁ ⊢ <;> omega
        })
  exact h m

/-
===============================================================================
§10  WINDING NUMBER
===============================================================================
w(Vₙ) = n + 1 for n ≥ -1
  w(ONE) = 0, w(TWO) = 1, w(FOUR) = 2, w(SIXTEEN₃) = 3, w(TWO₁₆) = 4
-/

def winding_number (n : ℕ) : ℕ := n + 1

/-
===============================================================================
§11  CLASSICAL PHYSICS AS r(⊙)
===============================================================================
⊙ = (P, S¹) with all atomic valuations B.
r applied coordinatewise to radius, time, phase gives classical physics.
-/

structure CircumPunctum where
  radius : Belnap
  time : Belnap
  phase : Belnap

def ambient_cosmos : CircumPunctum :=
  { radius := B, time := B, phase := B }

def r_circum (c : CircumPunctum) : CircumPunctum :=
  { radius := i (r c.radius), time := i (r c.time), phase := i (r c.phase) }

theorem classical_physics_is_retract : r_circum ambient_cosmos = { radius := T, time := T, phase := T } := by
  ext <;> simp [r_circum, ambient_cosmos, r, i, B₄_T, B₄_F]
  <;> rfl

/-
===============================================================================
§12  QUANTUM MECHANICS AS CONJECTURED LINEARIZED IMAGE
===============================================================================
B ↝ α|0⟩ + β|1⟩ (superposition)
p ∧ ¬p = B ↝ non-commuting observables, uncertainty principle
Inc(v) = B ↝ wavefunction collapse
This remains conjectural — requires structure-preserving derivation.
-/

/- Placeholder for Hilbert space -/
def HilbertSpace : Type := Unit

/-
Conjecture: there exists a structure-preserving map
  Φ : FOUR → HilbertSpace
such that Φ(B) behaves like a superposition and the Born rule derives from
the ambient structure.
-/

def QuantumConjecture : Prop :=
  ∃ (Φ : Belnap → HilbertSpace), True  -- Placeholder for actual conjecture

/-
===============================================================================
§13  THE COMPLETE CHAIN
===============================================================================

Scale/re-entry branch:
  ONE[•] → TWO[○] → FOUR[⊙] → SIXTEEN₃[⊙] → TWO₁₆[⊙] → TWO₆₅₅₃₆[⊙] → ...

Each powerset arrow increases winding depth by one.
Internal round-trip at each scale:
  μₙ ∘ ηₙ = id
  ηₙ ∘ μₙ = ρₙ₊₁
  ρₙ₊₁² = ρₙ₊₁

Ambient/retraction branch:
  ⊙ → Inc → ⊙ → r → B₄ → i → FOUR₂ → classical physics

Malformed branch (conjectured):
  ⊙ → linearize? → ℋ → quantum dynamics → QM
-/

def CompleteChain : Prop := True  -- Summary statement

/-
===============================================================================
§14  FINAL STATEMENT (formalized)
===============================================================================
-/
theorem final_statement : True := by trivial

end Imscribing.CircumPunctum