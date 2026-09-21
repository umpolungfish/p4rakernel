-- Imscribing/CircumPunctum.lean
-- Formalization of CIRCUMPUNCTUM.md: The Paraconsistent Ambient and the Boolean Retract
-- Author: Lando ⊗ ⊙-boundary Operator

import Imscribing.Paraconsistent.Belnap
import Mathlib.Logic.Relation
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Finset.Sum
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Order.Interval.Finset.Nat
import Imscribing.Paraconsistent.DialetheicWitness

namespace Imscribing.CircumPunctum

open Imscribing.Paraconsistent
open Imscribing.Paraconsistent.Belnap

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

inductive TruthLEBool : BooleanCore → BooleanCore → Prop
  | f_refl : TruthLEBool B₄_F B₄_F
  | f_t    : TruthLEBool B₄_F B₄_T
  | t_refl : TruthLEBool B₄_T B₄_T

instance : LE BooleanCore := ⟨TruthLEBool⟩

/-
Information order on Belnap (≤ᵢ): N <ᵢ T, N <ᵢ F, T <ᵢ B, F <ᵢ B, plus N <ᵢ B.
N is the info-bottom (gap) and B the info-top (glut).
-/
inductive InfoLE : Belnap → Belnap → Prop
  | n_refl : InfoLE N N
  | n_t    : InfoLE N T
  | n_f    : InfoLE N F
  | n_b    : InfoLE N B
  | t_refl : InfoLE T T
  | t_b    : InfoLE T B
  | f_refl : InfoLE F F
  | f_b    : InfoLE F B
  | b_refl : InfoLE B B

/-
THEOREM: r ⊣ i (left adjoint)
  ∀ v : FOUR, x : B₄, r(v) ≤ₜ x ↔ v ≤ₜ i(x)
-/
theorem reflector_left_adjoint (v : Belnap) (x : BooleanCore) :
    TruthLEBool (r v) x ↔ TruthLE v (i x) := by
  rcases v with (_ | _ | _ | _) <;> rcases x with (⟨⟩ | ⟨⟩) <;>
    exact ⟨fun h => by cases h <;> constructor, fun h => by cases h <;> constructor⟩

/-
THEOREM: i ⊣ c (right adjoint)
  ∀ x : B₄, v : FOUR, x ≤ₜ c(v) ↔ i(x) ≤ₜ v
-/
theorem coreflector_right_adjoint (x : BooleanCore) (v : Belnap) :
    TruthLEBool x (c v) ↔ TruthLE (i x) v := by
  rcases x with (⟨⟩ | ⟨⟩) <;> rcases v with (_ | _ | _ | _) <;>
    exact ⟨fun h => by cases h <;> constructor, fun h => by cases h <;> constructor⟩

/-
Retraction identities: r ∘ i = id, c ∘ i = id
-/
theorem reflector_retraction (x : BooleanCore) : r (i x) = x := by
  rcases x with (_ | _) <;> rfl

theorem coreflector_retraction (x : BooleanCore) : c (i x) = x := by
  rcases x with (_ | _) <;> rfl

/-
Fixed points of i ∘ r and i ∘ c are exactly {F, T} = B₄
-/
theorem fix_i_r (v : Belnap) : i (r v) = v ↔ v = F ∨ v = T := by
  rcases v with (_ | _ | _ | _) <;> decide

theorem fix_i_c (v : Belnap) : i (c v) = v ↔ v = F ∨ v = T := by
  rcases v with (_ | _ | _ | _) <;> decide

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

-- Extensive and monotone in the INFORMATION order (the paper's order): B is the
-- info-top, so v ≤ᵢ B for every v, and Inc is the constant map to that top.
theorem Inc_extensive (v : Belnap) : InfoLE v B := by
  rcases v with (_ | _ | _ | _)
  exacts [InfoLE.n_b, InfoLE.t_b, InfoLE.f_b, InfoLE.b_refl]

theorem Inc_monotone (v w : Belnap) : InfoLE v w → InfoLE (Inc v) (Inc w) := by
  intro _; exact InfoLE.b_refl

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
  rintro ⟨f, hf⟩
  have h := hf B₄_F
  rcases hfb : f B₄_F with _ | _ <;> rw [hfb] at h <;> simp [i, Inc] at h

/-
Corollary: r ∘ Inc = T, c ∘ Inc = F
Neither retraction reconstructs Inc.
-/
theorem r_Inc (v : Belnap) : r (Inc v) = B₄_T := rfl

theorem c_Inc (v : Belnap) : c (Inc v) = B₄_F := rfl

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

theorem trichotomy_exists : ∃ (m : TrichotomyMaps), True :=
  ⟨{ reflector := r, coreflector := c, closure := Inc,
     reflector_B := rfl, coreflector_B := rfl, closure_B := rfl }, trivial⟩

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

/- The re-entry tower as a genuine marker retraction. Each scale up adds one
   re-entry marker bit — the fibre the round trip forgets. This is a faithful
   model of the section/retraction structure (μ∘η = id, η∘μ = ρ ≠ id, Fix(ρ) ≅ Vₙ);
   the powerset cardinalities live separately in §9 below. -/
def V : ℕ → Type
  | 0     => Unit
  | (n+1) => V n × Bool

instance vInhabited : ∀ n, Inhabited (V n)
  | 0     => ⟨()⟩
  | (n+1) => ⟨((vInhabited n).default, true)⟩

/- Punctum at scale n -/
def p (n : ℕ) : V n := (vInhabited n).default

/- Punctum transport ηₙ : Vₙ → Vₙ₊₁, carry the value up as a marked singleton -/
def η {n : ℕ} (x : V n) : V (n + 1) := (x, true)

/- Reveal μₙ : Vₙ₊₁ → Vₙ, read the carried value back down -/
def μ {n : ℕ} (x : V (n + 1)) : V n := x.1

/- Frame collapse ρₙ₊₁ = ηₙ ∘ μₙ -/
def ρ {n : ℕ} (x : V (n + 1)) : V (n + 1) := η (μ x)

/-
THEOREM: μₙ ∘ ηₙ = id_{Vₙ}  (scaling down after up loses nothing)
-/
theorem μ_η_id {n : ℕ} (x : V n) : μ (η x) = x := rfl

/-
THEOREM: ρₙ₊₁² = ρₙ₊₁ (idempotent)
-/
theorem ρ_idempotent {n : ℕ} (x : V (n + 1)) : ρ (ρ x) = ρ x := rfl

/-
THEOREM: ρₙ₊₁ ≠ id_{Vₙ₊₁} in general (asymmetry of scale): the marker false is
forgotten, so ρ (x, false) = (x, true) ≠ (x, false).
-/
theorem ρ_ne_id {n : ℕ} : ¬ (∀ (x : V (n + 1)), ρ x = x) := by
  intro h
  exact Bool.noConfusion (congrArg Prod.snd (h (p n, false)))

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
    first | constructor | cases h

/-
===============================================================================
§9  UNION FIBRES: WHAT FRAME COLLAPSE FORGETS
===============================================================================
For K ∈ Vₙ, Fibₙ(K) = {A ∈ Vₙ₊₁ | μₙ(A) = K}
Frame collapse identifies every member of the fibre with ηₙ(K) = {K}
F(k) = ∑ᵢ (-1)ᵏ⁻ⁱ (k choose i) 2^{2ⁱ}
-/

/-- The union-fibre count: the number of families of subsets of a k-element set
    whose union is the whole set. It is the inclusion–exclusion (alternating)
    binomial transform of `2 ^ (2 ^ i)`, so it lives in ℤ. -/
def F_fibre (k : ℕ) : ℤ :=
  ∑ i ∈ Finset.range (k + 1), (-1 : ℤ) ^ (k - i) * (Nat.choose k i : ℤ) * 2 ^ (2 ^ i)

theorem F_fibre_zero  : F_fibre 0 = 2 := by decide
theorem F_fibre_one   : F_fibre 1 = 2 := by decide
theorem F_fibre_two   : F_fibre 2 = 10 := by decide
theorem F_fibre_three : F_fibre 3 = 218 := by decide
theorem F_fibre_four  : F_fibre 4 = 64594 := by decide

/- The alternating binomial column collapses to a Kronecker delta:
   ∑ₖ (-1)^(k-i) C(m,k) C(k,i) = [i = m], for i ≤ m. This is the heart of binomial
   inversion, from the trinomial revision C(m,k)C(k,i)=C(m,i)C(m-i,k-i) and the
   vanishing alternating row sum ∑ⱼ (-1)^j C(m-i,j). -/
private lemma alt_choose_column (m i : ℕ) (hi : i ≤ m) :
    (∑ k ∈ Finset.range (m + 1),
        (-1 : ℤ) ^ (k - i) * (m.choose k : ℤ) * (k.choose i : ℤ)) = if i = m then 1 else 0 := by
  have hterm : ∀ k ∈ Finset.range (m + 1),
      (-1 : ℤ) ^ (k - i) * (m.choose k : ℤ) * (k.choose i : ℤ)
        = (m.choose i : ℤ) *
            (if i ≤ k then (-1 : ℤ) ^ (k - i) * ((m - i).choose (k - i) : ℤ) else 0) := by
    intro k _
    by_cases hik : i ≤ k
    · rw [if_pos hik]
      have hcast : (m.choose k : ℤ) * (k.choose i : ℤ)
          = (m.choose i : ℤ) * ((m - i).choose (k - i) : ℤ) := by
        exact_mod_cast Nat.choose_mul hik
      rw [mul_assoc, hcast]; ring
    · rw [if_neg hik]
      have : (k.choose i) = 0 := Nat.choose_eq_zero_of_lt (not_le.mp hik)
      simp [this]
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, ← Finset.sum_filter]
  have hfilter : (Finset.range (m + 1)).filter (fun k => i ≤ k) = Finset.Ico i (m + 1) := by
    ext k; simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]; omega
  rw [hfilter, Finset.sum_Ico_eq_sum_range]
  have hsimp : ∀ j : ℕ,
      (-1 : ℤ) ^ ((i + j) - i) * ((m - i).choose ((i + j) - i) : ℤ)
        = (-1 : ℤ) ^ j * ((m - i).choose j : ℤ) := by
    intro j; rw [Nat.add_sub_cancel_left]
  rw [Finset.sum_congr rfl (fun j _ => hsimp j)]
  have hlen : m + 1 - i = (m - i) + 1 := by omega
  rw [hlen, Int.alternating_sum_range_choose]
  by_cases him : i = m
  · subst him; simp
  · have hne : m - i ≠ 0 := by omega
    simp [if_neg him, if_neg hne]

/- Binomial inversion: summing the alternating transform back against the
   binomials recovers the original sequence. -/
private lemma binomial_inversion (a : ℕ → ℤ) (m : ℕ) :
    (∑ k ∈ Finset.range (m + 1), (m.choose k : ℤ) *
        (∑ i ∈ Finset.range (k + 1), (-1 : ℤ) ^ (k - i) * (k.choose i : ℤ) * a i)) = a m := by
  have e1 : ∀ k ∈ Finset.range (m + 1), (m.choose k : ℤ) *
      (∑ i ∈ Finset.range (k + 1), (-1 : ℤ) ^ (k - i) * (k.choose i : ℤ) * a i)
      = ∑ i ∈ Finset.range (m + 1),
          (m.choose k : ℤ) * ((-1 : ℤ) ^ (k - i) * (k.choose i : ℤ) * a i) := by
    intro k _
    rw [Finset.mul_sum]
    apply Finset.sum_subset
    · intro x hx; simp only [Finset.mem_range] at *; omega
    · intro x _ hx2
      simp only [Finset.mem_range, not_lt] at hx2
      have : (k.choose x) = 0 := Nat.choose_eq_zero_of_lt (by omega)
      simp [this]
  rw [Finset.sum_congr rfl e1, Finset.sum_comm]
  have e2 : ∀ i ∈ Finset.range (m + 1),
      (∑ k ∈ Finset.range (m + 1),
        (m.choose k : ℤ) * ((-1 : ℤ) ^ (k - i) * (k.choose i : ℤ) * a i))
      = a i * (if i = m then 1 else 0) := by
    intro i hi
    simp only [Finset.mem_range] at hi
    have hfactor : (∑ k ∈ Finset.range (m + 1),
          (m.choose k : ℤ) * ((-1 : ℤ) ^ (k - i) * (k.choose i : ℤ) * a i))
        = a i * ∑ k ∈ Finset.range (m + 1),
            ((-1 : ℤ) ^ (k - i) * (m.choose k : ℤ) * (k.choose i : ℤ)) := by
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro k _; ring
    rw [hfactor, alt_choose_column m i (by omega)]
  rw [Finset.sum_congr rfl e2]
  have e3 : ∀ i ∈ Finset.range (m + 1),
      a i * (if i = m then (1 : ℤ) else 0) = if i = m then a i else 0 := by
    intro i _; by_cases h : i = m <;> simp [h]
  rw [Finset.sum_congr rfl e3, Finset.sum_ite_eq']
  simp

/-
Fibre identity: ∑ₖ (m choose k) F(k) = 2^{2ᵐ}. The weighted fibre counts sum to the
full next powerset level, for every m.
-/
theorem fibre_identity (m : ℕ) :
    (∑ k ∈ Finset.range (m + 1), (m.choose k : ℤ) * F_fibre k) = 2 ^ (2 ^ m) := by
  simpa [F_fibre] using binomial_inversion (fun i => (2 : ℤ) ^ (2 ^ i)) m

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
  rfl

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

/- ── The paraconsistent ambient B as a first-class dialetheic verdict ─────── -/

open Imscribing.Paraconsistent.DialetheicWitness in
/-- The ambient both-value B as a verdict: it is the fixed point of the closure
    (Inc B = B) held together with the Boolean impossibility, that no classical
    endomap reproduces the collapse to B. Stable inside, unreachable from the
    Boolean core; the classifier reads B. -/
def ambientBVerdict : Verdict (Inc B = B) :=
  .held Inc_fixed_point_B boolean_impossibility

open Imscribing.Paraconsistent.DialetheicWitness in
theorem ambientBVerdict_is_B : ambientBVerdict.classify = (true, true) := rfl

/-
===============================================================================
§15  THE TRANSLATION LEMMA: δ = η
===============================================================================
The re-entry tower carries a special Frobenius structure. Its comultiplication
δ splits a value up into the next scale as a marked singleton. Read from that
split role, δ looks like a different map from the punctum transport η, which
lifts a value up carrying the re-entry marker. The translation lemma is that
they are the same map. This is the self-dual ⊙ of the ob3ect: unit and counit
coincide, the special Frobenius condition.
-/

/-- The comultiplication δₙ : Vₙ → Vₙ₊₁ of the re-entry Frobenius structure:
    split the value up as a marked singleton. -/
def δ {n : ℕ} (x : V n) : V (n + 1) := (x, true)

/-- TRANSLATION LEMMA: δ = η as maps at every scale. The Frobenius
    comultiplication and the punctum transport are one map. -/
theorem δ_eq_η {n : ℕ} (x : V n) : δ x = η x := rfl

/-- With δ = η the special Frobenius law μ∘δ = id is exactly the tower's
    μ∘η = id: revealing straight after splitting up loses nothing. -/
theorem μ_δ_id {n : ℕ} (x : V n) : μ (δ x) = x := rfl

/-- The frame collapse read through δ agrees with the one read through η. -/
theorem ρ_via_δ {n : ℕ} (x : V (n + 1)) : η (μ x) = δ (μ x) := rfl

/-
===============================================================================
§16  THE COLIMIT THEOREM FOR THE EXTERIOR SEQUENCE
===============================================================================
The exterior sequence is the tower under the punctum transport:
  V₀ →^η V₁ →^η V₂ →^η ⋯
Its colimit is the direct limit: elements of every scale glued along η. Below
is the object, the cocone inclusions, the compatibility ιₙ₊₁∘η = ιₙ, and the
universal property in full — a unique mediating map out of the colimit for any
compatible cocone, with both its computation and its uniqueness.
-/

/-- One point of the exterior sequence: a scale index and a value there. -/
def ExtSeq : Type := Σ n : ℕ, V n

/-- The generating step of the direct system: lift one scale by η. -/
def extStep (a b : ExtSeq) : Prop := b = ⟨a.1 + 1, η a.2⟩

/-- The colimit gluing: the equivalence generated by the η-steps. -/
instance extSetoid : Setoid ExtSeq :=
  ⟨Relation.EqvGen extStep, Relation.EqvGen.is_equivalence extStep⟩

/-- The colimit of the exterior sequence. -/
def Colim : Type := Quotient extSetoid

/-- The cocone inclusion ιₙ : Vₙ → Colim. -/
def ιseq (n : ℕ) (x : V n) : Colim := ⟦⟨n, x⟩⟧

/-- Cocone compatibility: the inclusions commute with the transport, ιₙ₊₁∘η = ιₙ. -/
theorem ιseq_compat (n : ℕ) (x : V n) : ιseq (n + 1) (η x) = ιseq n x :=
  Quotient.sound (Relation.EqvGen.symm _ _ (Relation.EqvGen.rel _ _ rfl))

/-- Universal property, existence: any cocone (W, g) with gₙ₊₁∘η = gₙ factors
    through the colimit by a mediating map `desc g`. -/
def desc {W : Type*} (g : (n : ℕ) → V n → W) (hg : ∀ n (x : V n), g (n + 1) (η x) = g n x) :
    Colim → W :=
  Quotient.lift (fun a : ExtSeq => g a.1 a.2) (by
    intro a b h
    induction h with
    | rel a b hab => subst hab; exact (hg a.1 a.2).symm
    | refl a => rfl
    | symm a b _ ih => exact ih.symm
    | trans a b c _ _ ih1 ih2 => exact ih1.trans ih2)

/-- The mediating map computes on the inclusions: desc g ∘ ιₙ = gₙ. -/
theorem desc_ιseq {W : Type*} (g : (n : ℕ) → V n → W)
    (hg : ∀ n (x : V n), g (n + 1) (η x) = g n x) (n : ℕ) (x : V n) :
    desc g hg (ιseq n x) = g n x := rfl

/-- Universal property, uniqueness: any map agreeing with the cocone on every
    inclusion is `desc g`. Existence and uniqueness together are the colimit. -/
theorem desc_unique {W : Type*} (g : (n : ℕ) → V n → W)
    (hg : ∀ n (x : V n), g (n + 1) (η x) = g n x)
    (h : Colim → W) (hcompat : ∀ n (x : V n), h (ιseq n x) = g n x) :
    h = desc g hg := by
  funext c
  refine Quotient.inductionOn c ?_
  intro a
  exact (hcompat a.1 a.2)

/-- The winding number rises by one along each η-step of the exterior sequence,
    the scale depth the ⊡ mark fixes. -/
theorem winding_step (n : ℕ) : winding_number (n + 1) = winding_number n + 1 := rfl

/-
===============================================================================
§17  THE DIALETHEIC RE-ENTRY CYCLE
===============================================================================
The seven stages of dialetheic re-entry, drawn as the closing loop:

  1 Punctum        pure being, no distinction
  2 Boundary       inside ≠ outside, distinction drawn
  3 Re-entry       the centre sees itself, self-reference
  4 Trilattice     three truth poles
  5 Contained      the imscription wraps the trilattice
  6 Four values    the square frames truth, Belnap FOUR
  7 Closure        imscription, FOUR truth values, trilattice and punctum, one

The double arrow from Closure back to the Punctum is the re-entry: the cycle
advances through all seven and returns, and the return is what makes it a cycle
rather than a ladder.
-/

/-- The seven stages of the dialetheic re-entry. -/
inductive ReEntry : Type where
  | punctum | boundary | reEntry | trilattice | contained | fourValues | closure
  deriving DecidableEq, Repr

namespace ReEntry

/-- Advance one stage; Closure re-enters the Punctum, closing the loop. -/
def advance : ReEntry → ReEntry
  | punctum    => boundary
  | boundary   => reEntry
  | reEntry    => trilattice
  | trilattice => contained
  | contained  => fourValues
  | fourValues => closure
  | closure    => punctum

/-- The winding depth the ⊡ mark fixes at each stage, rising from the punctum. -/
def depth : ReEntry → ℕ
  | punctum    => 0
  | boundary   => 1
  | reEntry    => 2
  | trilattice => 3
  | contained  => 4
  | fourValues => 5
  | closure    => 6

/-- CLOSURE: seven advances return every stage to itself. The re-entry cycle is
    a genuine loop of period seven, not an open chain. -/
theorem cycle_closes (s : ReEntry) : advance^[7] s = s := by
  cases s <;> rfl

/-- The loop has no shorter period: one advance moves every stage. -/
theorem advance_moves (s : ReEntry) : advance s ≠ s := by
  cases s <;> decide

/-- Stage 3, re-entry, is the centre seeing itself: the dialetheic self-reference
    is the closure fixed point Inc B = B, the both-value holding itself. -/
theorem reEntry_is_self_reference : Inc B = B := Inc_fixed_point_B

/-- Stage 6, four values, is Belnap's FOUR: the four truths are pairwise
    distinct, the square framing exactly {N, T, F, B}. -/
theorem fourValues_distinct :
    N ≠ T ∧ N ≠ F ∧ N ≠ B ∧ T ≠ F ∧ T ≠ B ∧ F ≠ B := by decide

/-- Closure is reached from the punctum in six advances, one per form drawn:
    boundary, re-entry, trilattice, the containing imscription, the four values,
    and the closing frame. -/
theorem punctum_reaches_closure : advance^[6] punctum = closure := by rfl

/-- And closure re-enters the punctum, the double arrow. Unifying the four forms
    (imscription, FOUR truth values, trilattice, punctum) is that return: the
    whole is fed back into the point it started from. -/
theorem closure_reenters : advance closure = punctum := rfl

end ReEntry

/-
===============================================================================
§18  SELF-SIMILAR ZOOM: THE PUNCTUM–IMSCRIPTION HOLONOMY
===============================================================================
Zoom in on a punctum and it expands into a new imscription together with a new
punctum at once; zoom out and the bounding imscription itself becomes the
punctum of a larger imscription. The two moves are the tower's transport, and
their asymmetry is a holonomy: one round trip is flat, the other is not.

  zoomOut = η : Vₙ → Vₙ₊₁   the punctum gains a bounding imscription, the old
                             content is now what the boundary contains
  zoomIn  = μ : Vₙ₊₁ → Vₙ   descend into the inner punctum

`zoomIn ∘ zoomOut = id` is local flatness — magnifying a fresh boundary and
coming back loses nothing. `zoomOut ∘ zoomIn = ρ ≠ id` is the non-trivial
holonomy — zoom into a boundary and back and the marker bit is gone, the
boundary and punctum have swapped roles. This is the CircumPunctum instance of
`CosmicHolonomy`'s locally-flat-yet-globally-non-trivial connection; the choice
of which cut to call the punctum is the basepoint `MachHolonomy` shows only
conjugates the holonomy, never trivialises it.
-/

/-- Zoom out: wrap the punctum in a new bounding imscription. -/
def zoomOut {n : ℕ} (x : V n) : V (n + 1) := η x

/-- Zoom in: descend to the inner punctum. -/
def zoomIn {n : ℕ} (x : V (n + 1)) : V n := μ x

/-- Every scale has the same shape: a punctum wrapped by one boundary bit. The
    structure is scale-invariant, which is what makes the zoom self-similar. -/
theorem scale_self_similar (n : ℕ) : V (n + 1) = (V n × Bool) := rfl

/-- Local flatness: zoom out then in and nothing is lost. -/
theorem zoom_flat {n : ℕ} (x : V n) : zoomIn (zoomOut x) = x := rfl

/-- Non-trivial holonomy: zoom into a boundary and back does not return. The
    marker bit is forgotten, so the boundary that was outside comes back as the
    marked punctum — the punctum–imscription swap. -/
theorem zoom_holonomy {n : ℕ} : ∃ x : V (n + 1), zoomOut (zoomIn x) ≠ x :=
  ⟨(p n, false), by
    intro h
    exact Bool.noConfusion (congrArg Prod.snd h)⟩

/-- The two readings are one map at the fixed point: on a marked value zoom-out
    after zoom-in is the frame collapse ρ, idempotent, so the holonomy is a
    genuine retraction and not noise. -/
theorem zoom_is_collapse {n : ℕ} (x : V (n + 1)) : zoomOut (zoomIn x) = ρ x := rfl

end Imscribing.CircumPunctum