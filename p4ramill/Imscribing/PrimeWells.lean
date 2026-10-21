import Mathlib

/-!
# Prime wells: prime-exponent coordinates as the primary arithmetic space

Target: Lean 4 + Mathlib. This is a source draft, not a compiled certificate.
`WellAddress` stores finitely many positive prime exponents. The restriction
is enforced by a subtype, not by a comment about arbitrary natural bases.
-/

namespace PrimeWells

/-- An address is a finite map from prime labels to exponents. -/
abbrev WellAddress := { e : ℕ →₀ ℕ // ∀ p ∈ e.support, Nat.Prime p }

/-- Origin is the empty multiplicative address, representing 1. -/
def origin : WellAddress := ⟨0, by simp⟩

/-- The total re-entry depth, counting prime factors with multiplicity. -/
def depth (w : WellAddress) : ℕ := w.val.sum (fun _ exponent => exponent)

/-- Evaluate an exponent address as a positive integer. -/
def value (w : WellAddress) : ℕ := w.val.prod (fun p exponent => p ^ exponent)

/-- A prime-well entrance at exponent 1. -/
noncomputable def mouth (p : ℕ) (hp : Nat.Prime p) : WellAddress :=
  ⟨Finsupp.single p 1, by
    intro q hq
    have h : q = p := by
      simp only [Finsupp.mem_support_single] at hq
      exact hq.1
    simpa [h] using hp⟩

/-- Descending one level into the prime-p well. -/
noncomputable def descend (p : ℕ) (hp : Nat.Prime p) (w : WellAddress) : WellAddress :=
  ⟨w.val + Finsupp.single p 1, by
    intro q hq
    by_cases hqp : q = p
    · simpa [hqp] using hp
    · have hsingle : (Finsupp.single p (1 : ℕ)) q = 0 := by
        simp [Finsupp.single_apply, hqp]
      have hw : w.val q ≠ 0 := by
        simpa [Finsupp.mem_support_iff, Finsupp.add_apply, hsingle] using hq
      exact w.property q (Finsupp.mem_support_iff.mpr hw)⟩

/-- Binary support is a second reading of the evaluated address. -/
def binarySupport (w : WellAddress) : Finset ℕ :=
  (Finset.range (Nat.size (value w))).filter (fun i => (Nat.testBit (value w) i))

/-- Composition counted as occupied binary positions. -/
def binaryCount (w : WellAddress) : ℕ := (binarySupport w).card

/-- Prime atomicity is depth one; binary atomicity is binary count one. -/
def arithmeticAtom (w : WellAddress) : Prop := depth w = 1

def binaryAtom (w : WellAddress) : Prop := binaryCount w = 1

/-- The empty address is the origin of every well. -/
theorem origin_depth : depth origin = 0 := by simp [depth, origin]

theorem origin_value : value origin = 1 := by simp [value, origin]

/-!
Proof obligations for the full module, deliberately NOT asserted as theorems
until compiled and checked against the actual Mathlib version:

* value (mouth p hp) = p
* depth (mouth p hp) = 1
* value (descend p hp w) = p * value w
* depth (descend p hp w) = depth w + 1
* unique address for each n > 0 via `Nat.factorization n`
* (arithmeticAtom w ∧ binaryAtom w) ↔ value w = 2
* depth (p-well k) = k; value (p-well k) = p^k
* binaryCount of the 2-well is 1 at each positive depth

These are implementation targets, not assumed axioms or `sorry` proofs.
-/

end PrimeWells
