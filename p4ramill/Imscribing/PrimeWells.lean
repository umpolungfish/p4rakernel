import Mathlib

/-!
# Prime wells: prime-exponent coordinates as the primary arithmetic space

`WellAddress` stores finitely many positive prime exponents. The restriction
is enforced by a subtype, not by a comment about arbitrary natural bases.
Executable entrance search retains its source exclusions through Y. The
total coordinate equivalence and its evaluation laws are separate definitions.
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

/-- The source-only inverse supplied by the prime-coordinate equivalence.
Its executable arithmetic is `Nat.factorization`; evaluating this definition
includes the work of discovering the occupied prime labels. -/
def ofPositive (n : ℕ+) : WellAddress := Nat.factorizationEquiv n

theorem value_ofPositive (n : ℕ+) : value (ofPositive n) = n.val :=
  Nat.factorization_prod_pow_eq_self (ne_of_gt n.property)

/-- An executable finite-support reading of the actual address. -/
def coordinates (w : WellAddress) : List (ℕ × ℕ) :=
  (w.val.support.sort (· ≤ ·)).map fun p => (p,w.val p)

theorem address_unique (w : WellAddress) : (value w).factorization = w.val :=
  Nat.prod_pow_factorization_eq_self w.property

theorem value_injective : Function.Injective value := by
  intro w v h
  apply Subtype.ext
  rw [←address_unique w, ←address_unique v, h]

/-- Executable representation of the canonical exponent-one entrance. -/
def enter (p : ℕ) (hp : Nat.Prime p) : WellAddress :=
  ⟨{support:={p}, toFun:=fun q => if q=p then 1 else 0,
    mem_support_toFun:=by intro q; simp}, by
    intro q hq
    have h : q=p := by simpa using hq
    simpa [h] using hp⟩

theorem enter_eq_mouth (p : ℕ) (hp : Nat.Prime p) : enter p hp = mouth p hp := by
  apply Subtype.ext
  ext q
  simp [enter, mouth, Finsupp.single_apply, eq_comm]

theorem value_enter (p : ℕ) (hp : Nat.Prime p) : value (enter p hp) = p := by
  simp [value, enter, Finsupp.prod]

theorem depth_enter (p : ℕ) (hp : Nat.Prime p) : depth (enter p hp) = 1 := by
  simp [depth, enter, Finsupp.sum]

theorem enter_eq_descend_origin (p : ℕ) (hp : Nat.Prime p) :
    enter p hp = descend p hp origin := by
  apply Subtype.ext
  ext q
  simp [enter, descend, origin, Finsupp.add_apply, Finsupp.single_apply, eq_comm]

/-- An unresolved entrance search carries its exclusion evidence. Every
candidate smaller than the current one was tested against this same source. -/
structure Search (N : ℕ) where
  candidate : ℕ
  lower : 2 ≤ candidate
  excluded : ∀ k, 2 ≤ k → k < candidate → ¬k ∣ N
  deriving DecidableEq

def startSearch (N : ℕ) : Search N := ⟨2,by omega,by intros; omega⟩

inductive SearchReturn (N : ℕ) where
  | held : Search N → SearchReturn N
  | entered : (p : ℕ) → (hp : Nat.Prime p) → p ∣ N → SearchReturn N

/-- One source-bound operation. The surrounding Y owns the continuation. -/
def searchStep {N : ℕ} (s : Search N) : SearchReturn N :=
  if divides : s.candidate ∣ N then
    .entered s.candidate
      (Nat.prime_def_lt'.mpr ⟨s.lower, fun k hk hlt hdiv =>
        s.excluded k hk hlt (dvd_trans hdiv divides)⟩) divides
  else
    .held ⟨s.candidate+1,by have := s.lower; omega,by
      intro k hk hlt hdiv
      by_cases same : k=s.candidate
      · exact divides (same ▸ hdiv)
      · exact s.excluded k hk (by omega) hdiv⟩

/-!
Proof obligations for the full module, deliberately NOT asserted as theorems
until compiled and checked against the actual Mathlib version:

* value (mouth p hp) = p
* depth (mouth p hp) = 1
* value (descend p hp w) = p * value w
* depth (descend p hp w) = depth w + 1
* (arithmeticAtom w ∧ binaryAtom w) ↔ value w = 2
* depth (p-well k) = k; value (p-well k) = p^k
* binaryCount of the 2-well is 1 at each positive depth

These are implementation targets, not assumed axioms or `sorry` proofs.
The positive-integer inverse, uniqueness, and executable entrance evaluation
and depth are proved above. `enter_eq_descend_origin` identifies the native
entrance with the canonical well descent from the shared origin.
-/

end PrimeWells
