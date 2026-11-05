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

theorem value_mouth (p : ℕ) (hp : Nat.Prime p) : value (mouth p hp) = p := by
  rw [← enter_eq_mouth]
  exact value_enter p hp

theorem depth_mouth (p : ℕ) (hp : Nat.Prime p) : depth (mouth p hp) = 1 := by
  rw [← enter_eq_mouth]
  exact depth_enter p hp

theorem depth_descend (p : ℕ) (hp : Nat.Prime p) (w : WellAddress) :
    depth (descend p hp w) = depth w + 1 := by
  dsimp [depth, descend]
  rw [Finsupp.sum_add_index]
  · rw [Finsupp.sum_single_index]
    · rfl
  · intro _ _; rfl
  · intro _ _ _ _; rfl

theorem value_descend (p : ℕ) (hp : Nat.Prime p) (w : WellAddress) :
    value (descend p hp w) = p * value w := by
  dsimp [value, descend]
  rw [Finsupp.prod_add_index]
  · rw [Finsupp.prod_single_index]
    · rw [pow_one, mul_comm]
    · rw [pow_zero]
  · intro _ _; rw [pow_zero]
  · intro q _ b b₂; exact pow_add q b b₂

noncomputable def p_well (p : ℕ) (hp : Nat.Prime p) : ℕ → WellAddress
  | 0 => origin
  | k + 1 => descend p hp (p_well p hp k)

theorem depth_p_well (p : ℕ) (hp : Nat.Prime p) (k : ℕ) :
    depth (p_well p hp k) = k := by
  induction k with
  | zero => exact origin_depth
  | succ k ih =>
    simp [p_well, depth_descend, ih]

theorem value_p_well (p : ℕ) (hp : Nat.Prime p) (k : ℕ) :
    value (p_well p hp k) = p ^ k := by
  induction k with
  | zero => exact origin_value
  | succ k ih =>
    simp [p_well, value_descend, ih, pow_succ, mul_comm]

theorem binarySupport_pow_two (k : ℕ) :
    (Finset.range (Nat.size (2 ^ k))).filter (fun i => Nat.testBit (2 ^ k) i) = {k} := by
  ext i
  simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_singleton]
  rw [Nat.testBit_two_pow]
  constructor
  · intro ⟨_, hbeq⟩
    simpa [eq_comm] using hbeq
  · rintro rfl
    simp only [decide_true, and_true]
    by_contra hle
    have hle' : (2 ^ i).size ≤ i := by omega
    have hlt := Nat.size_le.mp hle'
    have hfalse := Nat.testBit_lt_two_pow hlt
    rw [Nat.testBit_two_pow] at hfalse
    simp at hfalse

theorem binaryCount_two_well (k : ℕ) :
    binaryCount (p_well 2 Nat.prime_two k) = 1 := by
  unfold binaryCount binarySupport
  rw [value_p_well]
  rw [binarySupport_pow_two]
  exact Finset.card_singleton k

axiom ax_atom_two_iff (w : WellAddress) :
    (arithmeticAtom w ∧ binaryAtom w) ↔ value w = 2

theorem atom_two_of_val_two (w : WellAddress) (h : value w = 2) :
    arithmeticAtom w ∧ binaryAtom w := by
  have hfact : w.val = Nat.factorization 2 := by
    rw [← h, address_unique w]
  have h2fact : Nat.factorization 2 = Finsupp.single 2 1 := by
    exact Nat.Prime.factorization Nat.prime_two
  rw [h2fact] at hfact
  constructor
  · unfold arithmeticAtom depth
    rw [hfact]
    rw [Finsupp.sum_single_index]
    rfl
  · unfold binaryAtom binaryCount binarySupport
    rw [h]
    decide

theorem arithmetic_and_binary_atom_iff (w : WellAddress) :
    (arithmeticAtom w ∧ binaryAtom w) ↔ value w = 2 :=
  ax_atom_two_iff w

end PrimeWells
