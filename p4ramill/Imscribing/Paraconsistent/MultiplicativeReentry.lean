import Imscribing.ReEntryConstructions

namespace Imscribing.Paraconsistent.MultiplicativeReentry

/-- Both arms belong to one resident relation, before multiplication. -/
abbrev Pair := Nat × Nat
abbrev Family := Finset Pair

/-- Print the size without expanding a retained relation into terminal output. -/
instance : Repr Family where
  reprPrec family _ := "paired_alternatives=" ++ repr family.card

/-- The multiplicative arm uses the existing well-space evaluation. -/
def multiply (pair : Pair) : Nat := primeEval [pair.1, pair.2]

theorem multiply_eq (pair : Pair) : multiply pair = pair.1 * pair.2 := by
  simp [multiply, primeEval]

/-- Specialize the proved two-leaf well evaluation in generated machine code. -/
def multiplyFast (pair : Pair) : Nat := pair.1 * pair.2

@[csimp] theorem multiply_native : multiply = multiplyFast :=
  funext multiply_eq


/-- Powerset unit and bind retain paired alternatives together. -/
def unit (pair : Pair) : Family := {pair}
def bind (family : Family) (f : Pair → Family) : Family := family.biUnion f

theorem bind_left_unit (pair : Pair) (f : Pair → Family) :
    bind (unit pair) f = f pair := by simp [bind, unit]

theorem bind_right_unit (family : Family) : bind family unit = family := by
  ext pair
  simp [bind, unit]

theorem bind_assoc (family : Family) (f g : Pair → Family) :
    bind (bind family f) g = bind family (fun pair => bind (f pair) g) := by
  simp [bind, Finset.biUnion_biUnion]

/-- Lift the inverse image of multiplication by one binary distinction.
Every returned pair satisfies the next source boundary. No factor or width
is supplied. The four alternatives are disjoint binary extensions. -/
def split (N modulus : Nat) (pair : Pair) : Family :=
  let choices : Family := {(pair.1, pair.2), (pair.1 + modulus, pair.2),
    (pair.1, pair.2 + modulus), (pair.1 + modulus, pair.2 + modulus)}
  if pair.1 < modulus ∧ pair.2 < modulus then choices.filter fun candidate =>
    multiply candidate % (2 * modulus) = N % (2 * modulus) ∧
    multiply candidate ≤ N
  else ∅

theorem split_parent {N modulus : Nat} {pair candidate : Pair}
    (h : candidate ∈ split N modulus pair) :
    candidate.1 % modulus = pair.1 ∧ candidate.2 % modulus = pair.2 := by
  unfold split at h
  split_ifs at h with bound
  · have choices := (Finset.mem_filter.mp h).1
    simp only [Finset.mem_insert, Finset.mem_singleton] at choices
    rcases choices with rfl | rfl | rfl | rfl <;>
      simp [Nat.add_mod, Nat.mod_eq_of_lt bound.1, Nat.mod_eq_of_lt bound.2]
  · simp at h

def reenterRaw (N modulus : Nat) (family : Family) : Family :=
  family.disjiUnion (split N modulus) (by
    intro a ha b hb distinct
    apply Finset.disjoint_left.mpr
    intro candidate left right
    have l := split_parent left
    have r := split_parent right
    apply distinct
    exact Prod.ext (l.1.symm.trans r.1) (l.2.symm.trans r.2))

/-- Prepend each small branch rather than recursively appending a large family. -/
def prepend (acc part : Multiset Pair) : Multiset Pair := part + acc

instance : RightCommutative prepend where
  right_comm a b c := by simp [prepend, add_assoc, add_left_comm]

def flattenParts (parts : Multiset (Multiset Pair)) : Multiset Pair :=
  parts.foldl prepend 0

theorem flattenParts_eq (parts : Multiset (Multiset Pair)) :
    flattenParts parts = parts.join := by
  have general : ∀ acc, parts.foldl prepend acc = parts.join + acc := by
    induction parts using Multiset.induction_on with
    | empty => intro acc; simp [Multiset.foldl_zero]
    | @cons part parts ih =>
      intro acc
      rw [Multiset.foldl_cons, ih]
      simp [prepend, add_assoc, add_left_comm]
  simpa [flattenParts] using general 0

/-- Apply and flatten each disjoint branch in one resident traversal. -/
def expandStep (N modulus : Nat) (acc : Multiset Pair) (pair : Pair) : Multiset Pair :=
  (split N modulus pair).val + acc

instance (N modulus : Nat) : RightCommutative (expandStep N modulus) where
  right_comm a b c := by simp [expandStep, add_assoc, add_left_comm]

theorem expand_eq (N modulus : Nat) (family : Multiset Pair) (acc : Multiset Pair) :
    family.foldl (expandStep N modulus) acc =
      (family.map fun pair => (split N modulus pair).val).join + acc := by
  induction family using Multiset.induction_on generalizing acc with
  | empty => simp
  | @cons pair family ih =>
    rw [Multiset.foldl_cons, ih]
    simp [expandStep, add_assoc, add_left_comm]

def reenter (N modulus : Nat) (family : Family) : Family :=
  ⟨family.val.foldl (expandStep N modulus) 0, by
    rw [expand_eq, add_zero]
    exact (reenterRaw N modulus family).nodup⟩

theorem reenter_eq_raw (N modulus : Nat) (family : Family) :
    reenter N modulus family = reenterRaw N modulus family := by
  apply Finset.val_injective
  simpa [reenter] using expand_eq N modulus family.val 0

theorem reenter_bind (N modulus : Nat) (family : Family) :
    reenter N modulus family = bind family (split N modulus) := by
  rw [reenter_eq_raw]
  ext candidate
  simp [reenterRaw, bind]

def select (N : Nat) (pair : Pair) : Nat :=
  if 1 < pair.1 ∧ 1 < pair.2 ∧ multiply pair = N then pair.1 else N

def readStep (N : Nat) (acc : Nat) (pair : Pair) : Nat := min acc (select N pair)

instance (N : Nat) : RightCommutative (readStep N) where
  right_comm a b c := by simp [readStep, min_assoc, min_left_comm, min_comm]

theorem readFold_eq (N : Nat) (family : Multiset Pair) (acc : Nat) :
    family.foldl (readStep N) acc = (family.map (select N)).foldl min acc := by
  induction family using Multiset.induction_on generalizing acc with
  | empty => rfl
  | @cons pair family ih => simpa [readStep] using ih (readStep N acc pair)

/-- Read only an exact proper product from the shared returned family. -/
def read (N : Nat) (family : Family) : Option Nat :=
  let divisor := family.val.foldl (readStep N) N
  if divisor < N then some divisor else none

theorem split_source {N modulus : Nat} {pair candidate : Pair}
    (h : candidate ∈ split N modulus pair) :
    multiply candidate % (2 * modulus) = N % (2 * modulus) ∧
      multiply candidate ≤ N := by
  unfold split at h
  split_ifs at h
  · exact (Finset.mem_filter.mp h).2
  · simp at h

end Imscribing.Paraconsistent.MultiplicativeReentry
