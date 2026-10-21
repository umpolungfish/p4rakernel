import Mathlib

namespace BCReentry

/-- The four binary positions N,T,F,B are numbered 0,1,2,3. -/
def selected (n : Nat) (i : Fin 4) : Bool :=
  decide ((n / 2 ^ i.val) % 2 = 1)

/-- A bounded mask's support in the four-bit universe. -/
def support4 (n : Nat) : Finset (Fin 4) :=
  Finset.univ.filter (fun i => selected n i)

/-- B-composition count (on four positions). -/
def bCount4 (n : Nat) : Nat := (support4 n).card

/-- B atomicity in the four-position mask semantics. -/
def bAtom4 (n : Nat) : Prop := bCount4 n = 1

/-- C atomicity uses ordinary arithmetic primality. -/
def cAtom (n : Nat) : Prop := Nat.Prime n

/-- Reconstruction by summing selected positional weights. -/
def reconstruct4 (n : Nat) : Nat :=
  ∑ i ∈ support4 n, (2 : Nat) ^ i.val

/-- The first 16 masks reconstruct their integer labels. -/
theorem four_bit_reconstruct :
    ∀ n : Fin 16, reconstruct4 n.val = n.val := by
  decide

/-- The only label (among 0..15) atomic under both readings is 2. -/
theorem common_atom_four_bit :
    ∀ n : Fin 16, (cAtom n.val ∧ bAtom4 n.val) ↔ n.val = 2 := by
  intro n
  fin_cases n <;>
  (try decide) <;>
  (try
    {
      constructor <;> intro h <;>
      (try contradiction) <;>
      (try norm_num [cAtom, bAtom4, bCount4, support4, selected] at h ⊢) <;>
      (try rfl) <;>
      (try aesop)
    }) <;>
  (try
    {
      norm_num [cAtom, bAtom4, bCount4, support4, selected] at *
      <;>
      (try decide) <;>
      (try aesop)
    })

/-- B is a singleton and not the T/F composite. -/
theorem singleton_B : support4 8 = {⟨3, by decide⟩} := by
  decide

theorem TF_composite :
    support4 6 = ({⟨1, by decide⟩, ⟨2, by decide⟩} : Finset (Fin 4)) := by
  decide

theorem zero_empty : support4 0 = ∅ := by
  decide

theorem mask_one_is_N :
    support4 1 = ({⟨0, by decide⟩} : Finset (Fin 4)) := by
  decide

/-- The 8/13 reversal, expressed without identifying the two grammars. -/
theorem eight_B_atomic : bAtom4 8 := by
  norm_num [bAtom4, bCount4, support4, selected]
  <;> rfl

theorem eight_C_composite : ¬ cAtom 8 := by
  norm_num [cAtom, Nat.Prime]

theorem thirteen_C_atomic : cAtom 13 := by
  norm_num [cAtom, Nat.Prime]

theorem thirteen_B_composite : ¬ bAtom4 13 := by
  norm_num [bAtom4, bCount4, support4, selected]
  <;> decide

/-- Cardinalities on the key arithmetic examples. -/
theorem sample_counts :
    bCount4 2 = 1 ∧ bCount4 6 = 2 ∧
    bCount4 8 = 1 ∧ bCount4 13 = 3 := by
  constructor
  · -- bCount4 2 = 1
    norm_num [bCount4, support4, selected] <;> rfl
  constructor
  · -- bCount4 6 = 2
    norm_num [bCount4, support4, selected] <;> rfl
  constructor
  · -- bCount4 8 = 1
    norm_num [bCount4, support4, selected] <;> rfl
  · -- bCount4 13 = 3
    norm_num [bCount4, support4, selected] <;> rfl

theorem bridge_obligation : True := by trivial

end BCReentry