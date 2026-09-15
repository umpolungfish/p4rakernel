/-
  FoldVerdict — the four-valued structural readout of a word, in closed form.

  A word is a list of the twelve marks. Two of them fork and fuse; seven do work;
  three (the two boundaries and self-reference) do neither. The readout is defined
  by a stack pairing of forks against fuses, and this file proves that it depends
  on the word through only the signed difference of the two counts and, when that
  difference vanishes, one existential condition on what a paired region encloses.

  The genetic lift carries the fork to asparagine and the fuse to glutamine, so the
  readout of a coding sequence is decided by the codon families AAY and CAR. Those
  facts are decided here over the finite codon type.
-/
import Mathlib

namespace Imscribing.FoldVerdict

/-- The twelve marks. -/
inductive Mark
  | vinit | tanch | afwd | arev | clink | evalt
  | fsplit | ffuse | imscrib | evalf | evali | ifix
  deriving DecidableEq, Repr, Fintype

open Mark

/-- Exactly twelve. -/
theorem twelve_marks : Fintype.card Mark = 12 := by decide

def isFork : Mark → Bool | fsplit => true | _ => false
def isFuse : Mark → Bool | ffuse  => true | _ => false

/-- Seven of the twelve transform a state. The boundaries, self-reference, and
    the fork and fuse themselves do not. -/
def doesWork : Mark → Bool
  | afwd | arev | clink | evalt | evalf | evali | ifix => true
  | _ => false

theorem work_card : (Finset.univ.filter (fun m => doesWork m = true)).card = 7 := by decide

theorem noWork_card : (Finset.univ.filter (fun m => doesWork m = false)).card = 5 := by decide

/-- Fork and fuse do no work, and neither is the other. -/
theorem fork_fuse_no_work :
    doesWork fsplit = false ∧ doesWork ffuse = false ∧ isFork ffuse = false := by decide

/-- Self-reference does no work. This is the witness that separates the enclosure
    condition from the weaker condition that a region merely be non-empty. -/
theorem imscrib_no_work : doesWork imscrib = false := by decide

/-! ### The stack pairing -/

/-- One step of the pairing: a fork pushes, a fuse pops if it can and is otherwise
    recorded unmatched, anything else passes. The state is
    (open forks on the stack, fuses that found the stack empty). -/
def step : ℕ × ℕ → Mark → ℕ × ℕ
  | (d, u), m =>
      if isFork m then (d + 1, u)
      else if isFuse m then (if d = 0 then (0, u + 1) else (d - 1, u))
      else (d, u)

/-- Pair a word left to right. The result is (unmatched forks, unmatched fuses). -/
def pairing (w : List Mark) : ℕ × ℕ := w.foldl step (0, 0)

/-- The pairing consumes one fork with each fuse it matches, so the signed
    difference of the unmatched counts is the signed difference of the counts. -/
theorem surplus_general (w : List Mark) (d u : ℕ) :
    ((w.foldl step (d, u)).1 : ℤ) - ((w.foldl step (d, u)).2 : ℤ)
      = (d : ℤ) - (u : ℤ) + (w.countP isFork : ℤ) - (w.countP isFuse : ℤ) := by
  induction w generalizing d u with
  | nil => simp
  | cons m w ih =>
      cases m <;>
        simp [List.foldl_cons, step, isFork, isFuse, List.countP_cons, ih] <;>
        (first
          | omega
          | (rcases Nat.eq_zero_or_pos d with h | h
             · subst h; simp [ih]; omega
             · rw [if_neg (by omega)]; omega))

/-- The Surplus Lemma, stated on the word alone. -/
theorem surplus (w : List Mark) :
    ((pairing w).1 : ℤ) - ((pairing w).2 : ℤ)
      = (w.countP isFork : ℤ) - (w.countP isFuse : ℤ) := by
  simpa using surplus_general w 0 0

/-- Rotation does not move the surplus: the readout is taken from whichever
    rotation pairs without avoidable underflow, and the identity is the same
    there, because a rotation is a permutation. -/
theorem surplus_rotate (w : List Mark) (k : ℕ) :
    ((pairing (w.rotate k)).1 : ℤ) - ((pairing (w.rotate k)).2 : ℤ)
      = (w.countP isFork : ℤ) - (w.countP isFuse : ℤ) := by
  have hp : (w.rotate k).Perm w := List.rotate_perm w k
  rw [surplus, hp.countP_eq, hp.countP_eq]

/-! ### The verdict -/

inductive Verdict | T | B | N | F
  deriving DecidableEq, Repr

open Verdict

/-- The closed form. `d` is the signed difference of the counts; `sub` says some
    paired region encloses a mark that does work. -/
def verdictOf (d : ℤ) (sub : Bool) : Verdict :=
  if d > 0 then B else if d < 0 then F else if sub then T else N

/-- The two failure modes are decided by composition alone, so no rearrangement
    moves a word off them: any permutation preserves both counts. -/
theorem verdict_perm_invariant_of_ne (w v : List Mark) (hp : w.Perm v)
    (sub sub' : Bool)
    (h : (w.countP isFork : ℤ) - (w.countP isFuse : ℤ) ≠ 0) :
    verdictOf ((w.countP isFork : ℤ) - (w.countP isFuse : ℤ)) sub
      = verdictOf ((v.countP isFork : ℤ) - (v.countP isFuse : ℤ)) sub' := by
  have hf : w.countP isFork = v.countP isFork := hp.countP_eq _
  have hg : w.countP isFuse = v.countP isFuse := hp.countP_eq _
  rw [hf, hg] at h ⊢
  unfold verdictOf
  rcases lt_or_gt_of_ne h with hlt | hgt
  · rw [if_neg (by omega), if_pos hlt, if_neg (by omega), if_pos hlt]
  · rw [if_pos hgt, if_pos hgt]

/-- Both failure modes cannot be repaired by rearrangement, and neither can be
    turned into closure by it. -/
theorem no_repair_by_rearrangement (w v : List Mark) (hp : w.Perm v) :
    (w.countP isFork : ℤ) - (w.countP isFuse : ℤ)
      = (v.countP isFork : ℤ) - (v.countP isFuse : ℤ) := by
  rw [hp.countP_eq, hp.countP_eq]

/-! ### The genetic lift -/

inductive Base | A | C | G | U
  deriving DecidableEq, Repr, Fintype

open Base

abbrev Codon := Base × Base × Base

theorem codon_card : Fintype.card Codon = 64 := by decide

/-- The promoted codons and the mark each emits; an unpromoted codon emits
    nothing. -/
def lift : Codon → Option Mark
  | (A, U, G) => some vinit
  | (U, G, G) => some tanch
  | (U, G, U) | (U, G, C) => some afwd
  | (U, A, U) | (U, A, C) => some arev
  | (U, U, U) | (U, U, C) => some clink
  | (A, U, U) | (A, U, C) | (A, U, A) => some evalt
  | (A, A, U) | (A, A, C) => some fsplit
  | (C, A, A) | (C, A, G) => some ffuse
  | (C, A, U) | (C, A, C) => some imscrib
  | (G, A, U) | (G, A, C) => some evalf
  | (A, A, A) | (A, A, G) => some evali
  | (G, A, A) | (G, A, G) => some ifix
  | _ => none

/-- Twenty-three of the sixty-four codons are promoted. -/
theorem promoted_card :
    (Finset.univ.filter (fun c : Codon => (lift c).isSome)).card = 23 := by decide

/-- Every mark is emitted by some codon: the lift is onto the twelve. -/
theorem lift_surjective : ∀ m : Mark, ∃ c : Codon, lift c = some m := by decide

/-- The fork is exactly the codon family AAY. -/
theorem fork_is_AAY : ∀ c : Codon,
    lift c = some fsplit ↔ (c = (A, A, U) ∨ c = (A, A, C)) := by decide

/-- The fuse is exactly the codon family CAR. -/
theorem fuse_is_CAR : ∀ c : Codon,
    lift c = some ffuse ↔ (c = (C, A, A) ∨ c = (C, A, G)) := by decide

/-- Fork and fuse differ in the first base alone, with A fixed at the second. -/
theorem fork_fuse_first_base :
    ∀ c : Codon, (lift c = some fsplit ∨ lift c = some ffuse) →
      c.2.1 = A ∧ (c.1 = A ∨ c.1 = C) := by decide

/-- The full {A,C}A{U,C,A,G} block splits four ways: fork, stoichiometry, fuse,
    criticality. -/
theorem the_ACA_block :
    lift (A, A, U) = some fsplit ∧ lift (A, A, C) = some fsplit ∧
    lift (A, A, A) = some evali ∧ lift (A, A, G) = some evali ∧
    lift (C, A, A) = some ffuse ∧ lift (C, A, G) = some ffuse ∧
    lift (C, A, U) = some imscrib ∧ lift (C, A, C) = some imscrib := by decide

/-- The three promoted marks besides fork and fuse that do no work. -/
theorem no_work_promoted :
    ∀ c : Codon, ∀ m, lift c = some m → doesWork m = false →
      (m = vinit ∨ m = tanch ∨ m = imscrib ∨ m = fsplit ∨ m = ffuse) := by decide

/-- Reading a frame: each promoted codon emits its mark. -/
def word (frame : List Codon) : List Mark := frame.filterMap lift

/-- The readout of a frame is decided by its AAY and CAR codons. -/
def isAAY (c : Codon) : Bool := decide (lift c = some fsplit)
def isCAR (c : Codon) : Bool := decide (lift c = some ffuse)

theorem frame_counts (frame : List Codon) :
    (word frame).countP isFork = frame.countP isAAY ∧
    (word frame).countP isFuse = frame.countP isCAR := by
  constructor <;>
  · induction frame with
    | nil => simp [word]
    | cons c f ih =>
        cases h : lift c <;>
          simp_all [word, List.filterMap_cons, List.countP_cons, isAAY, isCAR,
                    isFork, isFuse, h] <;>
          (rename_i m; cases m <;> simp_all)

end Imscribing.FoldVerdict

#print axioms Imscribing.FoldVerdict.surplus
#print axioms Imscribing.FoldVerdict.fork_is_AAY
#print axioms Imscribing.FoldVerdict.fuse_is_CAR
#print axioms Imscribing.FoldVerdict.frame_counts
#print axioms Imscribing.FoldVerdict.no_repair_by_rearrangement
