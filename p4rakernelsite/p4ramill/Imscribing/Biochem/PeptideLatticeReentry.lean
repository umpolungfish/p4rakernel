import Mathlib

/-! The supplied peptide word's B sector composes eight copies of the same
carried source relation. Banked re-entry retains the source and that return.
The resulting seven-step congruence is derived from the word, not supplied
as a clock parameter. These are carrier laws, not a folding completion claim.
-/
namespace Imscribing.Biochem.PeptideLatticeReentry

structure Channels (α : Type*) where
  n : α
  t : α
  f : α
  b : α

variable {α : Type*} [Semiring α]

def evalT (x : Channels α) : Channels α := ⟨0, x.t, 0, x.b⟩
def evalF (x : Channels α) : Channels α := ⟨x.n, 0, x.f, 0⟩
def arev (x : Channels α) : Channels α := ⟨x.t, x.n, x.b, x.f⟩
def clink (x : Channels α) : Channels α := ⟨x.n*x.n, x.t*x.t, x.f*x.f, x.b*x.b⟩
def fuse (x y : Channels α) : Channels α := ⟨x.n+y.n, x.t+y.t, x.f+y.f, x.b+y.b⟩
def engage (basis : α) (x : Channels α) : Channels α := ⟨basis, basis, x.f, x.b⟩

/-- Native nodes 3→13, 14→15 and 17→25, with identity/forward nodes omitted.
`basis` is the retained path language at the paradox node. -/
def body (x : Channels α) (basis : α) : Channels α :=
  let t₁ := evalT (clink (evalT x))
  let f₁ := evalF (arev (evalF x))
  let rejoined := engage basis (clink (fuse t₁ f₁))
  let t₂ := clink (evalT rejoined)
  let f₂ := evalF (arev (evalF rejoined))
  fuse t₂ f₂

theorem body_B (x : Channels α) (basis : α) : (body x basis).b = x.b ^ 8 := by
  simp [body, evalT, evalF, arev, clink, fuse, engage, pow_succ, mul_assoc]

theorem body_N (x : Channels α) (basis : α) : (body x basis).n = 0 := by
  simp [body, evalT, evalF, arev, clink, fuse, engage]

theorem body_F (x : Channels α) (basis : α) : (body x basis).f = 0 := by
  simp [body, evalT, evalF, arev, clink, fuse, engage]

inductive BTree where
  | source
  | eight (a b c d e f g h : BTree)

def leaves : BTree → Nat
  | .source => 1
  | .eight a b c d e f g h =>
    leaves a + leaves b + leaves c + leaves d + leaves e + leaves f + leaves g + leaves h

theorem leaves_mod_seven (tree : BTree) : leaves tree % 7 = 1 := by
  induction tree with
  | source => decide
  | eight a b c d e f g h ha hb hc hd he hf hg hh =>
    simp [leaves, Nat.add_mod, ha, hb, hc, hd, he, hf, hg, hh]

def comb : Nat → BTree
  | 0 => .source
  | k+1 => .eight .source .source .source .source .source .source .source (comb k)

theorem leaves_comb (k : Nat) : leaves (comb k) = 1 + 7*k := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [comb, leaves, ih]; omega

theorem exact_clock_language (n : Nat) :
    (∃ tree : BTree, leaves tree = n) ↔ ∃ k : Nat, n = 1 + 7*k := by
  constructor
  · rintro ⟨tree, rfl⟩
    have h := leaves_mod_seven tree
    refine ⟨leaves tree / 7, ?_⟩
    omega
  · rintro ⟨k, rfl⟩
    exact ⟨comb k, leaves_comb k⟩

#print axioms body_B
#print axioms exact_clock_language
end Imscribing.Biochem.PeptideLatticeReentry
