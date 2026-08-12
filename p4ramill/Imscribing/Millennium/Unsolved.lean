/-
Unsolved.lean — open problems, stated so that each says its problem.

The catalogue this comes from (`ig-docs/UNSOLVED.md`) does not compile: it mixes
Lean 3 syntax with Lean 4, names modules and constants Mathlib does not have, and
several of its statements are false or trivially true as written. A statement
that cannot be elaborated has not been checked by anything, and one that a
one-liner discharges is worse than absent, because it reads as a formalisation.

The discipline here is the corpus's: an open problem is a `def … : Prop`, it
states what the problem says, and nothing downstream assumes it without taking it
as a hypothesis. Where the original said something else, the docstring says what
it said.

Author: Lando⊗⊙perator
-/
import Mathlib

namespace Unsolved

open Filter

/-! ## Algebra -/

/-- **Casas-Alvero.** A monic polynomial over a characteristic-zero field that
shares a root with each of its first `d−1` derivatives is a `d`-th power of a
linear factor. The original asked that each derivative VANISH AT ZERO, which is a
condition on the point `0` rather than on a shared root, and is satisfied by
`X^d` alone among the polynomials it was meant to characterise. -/
def CasasAlvero : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (f : Polynomial K) (d : ℕ),
    f.natDegree = d → 1 ≤ d → f.Monic →
    (∀ i : ℕ, 1 ≤ i → i ≤ d - 1 →
      ∃ r : K, f.IsRoot r ∧ (Polynomial.derivative^[i] f).IsRoot r) →
    ∃ b : K, f = (Polynomial.X - Polynomial.C b) ^ d

/-- **Hadamard.** A Hadamard matrix exists at every order divisible by four. -/
def Hadamard : Prop :=
  ∀ k : ℕ, 0 < k → ∃ H : Matrix (Fin (4 * k)) (Fin (4 * k)) ℤ,
    (∀ i j, H i j = 1 ∨ H i j = -1) ∧
    H * H.transpose = (4 * k : ℤ) • (1 : Matrix (Fin (4 * k)) (Fin (4 * k)) ℤ)

/-- **The inverse Galois problem** over the rationals: every finite group is a
Galois group of some extension of `ℚ`. Stated over `ℚ` rather than over an
unnamed characteristic-zero field, since over a general such field the answer is
known and the problem is about `ℚ`. -/
def InverseGalois : Prop :=
  ∀ (G : Type) [Group G] [Finite G],
    ∃ (L : Type) (_ : Field L) (_ : Algebra ℚ L),
      Nonempty ((L ≃ₐ[ℚ] L) ≃* G)

/-! ## Analysis -/

/-- **The invariant subspace problem**, in the direction it is open: every
bounded operator on an infinite-dimensional separable Hilbert space has a
nontrivial closed invariant subspace. The original asserted the existence of an
operator WITHOUT one, over every Hilbert space including the finite-dimensional
ones, where every operator has an eigenvector — so it was false as written. -/
def InvariantSubspace : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H],
    ∀ T : H →L[ℂ] H, ∃ V : Submodule ℂ H,
      V ≠ ⊥ ∧ V ≠ ⊤ ∧ ∀ x ∈ V, T x ∈ V

/-- **Sendov.** Every root of a polynomial with all roots in the closed unit disc
has a critical point within distance one. -/
def Sendov : Prop :=
  ∀ p : Polynomial ℂ, 2 ≤ p.natDegree →
    (∀ z : ℂ, p.IsRoot z → ‖z‖ ≤ 1) →
    ∀ a : ℂ, p.IsRoot a →
      ∃ b : ℂ, (Polynomial.derivative p).IsRoot b ∧ ‖a - b‖ ≤ 1

/-- The Collatz step. -/
def collatz (n : ℕ) : ℕ := if n % 2 = 0 then n / 2 else 3 * n + 1

/-- **Collatz.** Every positive integer reaches one. -/
def Collatz : Prop := ∀ n : ℕ, 0 < n → ∃ k : ℕ, collatz^[k] n = 1

/-! ## Combinatorics -/

/-- The distance from a real to the nearest integer. -/
noncomputable def toNearestInt (x : ℝ) : ℝ := |x - round x|

/-- **The lonely runner.** With `k` runners at distinct constant speeds, each is
at some time at distance at least `1/k` from every other on the circular track.
The original asked for SOME integer `z` with `|Δ − z| ≥ 1/k`, which any large `z`
satisfies — the condition has to be on the distance to the NEAREST integer. -/
def LonelyRunner : Prop :=
  ∀ (k : ℕ) (speeds : Fin k → ℝ), 0 < k →
    (∀ i j, i ≠ j → speeds i ≠ speeds j) →
    ∀ i : Fin k, ∃ t : ℝ,
      ∀ j : Fin k, j ≠ i → (1 : ℝ) / k ≤ toNearestInt (t * (speeds i - speeds j))

/-- **Union-closed sets.** A finite family closed under union, with a nonempty
member, has an element lying in at least half of its sets. The original used
`Set.filter`, which does not exist, and offered an alternative disjunct that a
family of one set satisfies vacuously. -/
def UnionClosed : Prop :=
  ∀ (α : Type) [DecidableEq α] (F : Finset (Finset α)),
    F.Nonempty → (∃ s ∈ F, s.Nonempty) →
    (∀ s ∈ F, ∀ t ∈ F, s ∪ t ∈ F) →
    ∃ x : α, 2 * (F.filter (fun s => x ∈ s)).card ≥ F.card

/-! ## Number theory -/

/-- **Goldbach.** Every even number above two is a sum of two primes. -/
def Goldbach : Prop :=
  ∀ n : ℕ, Even n → 2 < n → ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p + q = n

/-- **Twin primes.** Infinitely many primes `p` with `p + 2` prime. -/
def TwinPrimes : Prop := ∀ N : ℕ, ∃ p : ℕ, N < p ∧ p.Prime ∧ (p + 2).Prime

/-- **Legendre.** A prime between consecutive squares. -/
def Legendre : Prop := ∀ n : ℕ, 0 < n → ∃ p : ℕ, n ^ 2 < p ∧ p < (n + 1) ^ 2 ∧ p.Prime

/-- The radical of `n`: the product of its distinct prime factors. -/
def rad (n : ℕ) : ℕ := n.primeFactors.prod id

/-- **abc.** For every `ε > 0` there is a constant `C` bounding `c` by
`C · rad(abc)^{1+ε}` on coprime triples. The original wrote `∃ C, C > 0 → …`,
whose `C = 0` instance makes the whole statement hold with nothing proved: an
implication where a conjunction was meant. -/
def ABC : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
    ∀ a b c : ℕ, 0 < a → 0 < b → a + b = c → Nat.Coprime a b →
      (c : ℝ) < C * (rad (a * b * c) : ℝ) ^ (1 + ε)

/-- **The Riemann hypothesis**, over Mathlib's own zeta rather than a series that
diverges where the problem lives: every zero in the critical strip has real part
one half. The original defined zeta by the naive sum, valid only for `Re s > 1`,
and allowed `s.im = 0` as an alternative conclusion, which admits the trivial
zeros. -/
def RiemannHypothesis : Prop :=
  ∀ s : ℂ, riemannZeta s = 0 → 0 < s.re → s.re < 1 → s.re = 1 / 2

/-- A perfect number equals the sum of its proper divisors. -/
def Perfect (n : ℕ) : Prop := ∑ d ∈ Nat.divisors n, d = 2 * n

/-- **Odd perfect numbers.** There are none. -/
def NoOddPerfect : Prop := ¬ ∃ n : ℕ, 0 < n ∧ ¬ Even n ∧ Perfect n

end Unsolved
