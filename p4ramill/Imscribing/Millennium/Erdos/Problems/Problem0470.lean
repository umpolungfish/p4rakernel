import Mathlib

/-!
# Erdős problem #470

Prize: 0.  Status as catalogued: **OPEN**.

*Reference:* [erdosproblems.com/470](https://www.erdosproblems.com/470)

Weird numbers (Benkoski–Erdős):
A natural number n is weird if it is abundant but not pseudoperfect.
Are there any odd weird numbers?
Are there infinitely many primitive weird numbers?
-/

open scoped BigOperators Classical

noncomputable section

namespace Erdos470

/-- Proper divisors of n. -/
def properDivisors (n : ℕ) : Finset ℕ :=
  (Finset.Ico 1 n).filter (fun d => d ∣ n)

/-- A number is abundant if the sum of its proper divisors exceeds n. -/
def IsAbundant (n : ℕ) : Prop :=
  ∑ d ∈ properDivisors n, d > n

/-- A number is pseudoperfect if some subset of proper divisors sums to n. -/
def IsPseudoperfect (n : ℕ) : Prop :=
  ∃ S ⊆ properDivisors n, ∑ d ∈ S, d = n

/-- A number is weird if it is abundant and not pseudoperfect. -/
def IsWeird (n : ℕ) : Prop :=
  IsAbundant n ∧ ¬ IsPseudoperfect n

/-- A weird number is primitive if no proper divisor is weird. -/
def IsPrimitiveWeird (n : ℕ) : Prop :=
  IsWeird n ∧ ∀ d ∈ properDivisors n, ¬ IsWeird d

/-- The Erdős problem #470 statement: existence of odd weird numbers, or infinitely many primitive weird. -/
def ErdosProblem470Statement : Prop :=
  (∃ n : ℕ, Odd n ∧ IsWeird n) ∨ {n : ℕ | IsPrimitiveWeird n}.Infinite

/-- Axiom (honest) : Erdős problem #470 (open problem). -/
axiom ax_erdos_problem_470 : ErdosProblem470Statement

theorem erdos_problem_470 : ErdosProblem470Statement :=
  ax_erdos_problem_470

end Erdos470
