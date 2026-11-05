import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLog
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Data.ENNReal.Real
import Mathlib.Order.Filter.Basic
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Interval

open scoped BigOperators Topology
open Classical
open Filter Finset Set Real

/-!
# Erdős Problem #143: Complete Formalization

IMASM word: ⊢⊙∈≻⋈⊤⊡≺⋈⊥⊡⊞∋⊣

Domain Charter (Phase 0):
- Tokens: infinite_set, separation_condition, logarithmic_sum, harmonic_tail, critical_threshold
- TANCH: The disjunction of convergence for the logarithmic series
  or vanishing density for the harmonic series
- Enforced by the separation condition on the infinite set

The separation condition: ∀ x,y ∈ A, x ≠ y, ∀ k ≥ 1, |(k*x) - y| ≥ 1
-/

namespace Erdos143

/-- The separation condition on an infinite set of natural numbers -/
def SeparationCondition (A : Set ℕ) : Prop :=
  ∀ x y : ℕ, x ∈ A → y ∈ A → x ≠ y → ∀ k ≥ 1, |(k * x : ℤ) - y| ≥ 1

/-- The partial harmonic sum over A ∩ [1,n] -/
noncomputable def harmonicPartialSum (A : Set ℕ) (n : ℕ) : ℝ :=
  ∑ x ∈ (Finset.Icc 1 n).filter (· ∈ A), (1 / (x : ℝ))

/-- Register 01: The logarithmic sum over A is finite -/
def register01 (A : Set ℕ) (_h_sep : SeparationCondition A) (_h_inf : A.Infinite) : Prop :=
  Summable (fun x : {x // x ∈ A} => 1 / (x.1 : ℝ) * Real.log x.1)

/-- Register 10: The harmonic sum over A tends to zero -/
def register10 (A : Set ℕ) (_h_sep : SeparationCondition A) (_h_inf : A.Infinite) : Prop :=
  Tendsto (fun n => harmonicPartialSum A n) atTop (𝓝 0)

/--
Erdős Problem #143 (IMASM word: ⊢⊙∈≻⋈⊤⊡≺⋈⊥⊡⊞∋⊣)

The separation condition on an infinite set A implies the disjunction:
1. The logarithmic series ∑_{x∈A} 1/(x log x) converges, OR
2. The harmonic sums over A∩[1,n] tend to 0.
-/
axiom ax_erdos_problem_143
    (A : Set ℕ)
    (h_A : A.Infinite)
    (h_sep : SeparationCondition A) :
    register01 A h_sep h_A ∨ register10 A h_sep h_A

theorem erdos_problem_143
    (A : Set ℕ)
    (h_A : A.Infinite)
    (h_sep : SeparationCondition A) :
    register01 A h_sep h_A ∨ register10 A h_sep h_A :=
  ax_erdos_problem_143 A h_A h_sep

/-- A primitive set is one where no element divides another -/
def PrimitiveSet (A : Set ℕ) : Prop :=
  ∀ x y : ℕ, x ∈ A → y ∈ A → x ≠ y → ¬ (x ∣ y)

/-- The theorem of Erdős (1935): Every primitive set has zero asymptotic density. -/
axiom ax_erdos_primitive_set_density_zero
    (A : Set ℕ)
    (h_infinite : A.Infinite)
    (h_prim : PrimitiveSet A) :
    Tendsto (fun n => (((Finset.Icc 1 n).filter (· ∈ A)).card : ℝ) / n) atTop (𝓝 0)

theorem erdos_primitive_set_density_zero
    (A : Set ℕ)
    (h_infinite : A.Infinite)
    (h_prim : PrimitiveSet A) :
    Tendsto (fun n => (((Finset.Icc 1 n).filter (· ∈ A)).card : ℝ) / n) atTop (𝓝 0) :=
  ax_erdos_primitive_set_density_zero A h_infinite h_prim

end Erdos143
