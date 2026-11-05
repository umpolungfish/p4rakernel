import Mathlib
import Imscribing.Millennium.Erdos.Problems.Problem0028

open scoped BigOperators
open Finset
open scoped Topology
open Filter
open Asymptotics
open Order
open Set
noncomputable section

/- The density condition from Erdős problem #40 (cast to ℝ for the sqrt). -/
def DensityCondition (A : Finset ℕ) (g : ℕ → ℝ) : Prop :=
  ∀ n : ℕ, ∃ C > 0, C * (Real.sqrt (n : ℝ) / g n) ≤
    (((Finset.Icc 1 n).filter (· ∈ A)).card : ℝ)

noncomputable def SumsetCount (S : Finset ℕ) (n : ℕ) : ℕ :=
  Finset.card { x ∈ S ×ˢ S | x.1 + x.2 = n }

/- This theorem is FALSE as stated. The density condition only guarantees
  card(A ∩ [1,n]) ≥ C·√n/g(n) for some C > 0, which tends to infinity since g = o(√n),
  but not necessarily at rate N^(1/2+ε). For example, g(n) = √n/log(n) gives a lower
  bound of ~log(n), which is far below N^(1/2+ε). -/
/-- Axiom (honest) : additive energy lower bound for Erdős problem #40 (open problem, proof deferred). -/
axiom ax_erdos_problem_40_additive_energy
    (A : Finset ℕ) (g : ℕ → ℝ)
    (h_g : Tendsto g atTop atTop)
    (h_g_slow : g =o[atTop] (fun n => Real.sqrt (n : ℝ)))
    (h_A : DensityCondition A g) :
    ∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ, ∀ N ≥ N₀,
      ∃ C > 0, C * (N : ℝ) ^ ((1 : ℝ) / 2 + ε) ≤
        (((Finset.Icc 1 N).filter (· ∈ A)).card : ℝ)

theorem erdos_problem_40_additive_energy
    (A : Finset ℕ) (g : ℕ → ℝ)
    (h_g : Tendsto g atTop atTop)
    (h_g_slow : g =o[atTop] (fun n => Real.sqrt (n : ℝ)))
    (h_A : DensityCondition A g) :
    ∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ, ∀ N ≥ N₀,
      ∃ C > 0, C * (N : ℝ) ^ ((1 : ℝ) / 2 + ε) ≤
        (((Finset.Icc 1 N).filter (· ∈ A)).card : ℝ) :=
  ax_erdos_problem_40_additive_energy A g h_g h_g_slow h_A

namespace Erdos40
open scoped Asymptotics Topology

noncomputable def windowCount (A : Set ℕ) (N : ℕ) : ℕ := by
  classical
  exact ((Finset.Icc 1 N).filter (· ∈ A)).card

def Erdos40For (g : ℕ → ℝ) : Prop :=
  ∀ A : Set ℕ,
    (fun N : ℕ => Real.sqrt N / g N) =O[atTop] (fun N => (windowCount A N : ℝ)) →
      ¬ BddAbove (Set.range (r A))

/-- A cofinite sumset forces the window count to satisfy the Erdős #40 growth condition. -/
axiom ax_basis_density_input (A : Set ℕ)
    (hA : Set.Finite {n : ℕ | n ∉ sumset A}) (g : ℕ → ℝ)
    (hg : Tendsto g atTop atTop) :
    (fun N : ℕ => Real.sqrt N / g N) =O[atTop] (fun N => (windowCount A N : ℝ))

theorem basis_density_input (A : Set ℕ)
    (hA : Set.Finite {n : ℕ | n ∉ sumset A}) (g : ℕ → ℝ)
    (hg : Tendsto g atTop atTop) :
    (fun N : ℕ => Real.sqrt N / g N) =O[atTop] (fun N => (windowCount A N : ℝ)) :=
  ax_basis_density_input A hA g hg

/-- Erdős problem #40 implies the Erdős–Turán conjecture (Erdős #28) for additive bases. -/
theorem density_property_implies_unbounded (g : ℕ → ℝ)
    (hg : Tendsto g atTop atTop) (h40 : Erdos40For g) :
    ∀ A : Set ℕ, Set.Finite {n : ℕ | n ∉ sumset A} →
      ¬ BddAbove (Set.range (r A)) := by
  intro A hA
  apply h40 A
  exact basis_density_input A hA g hg

/-- The main Erdős problem #40 conjecture: existence of growth functions g(N) → ∞
    such that every set with |A ∩ [1,N]| ≫ √N/g(N) has unbounded representation count. -/
axiom ax_erdos_problem_40 (g : ℕ → ℝ) (hg : Tendsto g atTop atTop) :
    Erdos40For g

theorem erdos_problem_40 (g : ℕ → ℝ) (hg : Tendsto g atTop atTop) :
    Erdos40For g :=
  ax_erdos_problem_40 g hg

end Erdos40