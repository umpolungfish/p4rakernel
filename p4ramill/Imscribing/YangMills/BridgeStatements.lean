/-
BridgeStatements.lean — the nine formal target properties for the
strong-coupling infinite-volume bridge, expressed as Lean definitions.

These are schematic props: the nonstandard predicates are opaque, and the
Schwinger functional S is opaque.  They record the exact shape of each
required property (SO(4) invariance, translation invariance, clustering,
OS reflection positivity, nonvanishing connected four-point function,
nontriviality, hermiticity, lattice-continuum convergence, vacuum cyclicity)
so that each can be discharged against the corpus's finite-volume lemmas.
-/
import Mathlib

open scoped BigOperators

namespace YangMills

/-! ## Carrier -/

abbrev BridgeConfig (n : ℕ) := Fin n → EuclideanSpace ℝ (Fin 4)

opaque BridgeS : (n : ℕ) → BridgeConfig n → ℝ
opaque BridgeSconn : BridgeConfig 4 → ℝ
opaque Theta : ∀ {n : ℕ}, BridgeConfig n → BridgeConfig n

/-! ## 1. SO(4) rotation invariance -/

def SO4RotationInvariance : Prop :=
  ∀ (n : ℕ) (R : Matrix.orthogonalGroup (Fin 4) ℝ),
    ∀ x : BridgeConfig n,
      BridgeS n (fun i => (WithLp.equiv 2 (Fin 4 → ℝ)).symm ((R : Matrix (Fin 4) (Fin 4) ℝ).mulVec (x i))) = BridgeS n x

/-! ## 2. Translation invariance -/

def TranslationInvariance : Prop :=
  ∀ (n : ℕ) (a : EuclideanSpace ℝ (Fin 4)) (x : BridgeConfig n),
    BridgeS n (fun i => x i + a) = BridgeS n x

/-! ## 3. Cluster property with exponential decay -/

def ClusterProperty (Δ : ℝ) : Prop :=
  ∀ n m : ℕ, ∃ C : ℝ, 0 < C ∧
    ∀ (x : BridgeConfig n) (y : BridgeConfig m) (R : ℝ), 0 ≤ R →
      (∀ i j, R ≤ dist (x i) (y j)) →
      |BridgeS (n + m) (Fin.append x y) - BridgeS n x * BridgeS m y| ≤
        C * Real.exp (-Δ * R)

/-! ## 4. Osterwalder–Schrader reflection positivity -/

def OSReflectionPositivity : Prop :=
  ∀ (k : ℕ) (n : Fin k → ℕ) (x : ∀ i, BridgeConfig (n i)) (c : Fin k → ℂ),
    0 ≤ Complex.re (∑ i, ∑ j,
      c i * starRingEnd ℂ (c j) *
        (BridgeS (n i + n j) (Fin.append (Theta (x i)) (x j)) : ℂ))

/-! ## 5. Nonvanishing connected four-point function -/

def NonvanishingConnectedFourPoint : Prop :=
  ∃ x : BridgeConfig 4, BridgeSconn x ≠ 0

/-! ## 6. Nontriviality of Schwinger functions -/

def NontrivialitySchwinger : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∃ x : BridgeConfig n, BridgeS n x ≠ 0

/-! ## 7. Hermitian symmetry of the reflection-positivity kernel -/

def reflectionKernel {n m : ℕ} (x : BridgeConfig n) (y : BridgeConfig m) : ℂ :=
  BridgeS (n + m) (Fin.append (Theta x) y)

def KernelHermitian : Prop :=
  ∀ (n m : ℕ) (x : BridgeConfig n) (y : BridgeConfig m),
    reflectionKernel x y = starRingEnd ℂ (reflectionKernel y x)

/-! ## 8. Lattice–continuum limit convergence -/

opaque BridgeSlatt : ℝ → (n : ℕ) → BridgeConfig n → ℝ
opaque BridgeSinf : (n : ℕ) → BridgeConfig n → ℝ

def LatticeContinuumLimit : Prop :=
  ∀ n : ℕ, ∀ ε : ℝ, 0 < ε → ∃ M : ℝ, ∀ β : ℝ, M ≤ β →
    ∀ x : BridgeConfig n, |BridgeSlatt β n x - BridgeSinf n x| < ε

/-! ## 9. Vacuum cyclicity and the physical Hilbert space -/

variable
  (Hphys : Type*) [NormedAddCommGroup Hphys] [InnerProductSpace ℂ Hphys] [CompleteSpace Hphys]
  (U : ∀ g : Unit, Hphys →L[ℂ] Hphys)
  (phi : ∀ n : ℕ, BridgeConfig n → Hphys →L[ℂ] Hphys)
  (Omega : Hphys)

def VacuumCyclicity : Prop :=
  closure ((Submodule.span ℂ
    { v : Hphys | ∃ (_g : Unit) (n : ℕ) (x : BridgeConfig n),
        v = U _g (phi n x Omega) }) : Set Hphys) = Set.univ

end YangMills
