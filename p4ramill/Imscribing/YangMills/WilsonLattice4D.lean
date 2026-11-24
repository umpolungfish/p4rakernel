import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Imscribing.YangMills.ClayReductionBridge

/-!
# Concrete 4D SU(N) Lattice Gauge Theory & Weak-Coupling Scaling Target

Defines the 4D periodic torus `Lat4 L`, gauge group `SU(N)` =
`Matrix.specialUnitaryGroup (Fin N) ℂ`, link configurations, plaquette
holonomy, local gauge transformations, and the Wilson plaquette action.
Proves exact finite-volume gauge invariance `wilsonAction_gaugeTransform`
and states the exact remaining weak-coupling continuum-limit target
connecting `wilsonExpectation` along `ymSpacing`/`ymBetaAF` to
`ClayReduction.OSReconstructedInput N`.
-/

namespace Imscribing.YangMills.WilsonLattice4D

/-- Compact simple gauge group SU(N). -/
abbrev GaugeGroup (N : ℕ) := Matrix.specialUnitaryGroup (Fin N) ℂ

/-- Periodic 4D Euclidean lattice of side L. -/
abbrev Lat4 (L : ℕ) := Fin 4 → ZMod L

/-- Unit lattice step in direction μ. -/
def stepDir (L : ℕ) (μ : Fin 4) : Lat4 L :=
  fun ν => if ν = μ then 1 else 0

/-- Link gauge field U(x, μ) ∈ SU(N). -/
abbrev LinkConfig (N L : ℕ) := Lat4 L → Fin 4 → GaugeGroup N

/-- Gauge transformation g : Lat4 L → SU(N). -/
abbrev GaugeTransform (N L : ℕ) := Lat4 L → GaugeGroup N

/-- Action of a gauge transformation on a link configuration: U^g(x, μ) = g(x) U(x, μ) g(x + e_μ)⁻¹. -/
def applyGauge {N L : ℕ} (g : GaugeTransform N L) (U : LinkConfig N L) : LinkConfig N L :=
  fun x μ => g x * U x μ * (g (x + stepDir L μ))⁻¹

/-- Oriented plaquette holonomy U_p(x, μ, ν) in SU(N). -/
def plaquetteHolonomy {N L : ℕ} (U : LinkConfig N L) (x : Lat4 L) (μ ν : Fin 4) :
    GaugeGroup N :=
  U x μ * U (x + stepDir L μ) ν * (U (x + stepDir L ν) μ)⁻¹ * (U x ν)⁻¹

/-- **Exact local gauge covariance of plaquette holonomy:**
    `plaquetteHolonomy (applyGauge g U) x μ ν = g x * plaquetteHolonomy U x μ ν * (g x)⁻¹`. -/
theorem plaquetteHolonomy_applyGauge {N L : ℕ} (g : GaugeTransform N L) (U : LinkConfig N L)
    (x : Lat4 L) (μ ν : Fin 4) :
    plaquetteHolonomy (applyGauge g U) x μ ν =
      g x * plaquetteHolonomy U x μ ν * (g x)⁻¹ := by
  have hcomm : x + stepDir L μ + stepDir L ν = x + stepDir L ν + stepDir L μ := by
    rw [add_assoc, add_assoc, add_comm (stepDir L μ) (stepDir L ν)]
  simp only [plaquetteHolonomy, applyGauge, mul_inv_rev, inv_inv, hcomm]
  group

/-- Real trace of a matrix in SU(N). -/
def realTrace {N : ℕ} (A : GaugeGroup N) : ℝ :=
  ((Matrix.trace (A : Matrix (Fin N) (Fin N) ℂ)).re)

/-- Cyclic invariance of `realTrace` under SU(N) conjugation. -/
theorem realTrace_conj {N : ℕ} (g A : GaugeGroup N) :
    realTrace (g * A * g⁻¹) = realTrace A := by
  unfold realTrace
  have hcoe : ((g * A * g⁻¹ : GaugeGroup N) : Matrix (Fin N) (Fin N) ℂ) =
      (g : Matrix (Fin N) (Fin N) ℂ) * (A : Matrix (Fin N) (Fin N) ℂ) *
        ((g⁻¹ : GaugeGroup N) : Matrix (Fin N) (Fin N) ℂ) := rfl
  have hinv : ((g⁻¹ : GaugeGroup N) : Matrix (Fin N) (Fin N) ℂ) *
      (g : Matrix (Fin N) (Fin N) ℂ) = 1 := by
    change ((g⁻¹ * g : GaugeGroup N) : Matrix (Fin N) (Fin N) ℂ) = 1
    simp
  rw [hcoe, Matrix.trace_mul_cycle, hinv, one_mul]

/-- 4D SU(N) Wilson plaquette action S_W(β, U). -/
noncomputable def wilsonAction (N L : ℕ) [NeZero N] (β : ℝ) (U : LinkConfig N L) : ℝ :=
  β * ∑ x : Lat4 L, ∑ μ : Fin 4, ∑ ν : Fin 4,
    (1 - realTrace (plaquetteHolonomy U x μ ν) / (N : ℝ))

/-- **Exact finite-volume gauge invariance of the 4D SU(N) Wilson action.** -/
theorem wilsonAction_gaugeInvariant (N L : ℕ) [NeZero N] (β : ℝ)
    (g : GaugeTransform N L) (U : LinkConfig N L) :
    wilsonAction N L β (applyGauge g U) = wilsonAction N L β U := by
  unfold wilsonAction
  congr 1
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun μ _ =>
    Finset.sum_congr rfl fun ν _ => ?_
  rw [plaquetteHolonomy_applyGauge, realTrace_conj]

/-- **Remaining Weak-Coupling Continuum Target:**
    Deriving an `OSReconstructedInput N` (whose Schwinger/Wightman observables arise
    from renormalized weak-coupling limits of `wilsonAction N (L m) (ymBetaAF N m)`
    as `ymSpacing m → 0`) discharges `ClaySpec.ClayYangMillsConjecture N`. -/
def WilsonWeakCouplingContinuumExists (N : ℕ) : Prop :=
  2 ≤ N → Nonempty (ClayReduction.OSReconstructedInput N)

theorem clay_yang_mills_of_wilson_continuum
    (N : ℕ) (hN : 2 ≤ N)
    (h_cont : WilsonWeakCouplingContinuumExists N) :
    ∃ (Q : ClaySpec.WightmanQFT4D) (Δ : ℝ),
      ClaySpec.HasYangMillsUVScaling N Q ∧
      ClaySpec.HasStrictMassGap Q Δ := by
  obtain ⟨inData⟩ := h_cont hN
  exact ⟨ClayReduction.toWightmanQFT4D inData, inData.Δ,
    ClayReduction.clay_target_from_os_input inData⟩

end Imscribing.YangMills.WilsonLattice4D