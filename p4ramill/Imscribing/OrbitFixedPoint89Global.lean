import Imscribing.OrbitFixedPoint89

open scoped BigOperators

noncomputable section

namespace Imscribing.OrbitFixedPoint89.Global

variable (initial : PhaseState)

/-!
# Global Two-Sided Orbital-History Fixed-Point Solver

The complete orbital unknown is

    σ : ℝ → PhaseState

The time domain is the entire real line. There is no distinguished
terminal time, and negative-time history is included in the same object.

The global Volterra operator is

    T(σ)(t).pos = x₀ + ∫₀ᵗ vσ(τ) dτ

    T(σ)(t).vel = v₀ + ∫₀ᵗ a(σ(τ)) dτ

A global orbital history is a fixed point of this operator.

The integration convention handles both positive and negative t.
The force law is the Newtonian acceleration already defined in
OrbitFixedPoint89.

Picard iteration acts on the entire history function, not on an
individual body or a finite sequence of time steps.

The solver certificate records the global fixed point, its
Newtonian differential law, and pointwise convergence of its
whole-history Picard approximations.
-/

/-! ## 1. Global history space -/

/-- A complete two-sided physical history. -/
abbrev GlobalHistory := Orbit

/-- Constant initial history, used as the first Picard approximation. -/
def initialHistory (initial : PhaseState) : GlobalHistory :=
  fun _ => initial

/-! ## 2. Global integral evolution operator -/

/-- The Volterra operator on the entire real-time history.

For negative times, interval integration automatically reverses
the integration orientation.
-/
def GlobalVolterraOperator
    (p : ThreeBodyParameters)
    (initial : PhaseState)
    (candidate : GlobalHistory) : GlobalHistory :=
  fun t =>
    { pos := fun i c =>
        initial.pos i c +
          ∫ τ in (0 : ℝ)..t, (candidate τ).vel i c
      vel := fun i c =>
        initial.vel i c +
          ∫ τ in (0 : ℝ)..t, accel p (candidate τ) i c }

/-- The global history is a fixed point of its own integral evolution. -/
def IsGlobalIntegralFixedPoint
    (p : ThreeBodyParameters)
    (initial : PhaseState)
    (σ : GlobalHistory) : Prop :=
  ∀ t, σ t = GlobalVolterraOperator p initial σ t

/-! ## 3. Exact fixed-point equations -/

/-- Position equation of the global fixed point. -/
theorem globalFixedPoint_position
    (p : ThreeBodyParameters)
    (initial : PhaseState)
    (σ : GlobalHistory)
    (h : IsGlobalIntegralFixedPoint p initial σ)
    (t : ℝ) (i : Body) (c : Fin 3) :
    (σ t).pos i c =
      initial.pos i c +
        ∫ τ in (0 : ℝ)..t, (σ τ).vel i c := by
  have heq := congrArg
    (fun s : PhaseState => s.pos i c) (h t)
  simpa [GlobalVolterraOperator] using heq

/-- Velocity equation of the global fixed point. -/
theorem globalFixedPoint_velocity
    (p : ThreeBodyParameters)
    (initial : PhaseState)
    (σ : GlobalHistory)
    (h : IsGlobalIntegralFixedPoint p initial σ)
    (t : ℝ) (i : Body) (c : Fin 3) :
    (σ t).vel i c =
      initial.vel i c +
        ∫ τ in (0 : ℝ)..t, accel p (σ τ) i c := by
  have heq := congrArg
    (fun s : PhaseState => s.vel i c) (h t)
  simpa [GlobalVolterraOperator] using heq

/-- The global fixed point recovers its prescribed initial position. -/
theorem globalFixedPoint_initial_position
    (p : ThreeBodyParameters)
    (initial : PhaseState)
    (σ : GlobalHistory)
    (h : IsGlobalIntegralFixedPoint p initial σ)
    (i : Body) (c : Fin 3) :
    (σ 0).pos i c = initial.pos i c := by
  have heq := globalFixedPoint_position p initial σ h 0 i c
  simpa using heq

/-- The global fixed point recovers its prescribed initial velocity. -/
theorem globalFixedPoint_initial_velocity
    (p : ThreeBodyParameters)
    (initial : PhaseState)
    (σ : GlobalHistory)
    (h : IsGlobalIntegralFixedPoint p initial σ)
    (i : Body) (c : Fin 3) :
    (σ 0).vel i c = initial.vel i c := by
  have heq := globalFixedPoint_velocity p initial σ h 0 i c
  simpa using heq

/-! ## 4. Global two-sided Picard iteration -/

/-- One Picard update acts on the complete real-time history. -/
def GlobalPicardStep
    (p : ThreeBodyParameters)
    (initial : PhaseState)
    (σ : GlobalHistory) : GlobalHistory :=
  GlobalVolterraOperator p initial σ

/-- Successive whole-history Picard approximations. -/
def GlobalPicardIteration
    (p : ThreeBodyParameters)
    (initial : PhaseState) :
    ℕ → GlobalHistory
  | 0 => initialHistory initial
  | n + 1 =>
      GlobalPicardStep p initial
        (GlobalPicardIteration p initial n)

/-- Initial whole-history approximation. -/
theorem globalPicard_zero
    (p : ThreeBodyParameters)
    (initial : PhaseState) :
    GlobalPicardIteration p initial 0 =
      initialHistory initial := rfl

/-- Every Picard iteration applies the same complete-history operator. -/
theorem globalPicard_successor
    (p : ThreeBodyParameters)
    (initial : PhaseState)
    (n : ℕ) :
    GlobalPicardIteration p initial (n + 1) =
      GlobalVolterraOperator p initial
        (GlobalPicardIteration p initial n) := rfl

/-! ## 5. Pointwise convergence on the complete real-time domain -/

/-- Position convergence of whole-history Picard iteration. -/
def PicardPositionConverges
    (p : ThreeBodyParameters)
    (initial : PhaseState)
    (σ : GlobalHistory) : Prop :=
  ∀ t i c,
    Filter.Tendsto
      (fun n => (GlobalPicardIteration p initial n t).pos i c)
      Filter.atTop
      (nhds ((σ t).pos i c))

/-- Velocity convergence of whole-history Picard iteration. -/
def PicardVelocityConverges
    (p : ThreeBodyParameters)
    (initial : PhaseState)
    (σ : GlobalHistory) : Prop :=
  ∀ t i c,
    Filter.Tendsto
      (fun n => (GlobalPicardIteration p initial n t).vel i c)
      Filter.atTop
      (nhds ((σ t).vel i c))

/-- Convergence of the complete orbital history, coordinatewise
at every real time, for every body and spatial coordinate. -/
def GlobalPicardConverges
    (p : ThreeBodyParameters)
    (initial : PhaseState)
    (σ : GlobalHistory) : Prop :=
  PicardPositionConverges p initial σ ∧
  PicardVelocityConverges p initial σ

/-! ## 6. Global orbital solver certificate -/

/-- A certified global orbital solution.

The history is a two-sided function on all of ℝ. It satisfies the
Newtonian differential law and the global integral fixed-point
equation. Its Picard approximations converge at every time and
coordinate.

The convergence property is an explicit certificate, not an
unstated assumption about arbitrary Newtonian initial data.
-/
structure GlobalOrbitSolverCertificate
    (p : ThreeBodyParameters)
    (initial : PhaseState) where

  history : GlobalHistory

  newtonian : IsNewtonianOrbit p history

  fixedPoint :
    IsGlobalIntegralFixedPoint p initial history

  picardPosition :
    PicardPositionConverges p initial history

  picardVelocity :
    PicardVelocityConverges p initial history

/-! ## 7. Global solver output -/

/-- The selected global two-sided orbital history. -/
def solveGlobalOrbit
    (C : GlobalOrbitSolverCertificate p initial) :
    GlobalHistory :=
  C.history

/-- The solver output satisfies the global fixed-point equation. -/
theorem solveGlobalOrbit_fixedPoint
    (C : GlobalOrbitSolverCertificate p initial) :
    IsGlobalIntegralFixedPoint p initial
      (solveGlobalOrbit initial C) :=
  C.fixedPoint

/-- The solver output satisfies the Newtonian differential law. -/
theorem solveGlobalOrbit_newtonian
    (C : GlobalOrbitSolverCertificate p initial) :
    IsNewtonianOrbit p (solveGlobalOrbit initial C) :=
  C.newtonian

/-- The solver output is recovered at time zero. -/
theorem solveGlobalOrbit_initial_state
    (C : GlobalOrbitSolverCertificate p initial)
    (i : Body) (c : Fin 3) :
    (solveGlobalOrbit initial C 0).pos i c =
      initial.pos i c ∧
    (solveGlobalOrbit initial C 0).vel i c =
      initial.vel i c := by
  exact
    ⟨globalFixedPoint_initial_position
        p initial C.history C.fixedPoint i c,
     globalFixedPoint_initial_velocity
        p initial C.history C.fixedPoint i c⟩

/-- Position Picard convergence for the solver output. -/
theorem solveGlobalOrbit_position_converges
    (C : GlobalOrbitSolverCertificate p initial) :
    PicardPositionConverges p initial
      (solveGlobalOrbit initial C) :=
  C.picardPosition

/-- Velocity Picard convergence for the solver output. -/
theorem solveGlobalOrbit_velocity_converges
    (C : GlobalOrbitSolverCertificate p initial) :
    PicardVelocityConverges p initial
      (solveGlobalOrbit initial C) :=
  C.picardVelocity

/-- Complete two-sided global orbit solution theorem. -/
theorem global_two_sided_orbit_solution
    (C : GlobalOrbitSolverCertificate p initial) :
    IsNewtonianOrbit p (solveGlobalOrbit initial C) ∧
    IsGlobalIntegralFixedPoint p initial (solveGlobalOrbit initial C) ∧
    GlobalPicardConverges p initial (solveGlobalOrbit initial C) := by
  exact
    ⟨C.newtonian, C.fixedPoint,
      ⟨C.picardPosition, C.picardVelocity⟩⟩

/-! ## 8. The two-sided time-translation action -/

/-- Translating a certified global Newtonian history produces
another certified Newtonian history, with no preferred time origin. -/
theorem global_tail_is_newtonian
    (p : ThreeBodyParameters)
    (σ : GlobalHistory)
    (hσ : IsNewtonianOrbit p σ)
    (shift : ℝ) :
    IsNewtonianOrbit p (σ.tail shift) :=
  tail_is_newtonian p σ hσ shift

/-- Tail composition is the additive action of the real-time group. -/
theorem global_tail_composition
    (σ : GlobalHistory) (s t : ℝ) :
    (σ.tail s).tail t = σ.tail (s + t) :=
  Orbit.tail_tail σ s t

/-- Every translated history has an inverse translation. -/
theorem global_tail_inverse
    (σ : GlobalHistory) (t : ℝ) :
    (σ.tail t).tail (-t) = σ :=
  Orbit.self_reference σ t

/-! ## 9. The central global-history result -/

/-- A certified global solution is simultaneously:

* a Newtonian orbit on all real times;
* a fixed point of its global integral evolution;
* the limit of whole-history Picard iteration;
* invariant as a class of solutions under real-time translation.

The orbital history is the fixed-point object, not a finite
sequence initialized at a selected terminal boundary.
-/
theorem global_orbital_history_fixed_point
    (C : GlobalOrbitSolverCertificate p initial) :
    IsNewtonianOrbit p (solveGlobalOrbit initial C) ∧
    IsGlobalIntegralFixedPoint p initial (solveGlobalOrbit initial C) ∧
    GlobalPicardConverges p initial (solveGlobalOrbit initial C) ∧
    (∀ t : ℝ,
      IsNewtonianOrbit p
        ((solveGlobalOrbit initial C).tail t)) := by
  refine ⟨C.newtonian, C.fixedPoint,
    ⟨C.picardPosition, C.picardVelocity⟩, ?_⟩
  intro t
  exact tail_is_newtonian p C.history C.newtonian t

end Imscribing.OrbitFixedPoint89.Global