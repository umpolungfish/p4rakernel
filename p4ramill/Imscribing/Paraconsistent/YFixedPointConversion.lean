import Imscribing.Paraconsistent.TemporalSemantics
import Imscribing.Paraconsistent.CombinatoryFixedPoint
import Imscribing.Paraconsistent.CombinatoryDynamics
import Imscribing.Paraconsistent.CombinatoryReentry

/-!
P7 strengthening (2026-11-18).
Three fixed-point notions are proved in separate modules:
  (1) Temporal.Semantics.Combinators.yUnfolding_stable_is_fixed : stability ⇒ f x = x,
  (2) CombinatoryFixedPoint.Certificate.fixed : table.interpret point = point,
  (3) CombinatoryReentry.Y_fixedpoint : Conversion (Y f) (f (Y f)).
They are at different types, so this module gives CONVERSIONS, not a false
equality: a certified point converts to the Signal fixed point, the Clock reads
its own feedback orbit as a yUnfolding, and the Term-level Y equation is the
source of the Steps reduction. No new axiom.
-/
namespace Imscribing.Paraconsistent.YFixedPointConversion

open Imscribing.Paraconsistent.Temporal.Semantics
open Imscribing.Paraconsistent.Temporal.Semantics.Combinators
open Imscribing.Paraconsistent.CombinatoryFixedPoint
open Imscribing.Paraconsistent.CombinatoryDynamics
open Imscribing.Paraconsistent.CombinatoryReentry
local infixl:70 " @@ " => Term.app

/-- A certified fixed point converts to the Signal fixed point: the certificate's
    orbit is a yUnfolding whose stable tail equals the certified point. -/
theorem certificate_fixed_from_signal_stability {program : Term}
    (cert : Certificate program) (tick : Nat) :
    cert.table.interpret cert.point = cert.point := by
  have hs : cert.orbit (tick + 4 + 1) = cert.orbit (tick + 4) := by
    rw [cert.orbit_settled (tick + 1), cert.orbit_settled tick]
  have hf := yUnfolding_stable_is_fixed cert.table.interpret Lean.Sixteen3.none
      (tick + 4) hs
  have hsettled : cert.orbit (tick + 4) = cert.point := cert.orbit_settled tick
  -- hf fixes the settled approximant; rewriting it to the certified point gives the claim
  rw [← hsettled]
  simpa [Certificate.orbit, yUnfolding] using hf

/-- The certified fixed point and the Signal fixed point agree on the point. -/
theorem certificate_fixed_agrees_with_signal {program : Term}
    (cert : Certificate program) :
    (cert.table.interpret cert.point = cert.point) ∧
    cert.orbit (4) = cert.point := by
  exact ⟨cert.fixed, cert.orbit_settled 0⟩

/-- The Clock's readout is the same yUnfolding signal: read = orbit = feedback.
    This is the relay between the certified fixed point and a native tick. -/
theorem clock_read_is_yUnfolding {program : Term} {seed : Lean.Sixteen3}
    (clock : Clock program seed) (tick : Nat) :
    clock.read tick = yUnfolding clock.cycle.table.interpret seed tick := by
  rw [Clock.read_eq_orbit]
  rfl

/-- A certified point is a program fixed point; this is the Sixteen3 equality
    converted into an executing step. -/
theorem certified_point_is_program_fixed {program : Term}
    (cert : Certificate program) :
    Steps (program @@ .datum cert.point) (.datum cert.point) :=
  cert.program_fixed

/-- The Term-level Y equation is a Conversion, not the value-level Eq above.
    Its role is to produce the reduction steps that the certificate checks. -/
theorem y_equation_is_source_of_reduction (x : Term) :
    Conversion (Y @@ (.k @@ x)) (.k @@ x @@ (Y @@ (.k @@ x))) ∧
    Steps (Y @@ (.k @@ x)) x := by
  exact ⟨Y_fixedpoint (.k @@ x), Y_constant x⟩

/-- The three notions coexist on one carried point, with their relations made
    explicit: Eq (Signal), Eq (Sixteen3), Conversion (Term). -/
theorem fixed_points_coexist {program : Term} (cert : Certificate program)
    (x : Term) :
    (cert.table.interpret cert.point = cert.point) ∧
    (cert.orbit (4) = cert.point) ∧
    Steps (program @@ .datum cert.point) (.datum cert.point) ∧
    Conversion (Y @@ (.k @@ x)) (.k @@ x @@ (Y @@ (.k @@ x))) := by
  exact ⟨cert.fixed, cert.orbit_settled 0, cert.program_fixed, Y_fixedpoint (.k @@ x)⟩

end Imscribing.Paraconsistent.YFixedPointConversion
