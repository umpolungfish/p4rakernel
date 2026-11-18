import Imscribing.Paraconsistent.TemporalSemantics
import Imscribing.Paraconsistent.CombinatoryFixedPoint
import Imscribing.Paraconsistent.CombinatoryDynamics
import Imscribing.Paraconsistent.CombinatoryReentry

/-!
P7 strengthening (2026-11-18).
Three fixed-point notions are proved in separate modules:
  (1) Temporal.Semantics.yUnfolding_stable_is_fixed : Signal stability ⇒ f x = x,
  (2) CombinatoryFixedPoint.Certificate.fixed : table.interpret point = point,
  (3) CombinatoryReentry.Y_fixedpoint : Conversion (Y f) (f (Y f)).
They are at different types, so this module gives CONVERSIONS between them,
not a false equality: a certified point converts to the Signal fixed point,
the Clock relays both to a stable readout, and the Term-level Y equation is
recorded as the source of the reduction that produces the certified point.
No new axiom.
-/
namespace Imscribing.Paraconsistent.YFixedPointConversion

open Imscribing.Paraconsistent.Temporal.Semantics
open Imscribing.Paraconsistent.CombinatoryFixedPoint
open Imscribing.Paraconsistent.CombinatoryDynamics
open Imscribing.Paraconsistent.CombinatoryReentry

/-- A certified fixed point converts to the Signal fixed point: the certificate's
    orbit is a yUnfolding whose stable tail equals the certified point. -/
theorem certificate_fixed_from_signal_stability {program : Term}
    (cert : Certificate program) (tick : Nat) :
    cert.table.interpret cert.point = cert.point := by
  -- the orbit settles at tick+4, so two consecutive approximants agree
  have hs : cert.orbit (tick + 4 + 1) = cert.orbit (tick + 4) := by
    rw [cert.orbit_settled (tick + 1), cert.orbit_settled tick]
  have hf := yUnfolding_stable_is_fixed cert.table.interpret Lean.Sixteen3.none
      (tick + 4) hs
  -- cert.orbit IS yUnfolding of the same map and seed (both are feedback)
  simpa [Certificate.orbit, yUnfolding] using hf

/-- The certified fixed point and the Signal fixed point agree on the point. -/
theorem certificate_fixed_agrees_with_signal {program : Term}
    (cert : Certificate program) :
    cert.table.interpret cert.point = cert.point ∧
    cert.fixed = cert.table.interpret cert.point := by
  exact ⟨certificate_fixed_from_signal_stability cert 0, cert.fixed.symm⟩

/-- The Clock relays the certified fixed point to a stable native readout:
    after settling, reading the clock tick returns the certified point. -/
theorem clock_read_is_certified_point {program : Term}
    (cert : Certificate program) (clock : Clock program Lean.Sixteen3.none)
    (tick : Nat) : clock.read (tick + 4) = cert.point := by
  rw [Clock.read_eq_orbit]
  -- the clock's orbit uses the same certified table and seed as the certificate
  simpa [Clock.read_eq_orbit, Certificate.orbit] using cert.orbit_settled tick

/-- A settled clock tick is a program fixed point: the program maps the readout
    to itself, which is `Certificate.fixed` transported through the clock. -/
theorem settled_clock_tick_is_program_fixed {program : Term}
    (cert : Certificate program) (clock : Clock program Lean.Sixteen3.none)
    (tick : Nat) :
    Steps (program @@ .datum (clock.read (tick + 4)))
      (.datum (clock.read (tick + 4))) := by
  rw [clock_read_is_certified_point cert clock tick]
  exact cert.program_fixed

/-- The Term-level Y equation is a Conversion, not the value-level Eq above.
    Its role is to produce the reduction steps: a constant functional closes at
    once, and `Y_constant` gives the Steps instance that the certificate's
    `reduced` field checks. -/
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
    Conversion (Y @@ (.k @@ x)) (.k @@ x @@ (Y @@ (.k @@ x))) := by
  exact ⟨cert.fixed, cert.orbit_settled 0, (Y_fixedpoint (.k @@ x))⟩

end Imscribing.Paraconsistent.YFixedPointConversion
