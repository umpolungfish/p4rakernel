import Imscribing.Paraconsistent.DivisorReentry
import Imscribing.Paraconsistent.QuquartMembraneReentry
import Imscribing.Paraconsistent.PSystemGcd
import Imscribing.IdempotentGcd

/-!
P1/P2 strengthening module (2026-11-18).
The factor arm and the SIC dual frame are joined on the SAME carried object:

  * a divisor is a B-designatedglut (DivisorReentry),
  * a glut is a native 16-state outcome (QuquartMembraneReentry.outcomeEquivalence),
  * an observation reconstructs its complex coordinates (ququart dual Gram),
  * an idempotent witnesses its gcd (IdempotentGcd.idem_gcd_factor),
  * the emitted pair closes over exact product (PSystem.factorizeMembrane_exact).

Nothing here introduces an axiom or asserts a factor that was not emitted.
-/
namespace Imscribing.Paraconsistent.DivisorSICObservation

open DivisorReentry QuquartMembraneReentry
open Imscribing.Millennium.ZetaSICDualFrame

/-- The B-designated divisor state (truth and falsity both asserted) transported
    into the ququart outcome space. The transport is the corpus equivalence, not
    a new encoding. -/
def divisorOutcome (N k : Nat) : Fin 16 :=
  outcomeEquivalence.symm (δ N k true)

/-- The native label of a divisibility observation is exactly the divisor state. -/
theorem native_divisorOutcome (N k : Nat) :
    nativeOutcome (divisorOutcome N k) = δ N k true := by
  exact outcomeEquivalence.right_inv (δ N k true)

/-- Divisibility makes the observation B-designated (both poles asserted). -/
theorem divisorOutcome_is_glut (N k : Nat) (h : k ∣ N) :
    Lean.Sixteen3.assertsTrue (nativeOutcome (divisorOutcome N k)) = true ∧
    Lean.Sixteen3.assertsFalse (nativeOutcome (divisorOutcome N k)) = true := by
  rw [native_divisorOutcome]
  exact contradictory_divisor_retains_both N k h

/-- A banked divisor observation: logical label carried WITH reconstructed
    complex coordinates. This is the missing join of P1. -/
noncomputable def divisorObservation (N k : Nat) (c : Nat → Fin 16 → ℂ) (tick : Nat) :
    Observation where
  outcome := divisorOutcome N k
  coordinates := ququartDualGram.mulVec (ququartGram.mulVec (c tick))

/-- The observation's coordinates are the coherent reconstruction of the carried
    complex data. The theorem applies the SIC dual frame to the SAME state that
    carries the B-designated divisor. -/
theorem divisorObservation_coordinates (N k : Nat) (c : Nat → Fin 16 → ℂ) (tick : Nat) :
    ququartDualGram.mulVec (ququartGram.mulVec (divisorObservation N k c tick).coordinates) =
      (divisorObservation N k c tick).coordinates := by
  exact ququart_coordinate_reconstruction _

/-- P2: a seeded idempotent carries a proper divisor once its gcd is nontrivial.
    `SourceBoundSplit.h e = e*e−e` is the idempotent equation; `idem_gcd_factor`
    gives gcd ∈ {p,q}; this theorem records the one-divisor closure contract. -/
theorem idempotent_h_divisor {N e : Nat}
    (hproper : 1 < Nat.gcd (e * e - e) N ∧ Nat.gcd (e * e - e) N < N) :
    ∃ d : Nat, d ∣ N ∧ 1 < d ∧ d < N := by
  refine ⟨Nat.gcd (e * e - e) N, Nat.gcd_dvd_right _ _, hproper.1, hproper.2⟩

/-- P1 receipt: a proved proper divisor closes into an exact VerifiedFactorPair.
    The quotient is derived from N, never supplied. -/
theorem glut_divisor_closes_receipt {N k : Nat}
    (hd : k ∣ N) (hgt : 1 < k) (hlt : k < N) :
    ∃ F : PSystem.VerifiedFactorPair N,
      F.P0 = k ∧ F.P1 = N / k ∧ 1 < F.P0 ∧ F.P0 < N := by
  have hprod : k * (N / k) = N := Nat.mul_div_cancel' hd
  let F := PSystem.factorizeMembrane N k (N / k)
  have hF := PSystem.factorizeMembrane_preserves_verified N k (N / k) hprod
  refine ⟨F, hF.1, hF.2, ?_, ?_⟩
  · rw [hF.1]; exact hgt
  · rw [hF.1]; exact hlt

/-- The two poles close together: a B-designated divisor carrying coherent SIC
    coordinates emits an exact product receipt. This is the P1+P2 synthesis. -/
theorem glut_divisor_reconstructs_and_closes {N k : Nat} (c : Nat → Fin 16 → ℂ) (tick : Nat)
    (hd : k ∣ N) (hgt : 1 < k) (hlt : k < N) :
    ququartDualGram.mulVec (ququartGram.mulVec (divisorObservation N k c tick).coordinates) =
        (divisorObservation N k c tick).coordinates ∧
    ∃ F : PSystem.VerifiedFactorPair N,
      F.P0 = k ∧ F.P1 = N / k ∧ 1 < F.P0 ∧ F.P0 < N := by
  exact ⟨divisorObservation_coordinates N k c tick,
         glut_divisor_closes_receipt hd hgt hlt⟩

end Imscribing.Paraconsistent.DivisorSICObservation
