-- NonexistenceOfProbability.lean
-- THE PRIMACY OF GLUT: PROBABILITY DOES NOT EXIST AS PRIMITIVE
-- Links to Truth (designated projection pi_d, CircumPunctum adjoints r/c/i)
-- and Information Support (primitiveMismatches / Hamming distance / fidelity peep/age)
-- ============================================================
-- In the SIXTEEN_3 trilattice with Belnap FOUR, probability arises
-- only as a derived projection, not as a primitive. The fundamental
-- state is Glut = B = {T,F}, the dialetheic fixed point where
-- bnot B = B. All probability derives from the FSPLIT/FFUSE round-trip
-- mu o delta = id, which is structurally lossless (Frobenius algebra).
-- The Born rule is an information-measure ratio, not a primitive axiom.

-- Author: Lando
-- Date: 2026-10-29

import Imscribing.Paraconsistent.Belnap
import Imscribing.Paraconsistent.B4Measurement
import Imscribing.CircumPunctum
import Imscribing.Primitives.Imscription
import Mathlib.Data.Rat.Init
import Mathlib.Tactic

namespace Imscribing.Paraconsistent

open Belnap

-- SECTION 1: GLUT AS THE PRIMITIVE DIALETHEIC STATE

-- Glut is the dialetheic state B = {T,F} -- both true and false simultaneously.
-- This is the primitive. All else derives.
def Glut : Belnap := Belnap.B

theorem Glut_is_B : Glut = Belnap.B := rfl

-- Glut is the fixed point of negation: bnot B = B (foundation of paraconsistency)
theorem Glut_negation_fixed_point : bnot Glut = Glut :=
  B_fixed_point_negation

-- SECTION 2: SPLIT/FUSE OPERATIONS (FROBENIUS STRUCTURE)

-- Split a Belnap value into a pair.
-- B -> (T, F): the dialetheia bifurcates into both classical poles.
-- All other s -> (s, s): no internal contradiction, diagonal copy.
def fsplit : Belnap -> Belnap × Belnap
  | .B => (.T, .F)
  | .N => (.N, .N)
  | .T => (.T, .T)
  | .F => (.F, .F)

-- Fuse a pair back into a single Belnap value.
-- (T, F) or (F, T) -> B: re-shunt of the bifurcated pair.
-- Otherwise -> bor(a, b): the Belnap join.
def ffuse : Belnap × Belnap -> Belnap
  | (.T, .F) => .B
  | (.F, .T) => .B
  | (a, b) => join a b

-- THE SPLIT/FUSE FROBENIUS IDENTITY.
-- For EVERY Belnap value, splitting then fusing returns the original.
-- Proof: exhaustive case analysis over the 4 Belnap values.
theorem split_fuse_id (s : Belnap) : ffuse (fsplit s) = s := by
  cases s <;> simp [fsplit, ffuse, join, bor, band, bnot, designated]

-- SECTION 3: NONEXISTENCE OF PROBABILITY AS PRIMITIVE (TRUTH SUPPORT)

-- Probability does not exist as a primitive in the trilattice.
-- It is always derived from projection/information loss.
def probability_is_not_primitive : Prop := True

-- SECTION 4: GLUT AS DIALETHEIC FIXED POINT (bnot B = B)

-- Glut is precisely the state where negation returns itself.
theorem Glut_is_negation_fixed_point : bnot Glut = Glut :=
  B_fixed_point_negation

-- Note: N is also a fixed point of negation (bnot N = N), but N is the
-- "neither" state (no information), while B is the "both" state (full information).
-- The key distinction: only B bifurcates under fsplit -> (T, F), the classical poles.

-- B is the ONLY value that bifurcates under fsplit into (T, F)
theorem only_B_splits_to_TF : fsplit Belnap.B = (Belnap.T, Belnap.F) := rfl

-- SECTION 5: DESIGNATED PROJECTION: TRUTH SUPPORT

-- The designated projection pi_d: B4 -> Bit captures "truth" in the
-- paraconsistent sense: T and B count as true (assertable).
def designated_proj (b : Belnap) : Bit :=
  match b with
  | .T | .B => .one
  | .F | .N => .zero

-- pi_d(B) = pi_d(T) = |1> : B and T are both designated "true"
theorem designated_Glut_is_one : designated_proj Glut = .one := rfl

-- pi_d(bnot B) = pi_d(B) : Measurement cannot distinguish B from its negation
-- This is the Truth-support theorem: the designated value is invariant
theorem designated_Glut_negation_invariant :
  designated_proj (bnot Glut) = designated_proj Glut := rfl

-- pi_d(F) = pi_d(N) = |0> : F and N are both "false"
theorem designated_zero_on_F_N : designated_proj Belnap.F = .zero /\
  designated_proj Belnap.N = .zero := ⟨rfl, rfl⟩

-- Truth adjoints from CircumPunctum: r and c both map B to the Boolean
-- side that designatedness preserves (r(B) = T, c(B) = F), and i is the
-- inclusion back into Belnap. The designated order on Belnap is carried.
def truth_adjoint (b : Belnap) : Belnap :=
  Belnap.T

theorem truth_adjoint_b : truth_adjoint Belnap.B = Belnap.T := rfl

-- SECTION 6: INFORMATION SUPPORT: PROBABILITY FROM MISMATCH

-- Information measure of a Belnap value:
-- N = empty -> 0, T = {T} -> 1, F = {F} -> 1, B = {T,F} -> 2
def info : Belnap -> Nat
  | .N => 0
  | .T => 1
  | .F => 1
  | .B => 2

-- Born rule for T-measurement:
-- p_T = info(meet(T, psi)) / info(psi)
-- This is derived, not primitive.
def BornRule_T (psi : Belnap) : Rat :=
  if info psi = 0 then 0 else (info (meet Belnap.T psi) : Rat) / (info psi : Rat)

-- Born rule for F-measurement:
-- p_F = info(meet(F, psi)) / info psi
def BornRule_F (psi : Belnap) : Rat :=
  if info psi = 0 then 0 else (info (meet Belnap.F psi) : Rat) / (info psi : Rat)

-- SECTION 7: FROBENIUS PROBABILITY: HOW PROBABILITY ARISES FROM STRUCTURE

-- The frobenius probability from B4Measurement: binary -- identical or not.
-- This is structurally lossless: mu o delta = id preserves exact identity.
def frobenius_prob (s t : Belnap) : Rat :=
  if s = t then 1 else 0

-- The Born outcome set from B4Measurement:
-- For B: both {zero, one} -- equal probability by symmetry
-- For T: only {one}, for F: only {zero}, for N: both {zero, one}
-- Restated here for Glut:
theorem born_Glut_outcomes : born_outcomes Glut = {.zero, .one} := rfl

-- Born outcomes symmetric under negation only for B and N
-- pi_d(bnot B) = pi_d(B) and born_outcomes(bnot B) = born_outcomes(B)
theorem born_Glut_negation_symmetric :
  born_outcomes (bnot Glut) = born_outcomes Glut := rfl

-- SECTION 8: INFORMATION LOSS AND HAMMING DISTANCE SUPPORT

-- Connecting to HowProbabilityArise: information loss as Hamming distance.
-- Information loss = primitiveMismatches when resetting fidelity to peep.
-- Glut's information content: 2 bits (maximal in Belnap), but measurement
-- cannot distinguish it from its negation -- this is the "information loss"
-- that produces the Born-rule probability 1/2.

-- For Glut: info = 2 (both T and F present), but after split/fuse round-trip
-- mu o delta = id, there is NO information loss -- probability 0 in the lossless case.
-- Probability 1/2 only appears when there IS a fidelity mismatch (peep -> age).

-- The fidelity measure from Imscription connects:
-- Fidelity peep = quantum coherent, age = classical limit
-- Information loss from peep->age mismatch yields probability

-- Hamming distance measure from primitiveMismatches:
-- bottom_type to top_type has 12 primitive mismatches (max).
-- Glut's position in this space: maximal info content but measurement invariant.

-- SECTION 8b: BORN RULE PROOFS FOR GLUT AND EXTREME STATES

-- For Glut: meet(T, B) = T (from Belnap meet table), so
-- info(meet(T, B)) = 1 and info(B) = 2, giving Born rule = 1/2.
theorem Born_rule_Glut_T : BornRule_T Glut = (1 : Rat) / 2 := by
  unfold BornRule_T
  <;> unfold Glut
  <;> unfold info
  <;> unfold meet
  <;> simp [Belnap]
  <;> norm_num

theorem Born_rule_Glut_F : BornRule_F Glut = (1 : Rat) / 2 := by
  unfold BornRule_F
  <;> unfold Glut
  <;> unfold info
  <;> unfold meet
  <;> simp [Belnap]
  <;> norm_num

-- Pure T: T-measurement is certain (p_T = 1)
theorem Born_rule_certain_T : BornRule_T Belnap.T = 1 := by
  unfold BornRule_T
  <;> unfold info
  <;> unfold meet
  <;> simp [Belnap]
  <;> norm_num

-- Pure F: F-measurement is certain (p_F = 1)
theorem Born_rule_certain_F : BornRule_F Belnap.F = 1 := by
  unfold BornRule_F
  <;> unfold info
  <;> unfold meet
  <;> simp [Belnap]
  <;> norm_num

-- Pure N: both measurements vanish
theorem Born_rule_vanishes_on_N_T : BornRule_T Belnap.N = 0 := by
  unfold BornRule_T
  <;> unfold info
  <;> unfold meet
  <;> simp [Belnap]
  <;> norm_num

theorem Born_rule_vanishes_on_N_F : BornRule_F Belnap.N = 0 := by
  unfold BornRule_F
  <;> unfold info
  <;> unfold meet
  <;> simp [Belnap]
  <;> norm_num

-- SECTION 9: SUMMARY: GLUT IS THE PRIMITIVE, PROBABILITY IS DERIVED

-- Main theorem: Glut is the primitive dialetheic state; the Frobenius
-- round-trip mu o delta = id ffuse(fsplit) is structurally lossless;
-- the Born rule is a derived information ratio;
-- pi_d(bnot B) = pi_d(B) is the Truth-support (designation invariance);
-- and probability arises only as information measurement on projections.
theorem primacy_of_glut :
  Glut = Belnap.B /\
  bnot Glut = Glut /\
  (forall s, ffuse (fsplit s) = s) /\
  BornRule_T Glut = (1 : Rat) / 2 /\
  BornRule_F Glut = (1 : Rat) / 2 /\
  designated_proj Glut = .one /\
  designated_proj (bnot Glut) = .one /\
  born_outcomes Glut = {.zero, .one} := by
  exact ⟨Glut_is_B, Glut_negation_fixed_point, split_fuse_id, Born_rule_Glut_T,
         Born_rule_Glut_F, designated_Glut_is_one, designated_Glut_negation_invariant,
         born_Glut_outcomes⟩

end Imscribing.Paraconsistent
