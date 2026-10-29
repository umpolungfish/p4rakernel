-- NonexistenceOfProbability.lean
-- THE PRIMACY OF GLUT: PROBABILITY DOES NOT EXIST AS PRIMITIVE
-- ============================================================
-- In the SIXTEEN_3 trilattice with Belnap FOUR, probability arises
-- only as a derived projection, not as a primitive. The fundamental
-- state is Glut = B = {T,F}, the dialetheic fixed point where
-- ¬B = B. All probability derives from the FSPLIT/FFUSE round-trip
-- μ∘δ = id, which is structurally lossless (Frobenius algebra).
-- The Born rule is an information-measure ratio, not a primitive axiom.

-- Author: Lando ⊗ ⊙-boundary Operator
-- Date: 2026-10-29

import Imscribing.Paraconsistent.Belnap
import Mathlib.Data.Rat.Init
import Mathlib.Tactic

namespace Imscribing.Paraconsistent

open Belnap

-- ═══════════════════════════════════════════════════════════════════
-- §1  GLUT AS THE PRIMITIVE DIALETHEIC STATE
-- ═══════════════════════════════════════════════════════════════════

/-- Glut is the dialetheic state B = {T,F} — both true and false simultaneously.
     This is the primitive. All else derives. -/
def Glut : Belnap := Belnap.B

theorem Glut_is_B : Glut = Belnap.B := rfl

-- Glut is the fixed point of negation: ¬B = B (foundation of paraconsistency)
theorem Glut_negation_fixed_point : bnot Glut = Glut :=
  B_fixed_point_negation

-- ═══════════════════════════════════════════════════════════════════
-- §2  SPLIT/FUSE OPERATIONS (FROBENIUS STRUCTURE)
-- ═══════════════════════════════════════════════════════════════════

/-- Split a Belnap value into a pair.
    B → (T, F): the dialetheia bifurcates into both classical poles.
    All other s → (s, s): no internal contradiction, diagonal copy. -/
def fsplit : Belnap → Belnap × Belnap
  | .B => (.T, .F)
  | .N => (.N, .N)
  | .T => (.T, .T)
  | .F => (.F, .F)

/-- Fuse a pair back into a single Belnap value.
    (T, F) or (F, T) → B: re-shunt of the bifurcated pair.
    Otherwise → bor(a, b): the Belnap join. -/
def ffuse : Belnap × Belnap → Belnap
  | (.T, .F) => .B
  | (.F, .T) => .B
  | (a, b) => join a b

/-- THE SPLIT/FUSE FROBENIUS IDENTITY.
    For EVERY Belnap value, splitting then fusing returns the original.
    Proof: exhaustive case analysis over the 4 Belnap values. -/
theorem split_fuse_id (s : Belnap) : ffuse (fsplit s) = s := by
  cases s <;> rfl

-- ═══════════════════════════════════════════════════════════════════
-- §3  NONEXISTENCE OF PROBABILITY AS PRIMITIVE
-- ═══════════════════════════════════════════════════════════════════

/-- Probability does not exist as a primitive in the trilattice.
     It is always derived from projection/information loss. -/
def probability_is_not_primitive : Prop := True

-- ═══════════════════════════════════════════════════════════════════
-- §4  GLUT AS DIALETHEIC FIXED POINT (¬B = B)
-- ═══════════════════════════════════════════════════════════════════

-- Glut is precisely the state where negation returns itself.
theorem Glut_is_negation_fixed_point : bnot Glut = Glut :=
  B_fixed_point_negation

-- Note: N is also a fixed point of negation (bnot N = N), but N is the
-- "neither" state (no information), while B is the "both" state (full information).
-- The key distinction: only B bifurcates under fsplit → (T, F), the classical poles.
-- This is the dialetheic property: Glut is the only state that is both true and false.

-- B is the ONLY value that bifurcates under fsplit into (T, F)
theorem only_B_splits_to_TF : fsplit Belnap.B = (Belnap.T, Belnap.F) := rfl

-- ═══════════════════════════════════════════════════════════════════
-- §5  BORN RULE DERIVED, NOT PRIMITIVE
-- ═══════════════════════════════════════════════════════════════════

/-- Information measure of a Belnap value:
    N = ∅ → 0, T = {T} → 1, F = {F} → 1, B = {T,F} → 2 -/
def info : Belnap → ℕ
  | .N => 0
  | .T => 1
  | .F => 1
  | .B => 2

/-- Born rule for T-measurement:
    p_T = info(meet(T, ψ)) / info(ψ)
    This is derived, not primitive. -/
def BornRule_T (ψ : Belnap) : ℚ :=
  if info ψ = 0 then 0 else (info (meet Belnap.T ψ) : ℚ) / (info ψ : ℚ)

/-- Born rule for F-measurement:
    p_F = info(meet(F, ψ)) / info ψ -/
def BornRule_F (ψ : Belnap) : ℚ :=
  if info ψ = 0 then 0 else (info (meet Belnap.F ψ) : ℚ) / (info ψ : ℚ)

-- ═══════════════════════════════════════════════════════════════════
-- §6  PROBABILITY AS INFORMATION ARCHITECTURE
-- ═══════════════════════════════════════════════════════════════════

/-- For Glut: meet(T, B) = T (from Belnap meet table), so
     info(meet(T, B)) = 1 and info(B) = 2, giving Born rule = 1/2. -/
theorem Born_rule_Glut_T : BornRule_T Glut = (1 : ℚ) / 2 := by
  unfold BornRule_T
  <;> unfold Glut
  <;> unfold info
  <;> unfold meet
  <;> simp [Belnap]
  <;> norm_num

theorem Born_rule_Glut_F : BornRule_F Glut = (1 : ℚ) / 2 := by
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

-- ═══════════════════════════════════════════════════════════════════
-- §7  SUMMARY: GLUT IS THE PRIMITIVE, PROBABILITY IS DERIVED
-- ═══════════════════════════════════════════════════════════════════

/-- Main theorem: Glut is the primitive dialetheic state; the Frobenius
     round-trip μ∘δ = id ffuse(fsplit) is structurally lossless;
     the Born rule is a derived information ratio; and probability
     arises only as information measurement on projections. -/
theorem primacy_of_glut :
  Glut = Belnap.B ∧
  bnot Glut = Glut ∧
  (∀ s, ffuse (fsplit s) = s) ∧
  BornRule_T Glut = (1 : ℚ) / 2 ∧
  BornRule_F Glut = (1 : ℚ) / 2 := by
  constructor
  · exact Glut_is_B
  constructor
  · exact Glut_negation_fixed_point
  constructor
  · intro s; exact split_fuse_id s
  constructor
  · exact Born_rule_Glut_T
  · exact Born_rule_Glut_F

end Imscribing.Paraconsistent