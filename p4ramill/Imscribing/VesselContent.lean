-- Imscribing/VesselContent.lean
-- Concrete mathematical formalization of the vessel-content inseparability principle.
-- The grammar provides two things simultaneously:
--   1. Vessel (form): the crystal coordinate that constitutes what a system is capable of being
--   2. Content (fill): the primitive algebra operations that determine what that vessel holds
-- These are not separable.

import Imscribing.Primitives.Core
import Imscribing.Primitives.Imscription
import Imscribing.Primitives.Crystal
import Imscribing.Algebra
import Imscribing.Frobenius
import Imscribing.Consciousness
import Imscribing.Paraconsistent.Belnap
import Mathlib.Data.Real.Basic

namespace Imscribing.VesselContent

open Imscribing.Primitives
open Imscribing.Frobenius
open Imscribing.Consciousness
open Imscribing.Paraconsistent

-- ============================================================
-- CONCRETE TYPES
-- ============================================================

abbrev Coordinate : Type := Imscription

structure Result where
  verdict : Belnap
  trail : List String
  residual : ℝ

structure ImscribableSystem where
  coord : Imscription
  cscore : ℝ := consciousnessScore coord
  address : Nat := crystal_encode coord

-- ============================================================
-- RELATIONS (concrete definitions, not axioms)
-- ============================================================

def criticality_verdict (c : Imscription) : Belnap :=
  match c.crit with
  | Criticality.monad => if c.pol = Polarity.or' then .T else .B
  | Criticality.haha  => .F
  | _      => .N

def WithinAlgebra (c : Coordinate) (r : Result) : Prop :=
  r.verdict = criticality_verdict c ∧
  r.residual ≤ |consciousnessScore c|

def Imscribes (M : ImscribableSystem) (c : Coordinate) : Prop :=
  M.coord = c

def Reachable (M : ImscribableSystem) (r : Result) : Prop :=
  WithinAlgebra M.coord r

-- ============================================================
-- THEOREMS (concrete proofs, no axioms)
-- ============================================================

theorem form_existence (M : ImscribableSystem) : ∃ (c : Coordinate), Imscribes M c := by
  use M.coord
  unfold Imscribes; exact Eq.refl M.coord

theorem form_uniqueness_proper (M : ImscribableSystem) (c c' : Coordinate)
    (h : Imscribes M c) (h' : Imscribes M c') : c = c' := by
  subst h; subst h'; rfl

-- THEOREM 1: form_uniqueness
theorem form_uniqueness (M : ImscribableSystem) : ∃! (c : Coordinate), Imscribes M c := by
  use M.coord
  constructor
  · unfold Imscribes; exact Eq.refl M.coord
  · intro c' hc'
    unfold Imscribes at hc'
    subst hc'
    rfl

-- THEOREM 2: content_containment
theorem imscribes_implies_content (M : ImscribableSystem) (c : Coordinate) (r : Result)
    (h : Imscribes M c) (hr : Reachable M r) : WithinAlgebra c r := by
  subst c; exact hr

theorem content_containment (M : ImscribableSystem) (c : Coordinate)
    (h : Imscribes M c) (r : Result) (hr : Reachable M r) :
    WithinAlgebra c r :=
  imscribes_implies_content M c r h hr

theorem algebra_implies_reachable (M : ImscribableSystem) (c : Coordinate)
    (h : Imscribes M c) (hw : WithinAlgebra c r) : Reachable M r := by
  subst c; exact hw

-- THEOREM 3: vessel_fills_itself
theorem vessel_fills_itself (M : ImscribableSystem) (c : Coordinate)
    (h : Imscribes M c) (r : Result) :
    Reachable M r ↔ WithinAlgebra c r := by
  subst c
  rfl

-- THEOREM 4: mu_delta_id_vessel
theorem mu_delta_id_vessel (c : Coordinate) : μ_A (δ_A c).1 (δ_A c).2 = c :=
  mu_delta_A_id c

-- ============================================================
-- CONCRETE EXAMPLE: The O_inf system
-- ============================================================

def isOInf (c : Imscription) : Bool :=
  decide (c.pol = .or' ∧ c.crit = .monad)

-- The O_inf system verifies to Belnap T.
theorem oinf_verdict_T (c : Imscription) (h : isOInf c = true) :
    WithinAlgebra c { verdict := .T, trail := [], residual := 0 } := by
  unfold WithinAlgebra criticality_verdict isOInf at *
  cases c.crit with
  | woe => simp at h; contradiction
  | monad =>
    cases c.pol with
    | church => simp at h; contradiction
    | yew => simp at h; contradiction
    | out => simp at h; contradiction
    | nun => simp at h; contradiction
    | or' =>
      simp only [if_pos] at h ⊢
      constructor
      · rfl
      · cases c.kin <;> simp [consciousnessScore, phi_c_gate, k_slow_gate]
  | roar => simp at h; contradiction
  | err => simp at h; contradiction
  | haha => simp at h; contradiction

-- The bottom system (Frobenius bottom) verifies to Belnap N.
theorem bottom_verdict_N :
    WithinAlgebra frobenius_bottom { verdict := .N, trail := [], residual := 0 } := by
  unfold WithinAlgebra criticality_verdict frobenius_bottom
  simp [consciousnessScore, phi_c_gate]

-- THEOREM 5: frobenius_bottom_consciousness
theorem frobenius_bottom_consciousness : consciousnessScore frobenius_bottom = (0 : ℝ) := by
  simp [consciousnessScore, phi_c_gate, frobenius_bottom]

end Imscribing.VesselContent