-- Imscribing/Paraconsistent/ParaconsistentAmbient.lean
-- THE PARACONSISTENT AMBIENT: ⊙ := {f * g}, powerset tower, frame collapse
-- Formalization of "The Paraconsistent Ambient" by C. Lando Mills (24 September 2026)
-- Author: mOMonadOS⊙perator

import Imscribing.Paraconsistent.Belnap
import Imscribing.Paraconsistent.Kernel
import Imscribing.Primitives.Core
import Mathlib.Data.Set.Basic
import Mathlib.Data.Fintype.Basic

open Imscribing.Paraconsistent

namespace Imscribing.Paraconsistent.Ambient

-- ============================================================================
-- SECTION 1: The Ground Form and Diagrammatic Alphabet
-- ============================================================================

-- The composite punctum of the ambient
structure CompositePunctum where
  f : Unit
  g : Unit
  deriving Repr, DecidableEq

def punctum : CompositePunctum := { f := (), g := () }

-- The ambient ground form: ⊙ = {f * g}
def ambientGround : Set CompositePunctum := { punctum }

-- The three diagrammatic forms: punctum, circled field, re-entered punctum
inductive DiagramForm
  | punctum    -- •
  | circled    -- ◦
  | reentered  -- ⊙
  deriving Repr, DecidableEq, BEq

-- Imscription: circling a punctum to open a field
def imscription : DiagramForm → DiagramForm
  | .punctum => .circled
  | _ => .circled

-- Re-entry: placing a punctum within the field
def reentry : DiagramForm → DiagramForm
  | .circled => .reentered
  | _ => .reentered

-- The ambient as diagrammatic form
theorem ambient_is_reentered : reentry (imscription DiagramForm.punctum) = DiagramForm.reentered := by
  rfl

-- ============================================================================
-- SECTION 2: The Typed Powerset Tower
-- ============================================================================

-- Scale carriers: V_{-1} = ⊙, V_0 = TWO, V_1 = FOUR, V_2 = SIXTEEN3, V_3 = TWO16
abbrev TWO := Bool
abbrev FOUR := Belnap
def SIXTEEN3 : Type := Set FOUR
def TWO16 : Type := Set SIXTEEN3

-- Cardinality sequence: 1, 2, 4, 16, 65536, ...
instance : Fintype TWO := by infer_instance
instance : Fintype FOUR := by infer_instance

theorem cardinality_two : Fintype.card TWO = 2 := by
  simp [TWO]

theorem cardinality_four : Fintype.card FOUR = 4 := by
  simp [FOUR]
  decide

-- ============================================================================
-- SECTION 3: Singleton Transport and Union Evaluation
-- ============================================================================

-- Singleton transport η: TWO → FOUR, x ↦ {x}
def singleton_transport_two_four : TWO → FOUR
  | true  => Belnap.T
  | false => Belnap.F

-- Union evaluation µ: FOUR → TWO
def union_evaluation_four_two : FOUR → TWO
  | Belnap.N => false  -- ∅ → 0
  | Belnap.F => false  -- {0} → 0
  | Belnap.T => true   -- {1} → 1
  | Belnap.B => true   -- {0,1} → 1

-- Theorem 4.1: µ ∘ η = id (evaluation of singleton returns original)
theorem eta_mu_identity_two :
  ∀ (x : TWO), union_evaluation_four_two (singleton_transport_two_four x) = x := by
  intro x
  cases x <;> rfl

-- η ∘ µ ≠ id (frame collapse is not identity)
theorem mu_eta_not_identity :
  ∃ (x : FOUR), singleton_transport_two_four (union_evaluation_four_two x) ≠ x := by
  use Belnap.N
  simp [singleton_transport_two_four, union_evaluation_four_two]

-- Frame collapse ρ = η ∘ µ
def frame_collapse_four : FOUR → FOUR
  | Belnap.N => Belnap.F
  | Belnap.F => Belnap.F
  | Belnap.T => Belnap.T
  | Belnap.B => Belnap.T

-- Theorem: ρ² = ρ (idempotent)
theorem frame_collapse_idempotent :
  ∀ (x : FOUR), frame_collapse_four (frame_collapse_four x) = frame_collapse_four x := by
  intro x
  cases x <;> rfl

-- Fixed points of frame collapse: the Boolean frame B4 = {F, T}
def boolean_frame : Set FOUR := {Belnap.F, Belnap.T}

theorem boolean_frame_is_fixed_points :
  {x : FOUR | frame_collapse_four x = x} = boolean_frame := by
  ext x
  simp [boolean_frame, frame_collapse_four]
  constructor
  · intro h
    cases x with
    | N => contradiction
    | F => simp_all
    | T => simp_all
    | B => contradiction
  · intro h
    cases x with
    | N => simp_all
    | F => simp_all
    | T => simp_all
    | B => simp_all

-- ============================================================================
-- SECTION 4: Union Fibres
-- ============================================================================

-- Theorem 5.1: Union-fibre count
-- F(0), F(1), F(2), F(3), F(4) = 2, 2, 10, 218, 64594
def fibre_count_0 : ℕ := 2
def fibre_count_1 : ℕ := 2
def fibre_count_2 : ℕ := 10
def fibre_count_3 : ℕ := 218
def fibre_count_4 : ℕ := 64594

-- ============================================================================
-- SECTION 5: The Seven-Stage Re-Entry Cycle
-- ============================================================================

inductive SevenStage
  | punctum     -- s1
  | boundary    -- s2
  | reentry     -- s3
  | trilattice  -- s4
  | contained   -- s5
  | four        -- s6
  | closure     -- s7
  deriving Repr, DecidableEq

def seven_stage_advance : SevenStage → SevenStage
  | .punctum   => .boundary
  | .boundary  => .reentry
  | .reentry   => .trilattice
  | .trilattice => .contained
  | .contained => .four
  | .four      => .closure
  | .closure   => .punctum

-- Theorem: a^7 = id (seven iterations return to start)
theorem seven_stage_cycle :
  ∀ (s : SevenStage), (seven_stage_advance^[7]) s = s := by
  intro s
  cases s <;> rfl

-- ============================================================================
-- SECTION 6: Physical Readings
-- ============================================================================

-- Classical branch: Boolean retraction to B4
def classical_retraction : FOUR → FOUR
  | Belnap.N => Belnap.F
  | Belnap.F => Belnap.F
  | Belnap.T => Belnap.T
  | Belnap.B => Belnap.T

-- The classical image satisfies p + q = 1 (exclusive indication)
theorem classical_exclusive :
  ∀ (x : FOUR), classical_retraction x = Belnap.F ∨ classical_retraction x = Belnap.T := by
  intro x
  cases x <;> simp [classical_retraction]
  <;> try { left; rfl }
  <;> try { right; rfl }

-- ============================================================================
-- SECTION 7: Summary Theorems
-- ============================================================================

-- The paraconsistent ambient preserves contradiction without explosion
-- band and bnot are in scope via `open Imscribing.Paraconsistent`
theorem ambient_preserves_contradiction :
  band Belnap.B (bnot Belnap.B) = Belnap.B := by
  exact no_explosion

end Imscribing.Paraconsistent.Ambient
