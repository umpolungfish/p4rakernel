-- Imscribing/VoxReconcile.lean
-- Stage 24c — WALK_WORD vs TYPE_WORD: semantic reconciliation.
--
-- Stage 24b separated two objects the shipped glyph string had conflated:
--
--   WALK_WORD = ∈∋⊤≻⊡   the string the Rust resident machine walks.
--                        vox sixteen3 check reads N — its ∈∋ frame is ADJACENT
--                        (span 1) and encloses no transformation.
--   TYPE_WORD = ∈⊤≻⊡∋   the structurally CLOSING form.
--                        vox sixteen3 check reads T — the transformation ⊤≻⊡
--                        occurs BETWEEN split and fuse (span 4).
--
-- The readings below are REFLECTED from the frozen Vox observation
-- (ig-docs/VOX_SEMANTICS.md §Addendum, Stage 24b), measured with the standalone
-- vox CLI's current surfaces: `vox verdict`, `vox sixteen3 check`, `vox pairs`.
-- This file does not re-run Vox; it records the measured values and states the
-- boundary they draw. It imports VoxResident and CHANGES NONE OF ITS THEOREMS:
-- those prove the record-level machine, not the glyph-word's structural closure.

import Imscribing.VoxResident

namespace Imscribing
namespace VoxReconcile

open VoxResident

/-- The FOUR-valued reading (Belnap T/F/B/N). -/
inductive Reading | T | F | B | N
  deriving DecidableEq, Repr

/-- One frozen Vox observation on a glyph word. -/
structure VoxObs where
  word     : List Char
  four     : Reading   -- `vox verdict`
  sixteen3 : Reading   -- `vox sixteen3 check`
  span     : Nat       -- `vox pairs`: CLOSE - OPEN
  work     : Bool      -- `vox pairs`: WORK column
  interior : List Char -- `vox pairs`: INTERIOR column
  deriving Repr

/-- The shipped reducer walk (Vox/src/reducer_store.rs:84). -/
def WALK_WORD : List Char := "∈∋⊤≻⊡".toList
/-- The structurally closing form. -/
def TYPE_WORD : List Char := "∈⊤≻⊡∋".toList
/-- The shipped edit/delete walk (Vox/src/tape_delete.rs:28). -/
def WALK_EDIT : List Char := "∈∋⊥≻⊡".toList
/-- The structurally closing edit form. -/
def TYPE_EDIT : List Char := "∈⊥≻⊡∋".toList

-- ── Frozen observations (Stage 24b; measured by the standalone vox CLI) ──
def walkObs : VoxObs :=
  { word := WALK_WORD, four := .N, sixteen3 := .N, span := 1, work := false, interior := [] }
def typeObs : VoxObs :=
  { word := TYPE_WORD, four := .T, sixteen3 := .T, span := 4, work := true, interior := "⊤≻⊡".toList }
def walkEditObs : VoxObs :=
  { word := WALK_EDIT, four := .N, sixteen3 := .N, span := 1, work := false, interior := [] }
def typeEditObs : VoxObs :=
  { word := TYPE_EDIT, four := .T, sixteen3 := .T, span := 4, work := true, interior := "⊥≻⊡".toList }

-- ── The measured readings, as theorems ──
theorem walk_reading     : walkObs.sixteen3 = .N := rfl
theorem type_reading     : typeObs.sixteen3 = .T := rfl
theorem walk_four        : walkObs.four = .N := rfl
theorem type_four        : typeObs.four = .T := rfl
theorem walk_reading_edit : walkEditObs.sixteen3 = .N := rfl
theorem type_reading_edit : typeEditObs.sixteen3 = .T := rfl

/-- The two words are DIFFERENT objects. Do not blur them back together. -/
theorem walk_ne_type : WALK_WORD ≠ TYPE_WORD := by decide
theorem walkEdit_ne_typeEdit : WALK_EDIT ≠ TYPE_EDIT := by decide

-- ── A catalog entry is the structural type of an executable object ──
/-- The catalog candidate: the CLOSING word, not the historically shipped walk. -/
def CATALOG_TYPE_WORD : List Char := TYPE_WORD
theorem catalog_type_closes : typeObs.sixteen3 = .T := rfl
theorem shipped_walk_is_provenance : walkObs.sixteen3 = .N := rfl

-- ── The boundary theorem ──
/-- The important boundary: record-level reducer correctness is INDEPENDENT of the
    glyph-word's structural closure. The machine the shipped label drives is correct
    (VoxResident.lean) while that label's own ∈∋ frame encloses no transformation. -/
theorem reducer_correct_while_walk_frame_empty :
    (∀ (τ : Trace) (i : Nat), DELETE τ i = delRecord τ i) ∧ walkObs.work = false :=
  ⟨DELETE_edit_is_oracle, rfl⟩

/-- The strongest statement of the reconciliation: the walk performs work in resident
    store semantics, while its own FSPLIT/FFUSE frame encloses no transformation. -/
theorem walk_works_frame_verifies_nothing :
    walkObs.sixteen3 = .N ∧ typeObs.sixteen3 = .T ∧ walkObs.work = false :=
  ⟨rfl, rfl, rfl⟩

end VoxReconcile
end Imscribing
