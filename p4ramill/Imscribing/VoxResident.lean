-- Imscribing/VoxResident.lean
-- FROZEN VOX SEMANTICS — the resident reducer ported to Lean (Stage 24).
--
-- Vox discharged these obligations by COMPUTATION (bins: TAPE-DELETE, TAPE-FUSE,
-- TAPE-ALGEBRA-WORDS, REDUCE-RESIDENT). Here they become STRUCTURAL theorems.
--
-- A trace tape is a word of records. A resident edit replaces a span of `g`
-- consecutive records by `repl` records. The four Vox transformations are ONE
-- operation under four data settings:
--
--     DELETE = span 1, repl []          (Vox EDIT word ∈∋⊥≻⊡, groups=1, fill=∅)
--     CANCEL = span k, repl []          (groups=k, fill=∅)
--     FUSE   = span 2, repl [merge]     (groups=2, fill=⊞)
--     INLINE = span k, repl [compose]   (groups=k, fill=⊞)
--
-- Headlines:
--   * DELETE_edit_is_oracle : the resident edit IS the oracle record-removal.
--   * edit_shrinks          : every valid edit strictly shrinks the trace, so the
--                             resident schedule terminates — no Rust loop needed.
--   * normalize_is_normal   : the resident reducer halts at a schedule-fixed point.
--
-- Modelled at the RECORD boundary — exactly what the ∈∋ byte walk implements.

import Mathlib.Data.List.Basic
import Mathlib.Tactic

namespace Imscribing
namespace VoxResident

/-- A trace is a word of records (each record is a word of marks). -/
abbrev Trace := List (List Char)

/-- The ORACLE: erase record `i` (Vox `delete_record` = `List.remove(i)`). -/
def delRecord (τ : Trace) (i : Nat) : Trace := τ.eraseIdx i

/-- The RESIDENT edit: replace the span `[i, i+g)` by `repl` (Vox `tape_edit` at the
    record boundary — the ∈∋ walk computes exactly this). -/
def edit (τ : Trace) (i g : Nat) (repl : Trace) : Trace :=
  τ.take i ++ repl ++ τ.drop (i + g)

/-- The four transformations are ONE operation under four data settings. -/
def DELETE (τ : Trace) (i : Nat) : Trace := edit τ i 1 []
def CANCEL (τ : Trace) (i k : Nat) : Trace := edit τ i k []
def FUSE   (τ : Trace) (i : Nat) (r : List Char) : Trace := edit τ i 2 [r]
def INLINE (τ : Trace) (i k : Nat) (w : List Char) : Trace := edit τ i k [w]

/-- `take i ++ drop (i+1)` is `eraseIdx i` — the take/drop decomposition of the oracle. -/
theorem take_drop_eq_eraseIdx : ∀ (τ : List α) (i : Nat),
    τ.take i ++ τ.drop (i + 1) = τ.eraseIdx i := by
  intro τ i
  induction τ generalizing i with
  | nil => cases i <;> rfl
  | cons a l ih =>
    cases i with
    | zero => rfl
    | succ j =>
      simp only [List.take_succ_cons, List.drop_succ_cons, List.eraseIdx_cons_succ,
                 List.cons_append]
      rw [ih j]

/-- FIDELITY: the resident DELETE edit equals the oracle. This is the Lean form of
    Vox's byte-equality `delete_word(trace,i) == delete_record(trace,i)` (3298/3298). -/
theorem DELETE_edit_is_oracle (τ : Trace) (i : Nat) :
    DELETE τ i = delRecord τ i := by
  unfold DELETE edit delRecord
  rw [List.append_nil, take_drop_eq_eraseIdx]

/-- LENGTH LAW: a replace of span `g` by `repl` changes the length by `repl.length - g`. -/
theorem edit_length (τ : Trace) (i g : Nat) (repl : Trace) (hi : i + g ≤ τ.length) :
    (edit τ i g repl).length = τ.length - g + repl.length := by
  unfold edit
  rw [List.length_append, List.length_append, List.length_take, List.length_drop]
  have hi' : i ≤ τ.length := by omega
  rw [Nat.min_eq_left hi']
  omega

/-- TERMINATION: every valid edit strictly shrinks the trace. This replaces the Rust
    resident loop's fuel with a decreasing measure — the schedule cannot run forever. -/
theorem edit_shrinks (τ : Trace) (i g : Nat) (repl : Trace)
    (hg : 1 ≤ g) (hrepl : repl.length < g) (hi : i + g ≤ τ.length) :
    (edit τ i g repl).length < τ.length := by
  rw [edit_length τ i g repl hi]
  omega

/-- The four Vox transformations satisfy the validity contract. -/
theorem rule_delete_valid : 1 ≤ (1 : Nat) ∧ ([] : Trace).length < 1 := by
  constructor <;> simp
theorem rule_fuse_valid (r : List Char) : 1 ≤ (2 : Nat) ∧ ([r] : Trace).length < 2 := by
  constructor <;> simp
theorem rule_inline_valid (k : Nat) (w : List Char) (hk : 2 ≤ k) :
    1 ≤ k ∧ ([w] : Trace).length < k := by
  constructor
  · omega
  · simp
    omega

/-- A schedule reads the tape and proposes (start, span, replacement). -/
abbrev Schedule := Trace → Option (Nat × Nat × Trace)

/-- Well-formed: any proposed edit is admissible (positive span, strictly shrinking). -/
def ScheduleValid (S : Schedule) : Prop :=
  ∀ τ i g repl, S τ = some (i, g, repl) → 1 ≤ g ∧ repl.length < g ∧ i + g ≤ τ.length

/-- The resident normalizer: repeatedly apply the schedule until it declines.
    Returns the normal form TOGETHER with the proof it is a fixed point — the
    subtype carries the halting obligation, so `normalize_is_normal` is definitional. -/
def normalizeWF (S : Schedule) (hS : ScheduleValid S) : Trace → { τ' : Trace // S τ' = none }
  | τ => match h : S τ with
         | none => ⟨τ, h⟩
         | some (i, g, repl) => normalizeWF S hS (edit τ i g repl)
termination_by τ => τ.length
decreasing_by
  have hv := hS τ i g repl h
  exact edit_shrinks τ i g repl hv.1 hv.2.1 hv.2.2

/-- The normal form of a tape under a valid schedule (Vox `reduce_resident`). -/
def normalize (S : Schedule) (hS : ScheduleValid S) (τ : Trace) : Trace :=
  (normalizeWF S hS τ).1

/-- HALTING: the resident reducer reaches a schedule-fixed point. This is the Lean
    form of Vox's `fixed point 966/966` from reduce_resident_cli. -/
theorem normalize_is_normal (S : Schedule) (hS : ScheduleValid S) (τ : Trace) :
    S (normalize S hS τ) = none := (normalizeWF S hS τ).2

end VoxResident
end Imscribing
