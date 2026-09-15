/-
  IMASM16_3Machine.lean
  THE WORD-TO-VERDICT OPERATOR
  =====================================================================
  Author: Lando⊗⊙perator

  `DialetheicWitness.lean` gives the sound return type for a real B-state
  (`Verdict.held`, two independently proved facts about the same object).
  Its own worked instances (`engagrVerdict`, `cosmicHolonomyVerdict`) are
  each built by hand for one fixed object. This file is the operator that
  removes the hand-authoring: run ANY glyph word through the real
  IMASM-16_3 register machine (faithful Lean port of
  `ob3ect/digital/imasm16_3_core.py`'s `IMASM16_3_Machine.transition`,
  checked opcode-for-opcode against that source, not re-derived from
  memory) and get back, automatically, a genuine `Verdict` when the walk
  actually lands on both bigT and bigF -- and `none` when it doesn't.

  This is the reusable Lean-level thing: feed it a word, not a per-object
  proof.
-/

import Imscribing.Paraconsistent.SixteenThreeTrilattice
import Imscribing.Paraconsistent.DialetheicWitness

namespace Imscribing.Paraconsistent.IMASM16_3Machine

open Reg16_3
open Imscribing.Paraconsistent.DialetheicWitness

-- ═══════════════════════════════════════════════════════════════════
-- §1  THE TWELVE OPCODES
-- ═══════════════════════════════════════════════════════════════════

/-- The twelve IMASM-16_3 opcodes, named exactly as
    `ob3ect/digital/imasm16_3_core.py` names them. -/
inductive Mark16_3 : Type where
  | VINIT | TANCH | AFWD | AREV | CLINK | EVALT
  | FSPLIT3 | FFUSE3 | IMSCRIB | EVALF | EVALI | IFIX
  deriving DecidableEq, Repr

open Mark16_3

/-- Glyph → opcode, the same twelve marks the wire form uses. -/
def Mark16_3.ofChar : Char → Option Mark16_3
  | '⊢' => some .VINIT
  | '⊣' => some .TANCH
  | '≻' => some .AFWD
  | '≺' => some .AREV
  | '⋈' => some .CLINK
  | '⊤' => some .EVALT
  | '∈' => some .FSPLIT3
  | '∋' => some .FFUSE3
  | '⊙' => some .IMSCRIB
  | '⊥' => some .EVALF
  | '⊞' => some .EVALI
  | '⊡' => some .IFIX
  | _   => none

/-- A glyph word (e.g. an ob3ect's `glyph_word` field) parsed into opcodes.
    Any character outside the twelve marks is dropped, exactly as the
    Python side's grammar has no alias or shim for a stray symbol. -/
def parseWord (s : String) : List Mark16_3 :=
  s.toList.filterMap Mark16_3.ofChar

-- ═══════════════════════════════════════════════════════════════════
-- §2  THE MACHINE STATE
-- ═══════════════════════════════════════════════════════════════════

/-- `emptyReg`: the register with no lane touched (Python's `EMPTY`). -/
def emptyReg : Reg16_3 := mk false false false false

/-- Mirrors `IMASM16_3_Machine`'s three fields exactly: the register, the
    `fixed` latch set by IFIX, and the fork stack that FSPLIT3 pushes onto
    and FFUSE3 pops (tracking which lanes each open fork's arms touched,
    so nested regions compose the way the Python docstring describes). -/
structure MachineState where
  reg   : Reg16_3
  fixed : Bool
  stack : List Reg16_3
  deriving DecidableEq, Repr

def initState : MachineState := { reg := emptyReg, fixed := false, stack := [] }

/-- `_touch` in the Python source: OR `v` into the register, and into the
    innermost open fork frame if one is open. -/
def touch (s : MachineState) (v : Reg16_3) : MachineState :=
  { s with
    reg := union s.reg v
    stack := match s.stack with
      | []          => []
      | top :: rest => union top v :: rest }

/-- The one-opcode transition, faithful to `IMASM16_3_Machine.transition`:
    VINIT resets both register and fork stack; TANCH/CLINK are no-ops;
    AFWD/IMSCRIB set T only from a genuinely empty register; AREV clears
    the register but leaves the fork stack alone (work on an arm is not a
    fuse); FSPLIT3 pushes an empty frame; FFUSE3 pops one, folds it into
    the register, and folds it into the new top frame if one remains;
    EVALT/EVALF/EVALI touch T, F, and {t,f} respectively; IFIX latches
    `fixed`. -/
def stepInner (s : MachineState) (m : Mark16_3) : MachineState :=
  match m with
  | .VINIT   => { s with reg := emptyReg, stack := [] }
  | .TANCH   => s
  | .AFWD    => if s.reg = emptyReg then { s with reg := mk true false false false } else s
  | .AREV    => { s with reg := emptyReg }
  | .CLINK   => s
  | .IMSCRIB => if s.reg = emptyReg then { s with reg := mk true false false false } else s
  | .FSPLIT3 => { s with stack := emptyReg :: s.stack }
  | .FFUSE3  =>
      match s.stack with
      | []          => s
      | top :: rest =>
          let s' : MachineState := { s with reg := union s.reg top, stack := rest }
          match rest with
          | []        => s'
          | r :: rest' => { s' with stack := union r top :: rest' }
  | .EVALT   => touch s (mk true false false false)
  | .EVALF   => touch s (mk false true false false)
  | .EVALI   => touch s (mk false false true true)
  | .IFIX    => { s with fixed := true }

/-- `if self.fixed and token not in (IFIX, IMSCRIB): return self.reg` --
    once fixed, every opcode except IFIX and IMSCRIB is a no-op. -/
def step (s : MachineState) (m : Mark16_3) : MachineState :=
  match s.fixed, m with
  | true, .IFIX    => stepInner s m
  | true, .IMSCRIB => stepInner s m
  | true, _        => s
  | false, _       => stepInner s m

/-- Run a word from the initial state, left to right. -/
def run (word : List Mark16_3) : MachineState :=
  word.foldl step initState

/-- The register the walk ends on. -/
def finalReg (word : List Mark16_3) : Reg16_3 :=
  (run word).reg

-- ═══════════════════════════════════════════════════════════════════
-- §3  THE OPERATOR: WORD → Verdict, AUTOMATICALLY
-- ═══════════════════════════════════════════════════════════════════

/-- The reusable operator. Any word, run through the real machine: if the
    walk lands with both bigT and bigF genuinely set, this returns a real
    `Verdict.held` -- two independently proved facts about the same final
    register, decided by the machine's own computation, not asserted. If
    the walk doesn't land there, this returns `none` rather than
    manufacture a witness the walk did not earn. -/
def wordVerdict? (word : List Mark16_3) :
    Option (Verdict ((finalReg word).bigT = true)) :=
  if h : (finalReg word).bigT = true ∧ (finalReg word).bigF = true then
    some (.held h.1 h.2)
  else
    none

/-- The classifier reads a produced witness as B, mechanically, the same
    read `DialetheicWitness`'s other instances get. -/
theorem wordVerdict_some_is_B (word : List Mark16_3) (v : Verdict ((finalReg word).bigT = true))
    (h : wordVerdict? word = some v) : v.classify = (true, true) := by
  unfold wordVerdict? at h
  split at h
  · injection h with h'; subst h'; rfl
  · exact absurd h (by simp)

-- ═══════════════════════════════════════════════════════════════════
-- §4  CHECKED AGAINST THE FIVE REAL OB3ECT WORDS
-- ═══════════════════════════════════════════════════════════════════

-- KastrupConformalGroup: canonical word, checked live against
-- ob3ect/digital/kastrupconformalgroup/kastrupconformalgroup_ob3ect.json
-- (rotat_audit k=0, final_register "A") and against the real Python
-- machine run in-session, both landing on the full register.
theorem kastrup_final_register :
    finalReg (parseWord "⊢∈≻⊤≺⊥⋈⊙⊞∋⊡⋈⊙⊣") = mk true true true true := by decide

theorem kastrup_has_witness :
    (wordVerdict? (parseWord "⊢∈≻⊤≺⊥⋈⊙⊞∋⊡⋈⊙⊣")).isSome := by decide

-- GlattfelderSelfContainmentPrinciple: same check.
theorem glattfelder_final_register :
    finalReg (parseWord "⊢∈⊤≻⊥≺⋈⊞∋⊙⊡⋈⊣⊙⊡") = mk true true true true := by decide

theorem glattfelder_has_witness :
    (wordVerdict? (parseWord "⊢∈⊤≻⊥≺⋈⊞∋⊙⊡⋈⊣⊙⊡")).isSome := by decide

-- ScholzeStixBooleanProjectionAtO2: same check.
theorem scholzestix_final_register :
    finalReg (parseWord "⊢⋈≻⊙∈⊤⊥⊞≺⋈∋⊡⊣") = mk true true true true := by decide

theorem scholzestix_has_witness :
    (wordVerdict? (parseWord "⊢⋈≻⊙∈⊤⊥⊞≺⋈∋⊡⊣")).isSome := by decide

-- The original INTER-UNIVERSAL TEICHMULLER THEORY gate-check word: same check.
theorem iut_class_final_register :
    finalReg (parseWord "⊢⊢⊢⊢∈≻⊤⋈⊙≺⊥⊞⋈∋⊡⊣") = mk true true true true := by decide

theorem iut_class_has_witness :
    (wordVerdict? (parseWord "⊢⊢⊢⊢∈≻⊤⋈⊙≺⊥⊞⋈∋⊡⊣")).isSome := by decide

-- IUTClosedWalkAtOInfinity (my own prompted word, this session): checked
-- to NOT produce a witness. Its walk clears the register with AREV right
-- before the final fuse and never re-touches T, so bigT is false on the
-- closing register -- `wordVerdict?` returns `none` rather than
-- manufacture a held state the walk did not reach.
theorem iutclosedwalkatoinfinity_final_register :
    finalReg (parseWord "⊢∈≻⊤⋈≺⊥⊞⋈⊙⊡∋⋈⊙⊣") = mk false true true true := by decide

theorem iutclosedwalkatoinfinity_no_witness :
    wordVerdict? (parseWord "⊢∈≻⊤⋈≺⊥⊞⋈⊙⊡∋⋈⊙⊣") = none := by decide

end Imscribing.Paraconsistent.IMASM16_3Machine
