import Imscribing.Paraconsistent.TemporalSemantics
import Imscribing.Paraconsistent.CombinatoryReentry

/-!
# Native SIXTEEN_3 expressivity, revised for p4rakernel

Uses the *actual* kernel carrier and the corpus's implemented FDE negation and
certified S/K/I reduction. The six primitive meets/joins have coordinate-local
semantics; the kernel/corpus language does NOT consist of those six operations
alone. In particular, lifted negation exchanges T and F memberships.

This file deliberately makes no claim that arbitrary finite-valued operations
are definable by the six meets/joins or by all currently available primitives.
No `sorry` or fresh axiom is used. Requires the repository's forked Lean.
-/

namespace Imscribing.PrimaLogica.NativeExpressivityRevised

open Lean
open Imscribing.Paraconsistent.Temporal.Semantics
open Imscribing.Paraconsistent.CombinatoryReentry

/-- Identifies the primitive SIXTEEN_3 lattice operations in the repository. -/
abbrev LatticeOp := Imscribing.Paraconsistent.CombinatoryReentry.LatticeOp

/-- Every lattice operation is coordinate-local at the T membership. -/
theorem lattice_T_local (op : LatticeOp)
    (x x' y y' : Sixteen3)
    (hx : x.hasT = x'.hasT) (hy : y.hasT = y'.hasT) :
    (op.apply x y).hasT = (op.apply x' y').hasT := by
  cases op <;> simp only [LatticeOp.apply, Sixteen3.join_i,
    Sixteen3.meet_i, Sixteen3.join_t, Sixteen3.meet_t,
    Sixteen3.join_f, Sixteen3.meet_f] <;> simp [hx, hy]

/-- SIXTEEN_3 lifted FDE negation accesses another coordinate. -/
theorem native_negation_exchanges_T_F (x : Sixteen3) :
    (FDE.liftNegation x).hasT = x.hasF ∧
    (FDE.liftNegation x).hasF = x.hasT := by
  cases x
  exact ⟨rfl, rfl⟩

/-- In particular, the T coordinate of lifted negation need not be local
    in the input's T coordinate. -/
theorem lifted_negation_not_T_local :
    ¬ (∀ x y : Sixteen3, x.hasT = y.hasT →
        (FDE.liftNegation x).hasT = (FDE.liftNegation y).hasT) := by
  intro h
  have heq := h (Sixteen3.ofBelnap false false false false)
    (Sixteen3.ofBelnap false false true false) rfl
  change false = true at heq
  cases heq

/-- Actual corpus reduction witnesses that lifted negation is executable. -/
theorem certified_negation (x : Sixteen3) :
    Steps (Imscribing.Paraconsistent.CombinatoryReentry.Term.app .negation (.datum x))
      (.datum (FDE.liftNegation x)) :=
  Steps.single (Step.negation x)

/-- The three native lattice orders also execute with reduction witnesses. -/
theorem certified_lattice (op : LatticeOp) (x y : Sixteen3) :
    Steps (Imscribing.Paraconsistent.CombinatoryReentry.Term.app (Imscribing.Paraconsistent.CombinatoryReentry.Term.app (.lattice op) (.datum x)) (.datum y))
      (.datum (op.apply x y)) :=
  lattice_apply op x y

/-- S/K/I computes composition using proved reduction, not a mere
    externally transported operation. -/
theorem certified_composition (outer inner : Imscribing.Paraconsistent.CombinatoryReentry.Term)
    (x y z : Sixteen3)
    (hi : Steps (Imscribing.Paraconsistent.CombinatoryReentry.Term.app inner (.datum x)) (.datum y))
    (ho : Steps (Imscribing.Paraconsistent.CombinatoryReentry.Term.app outer (.datum y)) (.datum z)) :
    Steps (Imscribing.Paraconsistent.CombinatoryReentry.Term.app (after outer inner) (.datum x)) (.datum z) :=
  after_apply outer inner x y z hi ho

end Imscribing.PrimaLogica.NativeExpressivityRevised
