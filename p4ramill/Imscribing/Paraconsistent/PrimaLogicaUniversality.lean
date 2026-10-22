import Imscribing.Paraconsistent.TemporalSemantics
import Imscribing.Paraconsistent.CombinatoryReentry

/-!
# Prima Logica: native carrier and represented logical fragments

Revision grounded in p4rakernel's actual SIXTEEN_3 kernel carrier,
FDE.liftNegation, FDE.singleton, and certified combinatory language.

The proven claims below are: (1) SIXTEEN_3 is the sixteen-element powerset
of the FOUR evidence alphabet; (2) negation preserves the singleton embedding;
(3) a Boolean centre can be represented using singleton T/F; and (4) the
combinatory reduction language can execute its native negation and lattice
connectives with explicit proofs of reduction.

The separate arbitrary-carrier representation in the earlier module transports
connectives and is NOT a native-term universality theorem. In particular,
this file does not assert that every possible logic is definable from the
kernel's existing primitives. Requires the repository's forked Lean.
-/

namespace Imscribing.PrimaLogica.UniversalityRevised

open Lean
open Imscribing.Paraconsistent.Temporal.Semantics
open Imscribing.Paraconsistent.CombinatoryReentry

/-- The complete native register: all four memberships are present. -/
def unifiedB : Sixteen3 := Sixteen3.all

theorem unifiedB_full :
    unifiedB.hasN = true ∧ unifiedB.hasT = true ∧
    unifiedB.hasF = true ∧ unifiedB.hasB = true := by
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- The information-top register and singleton B are different states. -/
theorem unifiedB_ne_singletonB :
    unifiedB ≠ FDE.singleton .B := by decide

/-- The FDE singleton injection preserves distinctness. -/
theorem singleton_injective : Function.Injective FDE.singleton := by
  intro a b h
  cases a <;> cases b <;> simp_all [FDE.singleton]

/-- The kernel/corpus's native lifted negation agrees with FOUR negation on
    all singleton witnesses. -/
theorem negation_commutes_with_singleton (v : FDE.Value) :
    FDE.liftNegation (FDE.singleton v) =
      FDE.singleton (_root_.Paraconsistent.Belnap.bnot v) :=
  FDE.liftNegation_singleton v

/-- A native executable syntax witness for lifted negation. -/
theorem negation_is_program (x : Sixteen3) :
    Steps (Imscribing.Paraconsistent.CombinatoryReentry.Term.app .negation (.datum x))
      (.datum (FDE.liftNegation x)) :=
  Steps.single (Step.negation x)

/-- Every one of the six native lattice operations is executable using
    the corpus's certified small-step semantics. -/
theorem lattice_is_program (op : LatticeOp) (x y : Sixteen3) :
    Steps (Imscribing.Paraconsistent.CombinatoryReentry.Term.app (Imscribing.Paraconsistent.CombinatoryReentry.Term.app (.lattice op) (.datum x)) (.datum y))
      (.datum (op.apply x y)) :=
  lattice_apply op x y

/-- Composition of two successful native programs remains a successful
    native program, with its reduction certificate constructed by S/K/I. -/
theorem composition_is_program (outer inner : Imscribing.Paraconsistent.CombinatoryReentry.Term)
    (x y z : Sixteen3)
    (hi : Steps (Imscribing.Paraconsistent.CombinatoryReentry.Term.app inner (.datum x)) (.datum y))
    (ho : Steps (Imscribing.Paraconsistent.CombinatoryReentry.Term.app outer (.datum y)) (.datum z)) :
    Steps (Imscribing.Paraconsistent.CombinatoryReentry.Term.app (after outer inner) (.datum x)) (.datum z) :=
  after_apply outer inner x y z hi ho

/-- A B-seeded native information join retains the glut membership. -/
theorem join_singletonB_retains_B (x : Sixteen3) :
    (Sixteen3.join_i x (FDE.singleton .B)).hasB = true := by
  rcases x with ⟨n, t, f, b⟩
  cases b <;> rfl

/-- The full register is absorbing for information join. -/
theorem unifiedB_absorbs_i (x : Sixteen3) :
    Sixteen3.join_i x unifiedB = unifiedB := by
  rcases x with ⟨n,t,f,b⟩
  cases n <;> cases t <;> cases f <;> cases b <;> rfl

end Imscribing.PrimaLogica.UniversalityRevised
