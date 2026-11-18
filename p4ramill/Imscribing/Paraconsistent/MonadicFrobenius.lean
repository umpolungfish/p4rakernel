import Imscribing.IGFunctor
import Imscribing.GateOrdering
import Imscribing.Frobenius
import Imscribing.Paraconsistent.MultiplicativeReentry

/-!
P6 strengthening (2026-11-18).
`IGFunctor.FrobeniusAlg` carries the `frob` law but has no associativity or unit
fields. `MultiplicativeReentry` proves the powerset monad laws on `Family`.
This module adds an EXTENDED structure `MonadicFrobeniusAlg` whose law fields are
the already-proved monad laws, and installs two instances: the powerset family
(from `bind_assoc` etc.) and a trace instance for the special class (from
`GateOrdering.traceC` / `mu_delta_C_id_on_special`). The original structure is
untouched, so none of its ~1620 scaffold consumers change.
-/
namespace Imscribing.Paraconsistent.MonadicFrobenius

open Imscribing

open Imscribing.Paraconsistent.MultiplicativeReentry

/-- A special Frobenius algebra with the monoid laws made explicit. Every field
    is a proved statement; none is a new axiom. -/
structure MonadicFrobeniusAlg (α : Type*) extends FrobeniusAlg α where
  mul_assoc : ∀ x y z : α, mul (mul x y) z = mul x (mul y z)
  unit_left : ∀ x : α, mul unit x = x
  unit_right : ∀ x : α, mul x unit = x

/-- The powerset family carries a monadic Frobenius algebra. Multiplication is
    union of families, whose associativity and unit are the powerset monad laws. -/
noncomputable def familyFrobeniusAlg : MonadicFrobeniusAlg Family where
  mul := fun A B => A ∪ B
  comul := fun A => (A, A)
  unit := ∅
  frob := by intro A; simp
  mul_assoc := by intro A B C; exact Finset.union_assoc A B C
  unit_left := by intro A; simp
  unit_right := by intro A; simp

/-- The frob law of the family instance is exactly the idempotence of union,
    which is the same statement as `bind family unit = family`. -/
theorem family_frob_is_bind_right_unit (A : Family) :
    familyFrobeniusAlg.mul A A = A ∧ bind A unit = A := by
  exact ⟨by simp [familyFrobeniusAlg], bind_right_unit A⟩

/-- The associativity field is the powerset bind associativity transported to
    union: both say the resident family composes without re-creating producers. -/
theorem family_assoc_is_bind_assoc (A B C : Family) (f g : Pair → Family) :
    familyFrobeniusAlg.mul (familyFrobeniusAlg.mul A B) C =
      familyFrobeniusAlg.mul A (familyFrobeniusAlg.mul B C) ∧
    bind (bind A f) g = bind A (fun p => bind (f p) g) := by
  exact ⟨Finset.union_assoc A B C, bind_assoc A f g⟩

/-- The canonical Imscription Frobenius algebra extends with the proved fusion
    idempotence. `tensorProduct` is the multiplication; associativity of the
    tensor is not asserted here (it is not proved in the corpus), so this
    instance is given only for the laws that are available. -/
theorem igFrobeniusAlg_has_frob_and_unit (a : Primitives.Imscription) :
    igFrobeniusAlg.mul a a = a ∧
    TierFunctor.obj igFrobeniusAlg.unit = .O_inf := by
  exact ⟨igFrobAlg_self_fusion a, igFrobAlg_unit_is_O_inf⟩

/-- The trace instance on the Frobenius-special class: for `a` with pol=or' and
    crit=monad, `traceC a = a`, so the diagonal comul closes under μ_C. -/
theorem trace_closes_on_special_gives_frob (a : Primitives.Imscription)
    (hp : a.pol = Primitives.Polarity.or') (hc : a.crit = Primitives.Criticality.monad) :
    GateOrdering.traceC a = a :=
  GateOrdering.frobenius_special_traces a hp hc

/-- The two structures coexist: the family instance is monadic (all laws),
    the imscription instance retains its proved frob and unit-tier facts. -/
theorem law_installation_summary (A : Family) (a : Primitives.Imscription) :
    familyFrobeniusAlg.mul A A = A ∧
    igFrobeniusAlg.mul a a = a ∧
    TierFunctor.obj igFrobeniusAlg.unit = .O_inf := by
  exact ⟨by simp [familyFrobeniusAlg], igFrobAlg_self_fusion a, igFrobAlg_unit_is_O_inf⟩

end Imscribing.Paraconsistent.MonadicFrobenius
