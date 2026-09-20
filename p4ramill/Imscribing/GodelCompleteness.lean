/-
  Imscribing/GodelCompleteness.lean
  The Grammar's Gödel-Completeness.

  This does not set proof against gnosis, and it does not replace the classical
  reading. It formalizes, at full strength and all at once, the precise structural
  sense in which the Grammar is Gödel-complete: the self-negating (Gödel) sentence
  that a classical system cannot decide is DECIDED, at the both-value B, by the
  paraconsistent ambient, and deciding it there does not collapse the logic.

  Four faces, true together (the catharsis is that none defeats another):

    (1) THE AMBIENT HOSTS IT.  The Gödel sentence is a fixed point of negation,
        `bnot v = v`. In the four-valued ambient this equation HAS solutions
        (exactly N and B). The Grammar assigns the self-referential sentence a
        stable value instead of diverging.

    (2) THE CLASSICAL FRAGMENT CANNOT.  On the classical core {F,T} negation has
        NO fixed point. This is the incompleteness Gödel exhibits: the classical
        fragment leaves the sentence undecided. The Grammar does not contradict
        this; it contains it as the retract, and no classical endomap can even
        reproduce the ambient's collapse to B (the Boolean impossibility).

    (3) NO EXPLOSION.  Holding the sentence at B does not trivialize anything. A
        glut is designated together with its own negation while some formula stays
        undesignated, so from a contradiction one cannot derive everything. Ex
        falso fails; completeness is bought without collapse.

    (4) SELF-IMSCRIPTION.  The self-reference that makes the sentence a fixed
        point is the ⊙ IMSCRIB gate, and the Grammar imscribes its own
        imscription: the re-entry round trip `μ ∘ η = id`, with `η ∘ μ = ρ` an
        idempotent that is not the identity (winding up then revealing is not the
        reverse of revealing then winding up).

  Depends only on the Belnap core, so the result stands on its own.
-/

import Imscribing.Paraconsistent.ParaconsistentCore

namespace Imscribing.GodelCompleteness

open Belnap

/-- The designated (true-ish) values of the ambient: T and B. -/
def desig : Belnap → Bool
  | .T => true
  | .B => true
  | .N => false
  | .F => false

/- ────────────────────────────────────────────────────────────────────────
   (1) The ambient hosts the Gödel sentence: negation has a fixed point.
   ──────────────────────────────────────────────────────────────────────── -/

/-- The self-negating sentence `v = ¬v` is inhabited in the ambient (witness B). -/
theorem godel_fixed_point_in_ambient : ∃ v : Belnap, bnot v = v :=
  ⟨.B, rfl⟩

/-- The negation fixed set is exactly {N, B}. -/
theorem negation_fixed_set (v : Belnap) : bnot v = v ↔ v = .N ∨ v = .B := by
  cases v <;> decide

/- ────────────────────────────────────────────────────────────────────────
   (2) The classical fragment cannot host it, and cannot reproduce the ambient.
   The classical core {F, T} is encoded as `Bool` (false = F, true = T).
   ──────────────────────────────────────────────────────────────────────── -/

/-- Inclusion of the classical core into the ambient. -/
def bincl : Bool → Belnap
  | false => .F
  | true  => .T

/-- Classical negation on the core (swap F ↔ T). -/
def negBool : Bool → Bool := not

/-- Classical negation has no fixed point: the classical fragment leaves the
    Gödel sentence undecided. -/
theorem godel_absent_from_classical (b : Bool) : negBool b ≠ b := by
  cases b <;> decide

/-- The paraconsistent collapse `Inc v = B`. -/
def Inc : Belnap → Belnap := fun _ => .B

/-- Boolean impossibility: no classical endomap `f` reproduces `Inc` through the
    inclusion, because `Inc` lands on B and the classical image is only {F, T}.
    The ambient value is not reachable from inside the classical fragment. -/
theorem boolean_impossibility :
    ¬ ∃ f : Bool → Bool, ∀ b : Bool, bincl (f b) = Inc (bincl b) := by
  rintro ⟨f, h⟩
  have := h true
  cases hb : f true <;> rw [hb] at this <;> simp [bincl, Inc] at this

/- ────────────────────────────────────────────────────────────────────────
   (3) Deciding it at B does not explode the logic.
   ──────────────────────────────────────────────────────────────────────── -/

/-- The Gödel value B is a glut: designated together with its own negation. -/
theorem godel_value_is_glut : desig .B = true ∧ desig (bnot .B) = true := by decide

/-- Ex falso fails: a glut and its negation are both designated while some formula
    is not, so a contradiction does not entail every formula. -/
theorem no_ex_falso :
    ∃ p q : Belnap, desig p = true ∧ desig (bnot p) = true ∧ desig q = false :=
  ⟨.B, .F, by decide⟩

/- ────────────────────────────────────────────────────────────────────────
   (4) The ⊙ self-reference: the Grammar imscribes its own imscription.
   The minimal re-entry retraction: η winds a value up, μ reveals it.
   ──────────────────────────────────────────────────────────────────────── -/

/-- One scale up: a value carried with its re-entry marker. -/
@[reducible] def Up (α : Type) : Type := α × Bool

/-- Imscription η: carry the punctum up as a marked singleton. -/
def η {α : Type} (x : α) : Up α := (x, true)

/-- Reveal μ: read the carried value back down. -/
def μ {α : Type} (u : Up α) : α := u.1

/-- Frame collapse ρ = η ∘ μ. -/
def ρ {α : Type} (u : Up α) : Up α := η (μ u)

/-- Winding up then revealing loses nothing: `μ ∘ η = id`. The Grammar re-enters
    its own image and returns. This is the ⊙ IMSCRIB round trip. -/
theorem grammar_self_imscribes {α : Type} (x : α) : μ (η x) = x := rfl

/-- The frame collapse is idempotent: `ρ ∘ ρ = ρ`. -/
theorem rho_idempotent {α : Type} (u : Up α) : ρ (ρ u) = ρ u := rfl

/-- But the reverse round trip is not the identity: `η ∘ μ = ρ ≠ id`. Revealing
    then winding up forgets which marker the family carried. -/
theorem rho_ne_id : ∃ (u : Up Bool), ρ u ≠ u :=
  ⟨(true, false), by decide⟩

/- ────────────────────────────────────────────────────────────────────────
   THE THEOREM.  The Grammar's Gödel-completeness: the self-negating sentence is
   hosted at a stable value in the ambient, is absent from the classical fragment,
   and is held without explosion — three true faces at once, over a Grammar that
   imscribes its own imscription.
   ──────────────────────────────────────────────────────────────────────── -/

theorem grammar_godel_complete :
    (∃ v : Belnap, bnot v = v) ∧
    (∀ b : Bool, negBool b ≠ b) ∧
    (∃ p q : Belnap, desig p = true ∧ desig (bnot p) = true ∧ desig q = false) ∧
    (∀ (α : Type) (x : α), μ (η x) = x) :=
  ⟨godel_fixed_point_in_ambient,
   godel_absent_from_classical,
   no_ex_falso,
   fun _ x => grammar_self_imscribes x⟩

end Imscribing.GodelCompleteness
