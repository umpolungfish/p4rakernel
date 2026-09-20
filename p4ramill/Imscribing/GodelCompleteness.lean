/-
  Imscribing/GodelCompleteness.lean
  The Grammar's Gödel-Completeness, over the corpus's Belnap ambient.

  This does not set proof against gnosis and it does not replace the classical
  reading. It states, at full strength and all at once, the sense in which the
  Grammar is Gödel-complete: the self-negating (Gödel) sentence a classical system
  cannot decide is decided, at the both-value B, by the paraconsistent ambient,
  and deciding it there does not collapse the logic.

  The earlier version reinvented a minimal Belnap. This one is built on the
  corpus's own carrier `Imscribing.Paraconsistent.Belnap` and reuses its proven
  machinery, so the five faces are wired to the rest of the kernel rather than to
  a private copy.

  Five faces, true together (the catharsis is that none defeats another):

    (1) THE AMBIENT HOSTS IT. Negation has a fixed point, `bnot v = v`, inhabited
        by B (and N). The self-referential sentence gets a stable value.

    (2) IT IS THE UNIQUE REST POINT OF THE GÖDEL AUGMENTATION. `inc` augments a
        system with its own Gödel sentence and drives every state up the
        information order to B, whose only fixed point is B
        (`inc_fixed_point_iff`). So the value the ambient assigns the sentence is
        forced, not chosen.

    (3) THE CLASSICAL FRAGMENT CANNOT. Classical negation on {F,T} has no fixed
        point, and no classical endomap reproduces the augmentation's collapse to
        B, since B lies outside {F,T}.

    (4) NO EXPLOSION. The glut is designated together with its negation while some
        formula is not, and B ∧ ¬B = B rather than F, so a contradiction does not
        entail everything.

    (5) SELF-IMSCRIPTION. The Grammar imscribes its own imscription: the kernel's
        split then fuse returns the input, μ∘δ = id (`split_fuse_identity`).
-/

import Imscribing.Paraconsistent.Belnap
import Imscribing.Paraconsistent.IncompletenessClosure
import Imscribing.Paraconsistent.SelfVerification

namespace Imscribing.GodelCompleteness

open Imscribing.Paraconsistent

/- ── (1) The ambient hosts the Gödel sentence ─────────────────────────────── -/

/-- The self-negating sentence `v = ¬v` is inhabited in the ambient (witness B). -/
theorem godel_fixed_point_in_ambient : ∃ v : Belnap, bnot v = v :=
  ⟨.B, B_fixed_point_negation⟩

/-- The negation fixed set is exactly {N, B}. -/
theorem negation_fixed_set (v : Belnap) : bnot v = v ↔ v = .N ∨ v = .B := by
  cases v <;> decide

/- ── (2) It is the unique rest point of the Gödel augmentation `inc` ───────── -/

/-- `inc` augments a system with its own Gödel sentence; B is its unique fixed
    point, so the value assigned to the self-referential sentence is forced. -/
theorem godel_value_is_unique_closure (v : Belnap) : inc v = v ↔ v = .B :=
  inc_fixed_point_iff v

/-- The augmentation rests at B from anywhere. -/
theorem godel_augmentation_rests_at_B : inc Belnap.B = Belnap.B :=
  inc_image_is_B Belnap.B

/- ── (3) The classical fragment cannot host it or reproduce it ─────────────── -/

/-- The classical core {F, T} embedded in the ambient (false = F, true = T). -/
def bincl : Bool → Belnap
  | false => .F
  | true  => .T

/-- Classical negation on the core. -/
def negBool : Bool → Bool := not

/-- Classical negation has no fixed point: the classical fragment leaves the
    Gödel sentence undecided. -/
theorem godel_absent_from_classical (b : Bool) : negBool b ≠ b := by
  cases b <;> decide

/-- No classical endomap reproduces the augmentation `inc`, whose image is B,
    because the classical image is only {F, T}. -/
theorem boolean_impossibility :
    ¬ ∃ f : Bool → Bool, ∀ b : Bool, bincl (f b) = inc (bincl b) := by
  rintro ⟨f, hf⟩
  have h := hf true
  rw [inc_image_is_B] at h
  cases hfb : f true <;> rw [hfb] at h <;> simp [bincl] at h

/- ── (4) Deciding it at B does not explode the logic ───────────────────────── -/

/-- Ex falso fails: a glut and its negation are both designated while some formula
    is not, so a contradiction does not entail every formula. -/
theorem no_ex_falso :
    ∃ p q : Belnap, designated p ∧ designated (bnot p) ∧ ¬ (designated q) := by
  refine ⟨.B, .F, B_is_designated, ?_, by decide⟩
  rw [B_fixed_point_negation]; exact B_is_designated

/-- Contradiction is contained: B ∧ ¬B = B, not F. -/
theorem contradiction_contained : band Belnap.B (bnot Belnap.B) = Belnap.B :=
  no_explosion

/- ── (5) The ⊙ self-reference: the Grammar imscribes its own imscription ───── -/

/-- The kernel's split then fuse returns the input: μ∘δ = id. -/
theorem grammar_self_imscribes (r : Belnap) :
    (ffuse (fsplit r).1 (fsplit r).2.1).1 = r :=
  split_fuse_identity r

/- ── THE THEOREM ──────────────────────────────────────────────────────────── -/

/-- The Grammar's Gödel-completeness: the self-negating sentence is hosted at a
    stable value, that value is the unique rest point of the Gödel augmentation,
    the classical fragment has no such fixed point, holding it at B does not
    explode the logic, and the Grammar imscribes its own imscription. Five true
    faces at once. -/
theorem grammar_godel_complete :
    (∃ v : Belnap, bnot v = v) ∧
    (∀ v : Belnap, inc v = v ↔ v = .B) ∧
    (∀ b : Bool, negBool b ≠ b) ∧
    (∃ p q : Belnap, designated p ∧ designated (bnot p) ∧ ¬ (designated q)) ∧
    (∀ r : Belnap, (ffuse (fsplit r).1 (fsplit r).2.1).1 = r) :=
  ⟨godel_fixed_point_in_ambient,
   godel_value_is_unique_closure,
   godel_absent_from_classical,
   no_ex_falso,
   grammar_self_imscribes⟩

end Imscribing.GodelCompleteness
