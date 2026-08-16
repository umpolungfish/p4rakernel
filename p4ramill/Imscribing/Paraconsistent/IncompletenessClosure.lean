import Imscribing.Paraconsistent.Belnap
/-!
# The incompleteness operator as a closure operator on the information order

`inc` augments a system with its own Gödel sentence: self-reference drives every
state to the dialetheia B.

The theorem this file exists for used to be stated as idempotence alone —
`inc (inc s) = inc s` — and that is TRUE but carries nothing, because `inc` is
constant and every constant map is idempotent. Idempotence is the leg you get for
free; it is not the claim.

The claim is that `inc` is a CLOSURE OPERATOR on the information order ≤_i, which
is three legs together:

  inflationary   a ≤ inc a          — augmentation never loses information
  monotone       a ≤ b → inc a ≤ inc b
  idempotent     inc (inc a) = inc a

The first leg is the one with content, and it needs the order to state at all: it
says that adding a system's own Gödel sentence moves it UP the information order
and never down. The third then follows from the first two plus the fixed point,
in the standard way, rather than from constancy.

Built on `Imscribing.Paraconsistent.Belnap`, whose ≤ is the approximation order
(N bottom; T and F below B; B top), so this is the corpus's Belnap and not a
second one.
-/

namespace Imscribing.Paraconsistent

/-- The incompleteness operator: augment a system with its Gödel sentence.
    N gains a truth-value it did not have; T and F gain the opposing value they
    could not have; B already carries both. -/
def inc : Belnap → Belnap
  | .N => .B
  | .T => .B
  | .F => .B
  | .B => .B

/-- Leg one, and the content: augmentation is INFLATIONARY on the information
    order. Nothing is lost by adding the Gödel sentence. -/
theorem inc_inflationary (a : Belnap) : a ≤ inc a := by
  cases a <;> first
    | exact ApproxLE.n_bot | exact ApproxLE.t_b
    | exact ApproxLE.f_b   | exact ApproxLE.b_refl

/-- Leg two: monotone in the information order. -/
theorem inc_monotone {a b : Belnap} (_ : a ≤ b) : inc a ≤ inc b := by
  cases a <;> cases b <;> exact ApproxLE.b_refl

/-- Leg three: idempotent. -/
theorem inc_idempotent (a : Belnap) : inc (inc a) = inc a := by
  cases a <;> rfl

/-- THE CLOSURE OPERATOR. The three legs together — this is the theorem; no one
    leg of it is. -/
theorem inc_is_closure_operator :
    (∀ a : Belnap, a ≤ inc a)
    ∧ (∀ a b : Belnap, a ≤ b → inc a ≤ inc b)
    ∧ (∀ a : Belnap, inc (inc a) = inc a) :=
  ⟨inc_inflationary, fun _ _ h => inc_monotone h, inc_idempotent⟩

/-- The mechanism, said plainly rather than left to be discovered: the image is
    the single point B. This is WHY idempotence is free, and stating it here is
    what stops the idempotence theorem from looking like more than it is. -/
theorem inc_image_is_B (a : Belnap) : inc a = .B := by
  cases a <;> rfl

/-- B is a fixed point, and the ONLY one — an iff, so it carries both directions
    rather than asserting the easy half. -/
theorem inc_fixed_point_iff (a : Belnap) : inc a = a ↔ a = .B := by
  constructor
  · intro h; rw [inc_image_is_B] at h; exact h.symm
  · intro h; subst h; rfl

/-- The closure is REACHED IN ONE STEP from anywhere: there is no state needing a
    second application, which is a stronger statement than idempotence and is the
    one that distinguishes this operator from a closure with a longer ascent. -/
theorem inc_closes_in_one_step (a : Belnap) : inc a = inc (inc a) := by
  cases a <;> rfl

/-- Every non-B state STRICTLY gains information: `a ≤ inc a` and `a ≠ inc a`.
    This is the inflationary leg sharpened, and it is what fails for a closure
    operator that fixes more than one point. -/
theorem inc_strict_below_B {a : Belnap} (h : a ≠ .B) : a ≤ inc a ∧ a ≠ inc a := by
  refine ⟨inc_inflationary a, ?_⟩
  rw [inc_image_is_B]; exact h

/-- Corollary, and the bridge to the bifurcation law: B is the unique closed
    state of the augmentation, so every δ that opens does so from the one place
    the operator can rest. -/
theorem unique_closed_state (a : Belnap) (h : inc a = a) : a = .B :=
  (inc_fixed_point_iff a).mp h

end Imscribing.Paraconsistent
