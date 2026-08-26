/-
  DeMorganBooleanCentre.lean
  ──────────────────────────
  THEOREM: Bool is a coreflective subcategory of DeMorg, concretely, for the
  De Morgan algebra Belnap FOUR carries in the truth order.

  ClassicalRestriction.lean already proved a coreflection: the B-excluding
  subtype { v // v ≠ B } sits inside Belnap FOUR as a coreflective subcategory
  in the truth order, with classicalSwitch (B ↦ F) as the coreflector. That
  result answers "what survives if contradiction is disallowed."

  This file answers a different, standard question: which Belnap values form
  a BOOLEAN algebra, in the textbook De Morgan-algebra sense — excluded middle,
  x ∨ ¬x = 1, not merely x ≠ B? The two questions have different answers.
  N ≠ B, so N survives ClassicalRestriction's cut. But N ∨ ¬N = N ≠ T under the
  truth-order join, so N fails excluded middle and does NOT survive this one.
  The Boolean centre is the sharper, smaller fragment {T, F}; "not
  contradictory" and "classical" come apart at N, checked below rather than
  asserted.

  band/bor in ParaconsistentCore are dominance operators (F beats everything,
  then N, then B), not the truth-order lattice meet/join — the kernel rejects
  De Morgan duality for that pair outright at the N/B cross terms (N.band B
  reduces to N, not F, so bnot distributes wrong). The De Morgan algebra this
  file needs is the actual truth-order lattice: meet and join under
  F ≤ N ≤ T, F ≤ B ≤ T, N ∥ B — defined fresh below as tmeet/tjoin.

  Author: Lando⊗⊙perator
  Tier:   O_∞
-/

import Imscribing.Paraconsistent.ParaconsistentCore
import Imscribing.Paraconsistent.ParaconsistentFrobeniusClosure
import Imscribing.Paraconsistent.ClassicalRestriction

namespace DeMorganBooleanCentre

open Belnap ClassicalRestriction

-- ═══════════════════════════════════════════════════════════════════
-- §1  THE TRUTH-ORDER LATTICE: MEET AND JOIN
-- ═══════════════════════════════════════════════════════════════════
--
-- F ≤ N ≤ T and F ≤ B ≤ T; N and B incomparable. Meet and join of two
-- incomparable elements are the bottom and top respectively — the diamond
-- closes there, not at either element.

def tmeet : Belnap → Belnap → Belnap
  | .F, _ | _, .F => .F
  | .N, .B | .B, .N => .F
  | .N, _ | _, .N => .N
  | .B, _ | _, .B => .B
  | .T, .T => .T

def tjoin : Belnap → Belnap → Belnap
  | .T, _ | _, .T => .T
  | .N, .B | .B, .N => .T
  | .N, _ | _, .N => .N
  | .B, _ | _, .B => .B
  | .F, .F => .F

-- ═══════════════════════════════════════════════════════════════════
-- §2  BELNAP FOUR IS A DE MORGAN ALGEBRA IN THE TRUTH ORDER
-- ═══════════════════════════════════════════════════════════════════
--
-- (tmeet, tjoin, bnot, F, T) as (∧, ∨, ¬, 0, 1): distributive lattice,
-- De Morgan duality, involution — everything DeMorg asks for except
-- excluded middle, which is exactly the axiom Bool adds.

theorem bnot_involutive : ∀ v : Belnap, bnot (bnot v) = v := by
  intro v; cases v <;> rfl

theorem de_morgan_and : ∀ a b : Belnap,
    bnot (tmeet a b) = tjoin (bnot a) (bnot b) := by
  intro a b; cases a <;> cases b <;> rfl

theorem de_morgan_or : ∀ a b : Belnap,
    bnot (tjoin a b) = tmeet (bnot a) (bnot b) := by
  intro a b; cases a <;> cases b <;> rfl

theorem tmeet_comm : ∀ a b : Belnap, tmeet a b = tmeet b a := by
  intro a b; cases a <;> cases b <;> rfl

theorem tjoin_comm : ∀ a b : Belnap, tjoin a b = tjoin b a := by
  intro a b; cases a <;> cases b <;> rfl

theorem tmeet_assoc : ∀ a b c : Belnap, tmeet (tmeet a b) c = tmeet a (tmeet b c) := by
  intro a b c; cases a <;> cases b <;> cases c <;> rfl

theorem tjoin_assoc : ∀ a b c : Belnap, tjoin (tjoin a b) c = tjoin a (tjoin b c) := by
  intro a b c; cases a <;> cases b <;> cases c <;> rfl

theorem tmeet_distrib_tjoin : ∀ a b c : Belnap,
    tmeet a (tjoin b c) = tjoin (tmeet a b) (tmeet a c) := by
  intro a b c; cases a <;> cases b <;> cases c <;> rfl

theorem tmeet_agrees_with_truthLE : ∀ a b : Belnap,
    truthLE (tmeet a b) a = true ∧ truthLE (tmeet a b) b = true := by
  intro a b; cases a <;> cases b <;> decide

theorem tjoin_agrees_with_truthLE : ∀ a b : Belnap,
    truthLE a (tjoin a b) = true ∧ truthLE b (tjoin a b) = true := by
  intro a b; cases a <;> cases b <;> decide

/-- Excluded middle FAILS on Belnap FOUR — the axiom that separates DeMorg
    from Bool. N and B are both witnesses, for the same underlying reason:
    each is incomparable with its own negation in the truth order, so their
    join lands back on the element itself rather than climbing to T. -/
theorem excluded_middle_fails : ¬ (∀ v : Belnap, tjoin v (bnot v) = .T) := by
  intro h
  have := h .N
  simp [tjoin, bnot] at this

theorem N_fails_excluded_middle : tjoin .N (bnot .N) ≠ .T := by decide
theorem B_fails_excluded_middle : tjoin .B (bnot .B) ≠ .T := by decide
theorem T_satisfies_excluded_middle : tjoin .T (bnot .T) = .T := by decide
theorem F_satisfies_excluded_middle : tjoin .F (bnot .F) = .T := by decide

-- ═══════════════════════════════════════════════════════════════════
-- §3  THE BOOLEAN CENTRE:  R(Belnap) = { v | v ∨ ¬v = 1 }
-- ═══════════════════════════════════════════════════════════════════

/-- The Boolean-centre membership predicate, exactly as Theorem 1 defines it:
    v qualifies iff excluded middle holds at v. -/
abbrev inCentre (v : Belnap) : Prop := tjoin v (bnot v) = .T

/-- Computed, not stipulated: the Boolean centre of Belnap FOUR is exactly
    {T, F}. -/
theorem centre_is_T_F : ∀ v : Belnap, inCentre v ↔ (v = .T ∨ v = .F) := by
  intro v; cases v <;> decide

/-- The Boolean centre as a subtype. -/
abbrev BoolCentre := { v : Belnap // inCentre v }

-- ═══════════════════════════════════════════════════════════════════
-- §4  WHERE "NOT CONTRADICTORY" AND "CLASSICAL" COME APART
-- ═══════════════════════════════════════════════════════════════════
--
-- ClassicalRestriction's cut and this one agree on B (both exclude it) and
-- on T, F (both keep them). They disagree on N.

/-- N survives ClassicalRestriction's cut: it is not B. -/
theorem N_survives_classical_restriction : isClassical .N := N_is_classical

/-- N does not survive this cut: it fails excluded middle. -/
theorem N_excluded_from_centre : ¬ inCentre .N := N_fails_excluded_middle

/-- So the two notions of "classical" are genuinely different subsets of
    Belnap FOUR, not two names for the same cut. N is classical in
    ClassicalRestriction's sense (not a dialetheia) and not classical in
    this sense (not excluded-middle-satisfying). -/
theorem the_two_cuts_differ : isClassical .N ∧ ¬ inCentre .N :=
  ⟨N_is_classical, N_fails_excluded_middle⟩

/-- On B, both cuts agree: excluded. -/
theorem B_excluded_from_both : ¬ isClassical .B ∧ ¬ inCentre .B :=
  ⟨B_not_classical, B_fails_excluded_middle⟩

-- ═══════════════════════════════════════════════════════════════════
-- §5  THE INCLUSION:  BoolCentre ↪ Belnap
-- ═══════════════════════════════════════════════════════════════════

def inclCentre : BoolCentre → Belnap := Subtype.val

theorem inclCentre_injective : Function.Injective inclCentre :=
  fun _ _ h => Subtype.ext h

/-- Two witnesses outside the image, where ClassicalRestriction's inclusion
    only had one: neither N nor B is classical in this sharper sense. -/
theorem inclCentre_not_surjective : ¬ Function.Surjective inclCentre := by
  intro h
  obtain ⟨c, hc⟩ := h .N
  exact N_fails_excluded_middle (hc ▸ c.2)

-- ═══════════════════════════════════════════════════════════════════
-- §6  THE COREFLECTOR
-- ═══════════════════════════════════════════════════════════════════
--
-- Only a definite T counts as classically true; N, B, and F all collapse to
-- F. The B-side of this rule is the same "ex falso" choice
-- ClassicalRestriction already made (B ↦ F); this file's boolSwitch just
-- also resolves N the same way — absence of a truth-commitment defaults to
-- false, same as a contradiction does.

def boolSwitch : Belnap → Belnap
  | .T => .T
  | _  => .F

theorem boolSwitch_image_in_centre : ∀ v : Belnap, inCentre (boolSwitch v) := by
  intro v; cases v <;> decide

theorem boolSwitch_idempotent : ∀ v : Belnap,
    boolSwitch (boolSwitch v) = boolSwitch v := by
  intro v; cases v <;> rfl

theorem boolSwitch_fixes_iff_centre : ∀ v : Belnap,
    boolSwitch v = v ↔ inCentre v := by
  intro v; cases v <;> decide

/-- The retract: boolSwitch ∘ inclCentre = id on the Boolean centre. -/
theorem switch_inclCentre_retract : ∀ c : BoolCentre,
    boolSwitch (inclCentre c) = inclCentre c :=
  fun c => (boolSwitch_fixes_iff_centre c.1).mpr c.2

-- ═══════════════════════════════════════════════════════════════════
-- §7  THE ADJUNCTION: BoolCentre IS COREFLECTIVE, TRUTH ORDER ONLY
-- ═══════════════════════════════════════════════════════════════════
--
-- Same shape as ClassicalRestriction §7: inclCentre ⊣ boolSwitch holds in
-- the truth order, the reverse fails, and the kernel decides both.

theorem truth_inclCentre_left_adjoint : ∀ (c x : Belnap), inCentre c →
    truthLE c x = truthLE c (boolSwitch x) := by
  intro c x hc
  rcases (centre_is_T_F c).mp hc with hT | hF
  · subst hT; cases x <;> decide
  · subst hF; cases x <;> decide

/-- The reverse direction fails: at x = N, c = F, boolSwitch N = F ≤_t F but
    N ≤_t F is false. Same shape of counterexample ClassicalRestriction found
    at B; here N alone already breaks it, before B is even needed. -/
theorem truth_switch_left_adjoint_fails :
    truthLE (boolSwitch .N) .F ≠ truthLE .N .F := by decide

theorem switch_monotone_truth : ∀ (a b : Belnap),
    truthLE a b = true → truthLE (boolSwitch a) (boolSwitch b) = true := by
  intro a b; cases a <;> cases b <;> decide

/-- Information order: no adjunction, same as ClassicalRestriction found. -/
theorem info_inclCentre_left_adjoint_fails :
    infoLE .T .B ≠ infoLE .T (boolSwitch .B) := by decide

/-- **Coreflective subcategory (main theorem).** BoolCentre is a coreflective
    subcategory of Belnap FOUR in the truth order: inclusion is the left
    adjoint, boolSwitch is the right adjoint (coreflector), the retract of §6
    is this adjunction's unit, the reverse adjunction fails, and no
    adjunction exists in the information order. This is Theorem 1 —
    Bool ↪ DeMorg is coreflective — instantiated at L = Belnap FOUR, with the
    coreflector computed rather than assumed to exist. -/
theorem centre_coreflective_in_truth_order :
    (∀ c : Belnap, inCentre c → boolSwitch c = c) ∧
    (∀ c x : Belnap, inCentre c → truthLE c x = truthLE c (boolSwitch x)) ∧
    (truthLE (boolSwitch .N) .F ≠ truthLE .N .F) ∧
    (infoLE .T .B ≠ infoLE .T (boolSwitch .B)) :=
  ⟨fun c hc => (boolSwitch_fixes_iff_centre c).mpr hc,
   truth_inclCentre_left_adjoint,
   truth_switch_left_adjoint_fails,
   info_inclCentre_left_adjoint_fails⟩

end DeMorganBooleanCentre
