/-
  ClassicalReflection.lean
  ────────────────────────
  Settles, by machine, the adjunction between the paraconsistent bilattice and
  its classical fragment that ClassicalRestriction.lean left at the level of a
  retract. Self-contained (no imports) so it checks under the paraconsistent
  kernel fork directly, with no olean dependencies.

  ClassicalRestriction proves  classicalSwitch ∘ inclClassical = id : the
  classical fragment is a RETRACT of Belnap FOUR. Whether that upgrades to a
  categorical ADJUNCTION (a (co)reflective subcategory) depends on which order
  Belnap carries and on the adjunction direction. Both are finite, so `decide`
  answers them.

  VERDICT (every clause `decide`/`rfl`-checked below):
    • TRUTH order:  inclusion ⊣ classicalSwitch  HOLDS  (i ⊣ r), a coreflection;
                    classicalSwitch ⊣ inclusion   FAILS (r ⊣ i).
    • INFORMATION order (the repo's Belnap `≤`): NEITHER direction holds;
                    classicalSwitch is not even monotone there.
    • retract  r∘i = id  holds unconditionally.

  So "constrain-then-expand returns X" is the unit isomorphism of  i ⊣ r  in the
  truth order, and the direction is  F ⊣ U  (F = inclusion, U = classicalSwitch),
  NOT  U ⊣ F.

  Author: Lando⊗⊙perator
-/

namespace ClassicalReflection

/-- Belnap FOUR (self-contained copy). -/
inductive Belnap : Type where
  | N | T | F | B
  deriving DecidableEq, Repr, Inhabited

/-- The classical fragment: the B-excluding subtype. -/
abbrev ClassicalBelnap := { v : Belnap // v ≠ .B }

/-- Inclusion of the classical fragment into the full bilattice. -/
def inclClassical : ClassicalBelnap → Belnap := Subtype.val

/-- The classical switch: collapse B to F (ex falso for B). -/
def classicalSwitch : Belnap → Belnap
  | .B => .F
  | v  => v

/-- Truth order (≤_t): F bottom, T top, N and B incomparable middles.
    F ≤ N ≤ T and F ≤ B ≤ T. -/
def truthLE : Belnap → Belnap → Bool
  | .F, _  => true
  | .N, .N => true | .N, .T => true | .N, _ => false
  | .T, .T => true | .T, _ => false
  | .B, .T => true | .B, .B => true | .B, _ => false

/-- Information order (⊑): N bottom, B top, T and F incomparable.
    N ⊑ T ⊑ B and N ⊑ F ⊑ B. Matches the repo's Belnap `≤`. -/
def infoLE : Belnap → Belnap → Bool
  | .N, _  => true
  | .T, .T => true | .T, .B => true | .T, _ => false
  | .F, .F => true | .F, .B => true | .F, _ => false
  | .B, .B => true | .B, _ => false

-- ── The retract (order-independent) — the adjunction unit ────────────────────

theorem switch_incl_retract (c : ClassicalBelnap) :
    classicalSwitch (inclClassical c) = inclClassical c := by
  obtain ⟨v, hv⟩ := c
  cases v with
  | B => exact absurd rfl hv
  | N => rfl
  | T => rfl
  | F => rfl

-- ── TRUTH ORDER: inclusion ⊣ classicalSwitch (i ⊣ r) HOLDS ──────────────────

/-- Galois connection `i ⊣ r` in the truth order: for classical `c` and any `x`,
    `i c ≤_t x ↔ c ≤_t r x`. With `i c = c` and `r x` classical this is the
    equality below, for every non-`B` `c`. -/
theorem truth_incl_left_adjoint (c x : Belnap) (hc : c ≠ .B) :
    truthLE c x = truthLE c (classicalSwitch x) := by
  cases c with
  | B => exact absurd rfl hc
  | N => cases x <;> rfl
  | T => cases x <;> rfl
  | F => cases x <;> rfl

/-- The opposite direction `r ⊣ i` FAILS in the truth order: at `x = B, c = F`,
    `r B = F ≤_t F` is true but `B ≤_t F` is false. -/
theorem truth_switch_left_adjoint_fails :
    truthLE (classicalSwitch .B) .F ≠ truthLE .B .F := by decide

-- ── INFORMATION ORDER: no adjunction either way; not monotone ────────────────

/-- `i ⊣ r` FAILS in the information order: `T ⊑ B` is true but `T ⊑ r B = F`
    is false. -/
theorem info_incl_left_adjoint_fails :
    infoLE .T .B ≠ infoLE .T (classicalSwitch .B) := by decide

/-- `r ⊣ i` FAILS in the information order: `r B = F ⊑ F` true but `B ⊑ F`
    false. -/
theorem info_switch_left_adjoint_fails :
    infoLE (classicalSwitch .B) .F ≠ infoLE .B .F := by decide

/-- classicalSwitch is monotone in the truth order (a precondition for the
    truth-order adjunction). -/
theorem switch_monotone_truth (a b : Belnap) :
    truthLE a b = true → truthLE (classicalSwitch a) (classicalSwitch b) = true := by
  cases a <;> cases b <;> intro h <;> simp_all [truthLE, classicalSwitch]

/-- classicalSwitch is NOT monotone in the information order: `T ⊑ B` holds but
    `r T = T ⊑ r B = F` does not. This is why no info-order adjunction exists. -/
theorem switch_not_monotone_info :
    infoLE .T .B = true ∧ infoLE (classicalSwitch .T) (classicalSwitch .B) = false := by
  decide

-- ── Summary ─────────────────────────────────────────────────────────────────

/-- The complete machine-checked verdict:
    (1) the classical fragment is a retract (unit `r∘i = id`);
    (2) truth order: inclusion is left adjoint to classicalSwitch (`i ⊣ r`, a
        coreflection); the reverse fails;
    (3) information order: neither adjunction holds.
    GPT's `F ⊣ U` (F = inclusion, U = classicalSwitch) is correct, in the truth
    order only. -/
theorem classical_coreflective_in_truth_order :
    (∀ c : ClassicalBelnap, classicalSwitch (inclClassical c) = inclClassical c) ∧
    (∀ c x : Belnap, c ≠ .B → truthLE c x = truthLE c (classicalSwitch x)) ∧
    (truthLE (classicalSwitch .B) .F ≠ truthLE .B .F) ∧
    (infoLE .T .B ≠ infoLE .T (classicalSwitch .B)) ∧
    (infoLE (classicalSwitch .B) .F ≠ infoLE .B .F) :=
  ⟨switch_incl_retract, truth_incl_left_adjoint,
   truth_switch_left_adjoint_fails, info_incl_left_adjoint_fails,
   info_switch_left_adjoint_fails⟩

end ClassicalReflection
