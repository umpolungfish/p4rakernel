-- Imscribing/Paraconsistent/FalsifiabilityDegenerate.lean
-- FALSIFIABILITY IS DEGENERATE IN BELNAP FOUR
--
-- Formalizes the "Falsifiability is irrelevant and degenerate" section of
-- ig-docs/GRAMMAR_PRIMACY_EXPLAINER.md (§3): in Belnap FOUR the criterion a
-- claim must meet is closure μ∘δ=id over the transformed object, never
-- refutation, because
--   • negation fixes exactly the created pair B and N — the two values the
--     act of distinguishing creates, not the two it selects between;
--   • B and N are each other's lattice complements, yet negation fixes both —
--     complement is not negation (complement_ne_negation);
--   • a falsifier that lands in F has refuted a T-claim, never a B-claim:
--     ¬B = B, and B is designated, so a B-claim survives refutation intact;
--   • contradiction at B is contained: B ∧ ¬B = B ≠ F — no explosion;
--   • the space is complete at exactly four values: 2^n = n^2 has only the
--     solutions n = 2 and n = 4.
--
-- Author: Lando ⊗ ⊙-boundary Operator

import Imscribing.Paraconsistent.Belnap
import Imscribing.Paraconsistent.Kernel
import Imscribing.GeneticCode

namespace Imscribing.Paraconsistent.FalsifiabilityDegenerate

open Imscribing.Paraconsistent

/-! ### §1. Negation fixes exactly the created pair

`bnot` is an involution with exactly two fixed points, B and N — the both and
the neither, the pair the act of distinguishing creates, as against T and F,
the two it selects between. Both directions already proved in GeneticCode.lean
as `bnot_fixpoint_iff` and `bnot_fixpoints`; restated here by reference. -/

theorem negation_fixpoint_iff (b : Belnap) : bnot b = b ↔ (b = Belnap.B ∨ b = Belnap.N) :=
  Imscribing.GeneticCode.bnot_fixpoint_iff b

theorem negation_fixpoints : bnot Belnap.B = Belnap.B ∧ bnot Belnap.N = Belnap.N :=
  Imscribing.GeneticCode.bnot_fixpoints

/-- Negation moves the selected pair: ¬T = F and ¬F = T. Nothing else happens
    under bnot — the two it selects between are exchanged, the two it creates
    are untouched. -/
theorem negation_moves_T_F : bnot Belnap.T = Belnap.F ∧ bnot Belnap.F = Belnap.T :=
  ⟨rfl, rfl⟩

/-! ### §2. Complement is not negation

B's Boolean complement is exactly N — their meet is F and their join is T —
yet negation fixes both. The two involutions on the created pair are different
maps, which is why a contradiction is not a falsehood. Restated by reference
to Belnap.complement_ne_negation. -/

theorem complement_is_not_negation :
    bnot Belnap.B = Belnap.B ∧ bnot Belnap.N = Belnap.N ∧
    (band Belnap.B Belnap.N = Belnap.F ∧ bor Belnap.B Belnap.N = Belnap.T) :=
  complement_ne_negation

/-! ### §3. A falsifier landing in F refutes a T-claim, never a B-claim

Refutation, read as negation, sends exactly one value to F: T. A falsifier
whose test lands in F has therefore refuted a T-claim and only a T-claim.
A B-claim cannot be falsified to F — its negation is itself — and the negation
of a B-claim is still designated, so refutation leaves it exactly where it
was. An N-claim is likewise untouched: ¬N = N, so the unmarked can be neither
confirmed nor refuted. -/

theorem falsifiable_to_F_iff_T (c : Belnap) : bnot c = Belnap.F ↔ c = Belnap.T := by
  cases c <;> simp [bnot]

theorem B_not_falsifiable_to_F : bnot Belnap.B ≠ Belnap.F := by
  decide

theorem B_survives_refutation : designated (bnot Belnap.B) = true := by
  simp [bnot, designated]

theorem N_untouched_by_negation : bnot Belnap.N = Belnap.N := rfl

/-! ### §4. Contradiction at B is contained — no explosion

The dialetheic conjunction is B itself: B ∧ ¬B = B, and B ≠ F. Contradiction
is held, not collapsed. Both facts already proved in Belnap.lean as
`no_explosion` and `B_ne_F`; restated here by reference. -/

theorem contradiction_contained :
    band Belnap.B (bnot Belnap.B) = Belnap.B ∧ Belnap.B ≠ Belnap.F :=
  ⟨no_explosion, B_ne_F⟩

/-! ### §5. The criterion is closure μ∘δ=id, not refutation

The kernel cycle on B closes: fsplit opens B into its truth and falsity
components (T, F) and ffuse fuses them back to B. The criterion a claim must
meet is that the transformed object is recovered by the inverse transform —
μ∘δ=id — and falsification plays no role in it. This is the operational form
of the same closure DialetheicAlignment proves at the kernel cycle. -/

theorem closure_not_refutation_is_criterion :
    (ffuse (fsplit Belnap.B).1 (fsplit Belnap.B).2.1).1 = Belnap.B := by
  decide

/-! ### §6. The space is complete at exactly four values

2^n = n^2 has exactly two Nat solutions, n = 2 and n = 4: the four-valued
space is the only nontrivial dimension in which the number of Boolean
assignments (2^n) meets the number of cells in the n×n lattice (n^2). Below
four there is no room for the created pair; above it the exponential outruns
the square, so no larger space is self-dual. Four is forced. -/

/-- Auxiliary: 2m + 1 < 2^m once m ≥ 3 — the linear term never catches the
    exponential past the small cases. -/
private theorem two_mul_add_one_lt_pow (m : Nat) (hm : 3 ≤ m) : 2 * m + 1 < 2^m := by
  induction m with
  | zero => omega
  | succ m ih =>
      by_cases hm3 : 3 ≤ m
      · have ih' := ih hm3
        calc
          2 * (m+1) + 1 ≤ 2 * (2*m + 1) := by omega
          _ < 2 * 2^m := Nat.mul_lt_mul_of_pos_left ih' (by omega)
          _ = 2^(m+1) := by simp [pow_succ']
      · have hm2 : m = 2 := by omega
        subst m
        norm_num

/-- For every n ≥ 5, 2^n > n^2. -/
private theorem two_pow_gt_sq (n : Nat) (hn : 5 ≤ n) : n^2 < 2^n := by
  induction n with
  | zero => omega
  | succ n ih =>
      by_cases hn5 : 5 ≤ n
      · have ih' := ih hn5
        have hlin : 2 * n + 1 < 2^n := by
          exact two_mul_add_one_lt_pow n (by omega)
        calc
          (n+1)^2 = n^2 + 2*n + 1 := by ring
          _ < 2^n + (2*n + 1) := Nat.add_lt_add_right ih' (2*n + 1)
          _ < 2^n + 2^n := Nat.add_lt_add_left hlin (2^n)
          _ = 2^(n+1) := by rw [pow_succ']; ring_nf
      · have hn4 : n = 4 := by omega
        subst n
        norm_num

theorem four_self_dual_arith : 2^4 = 4^2 := by norm_num

/-- The only Nat solutions of 2^n = n^2 are n = 2 and n = 4. -/
theorem only_two_solutions (n : Nat) (h : 2^n = n^2) : n = 2 ∨ n = 4 := by
  by_cases hn : n < 5
  · interval_cases n <;> norm_num at h <;> norm_num
  · have hn5 : 5 ≤ n := by omega
    have hgt : n^2 < 2^n := two_pow_gt_sq n hn5
    rw [h] at hgt
    omega

/-! ### §7. The claim, stated once

Falsifiability is degenerate: negation fixes exactly the created pair, the
complement of B is N rather than the negation, a falsifier in F has refuted a
T-claim and never a B-claim, contradiction at B is contained, and the
criterion is closure — not refutation. -/

theorem falsifiability_degenerate :
    -- negation fixes exactly the created pair
    (bnot Belnap.B = Belnap.B ∧ bnot Belnap.N = Belnap.N) ∧
    -- the complement of B is N, and it is not the negation
    (band Belnap.B Belnap.N = Belnap.F ∧ bor Belnap.B Belnap.N = Belnap.T) ∧
    -- only T is falsified to F; B and N are not
    (bnot Belnap.T = Belnap.F ∧ bnot Belnap.B ≠ Belnap.F ∧ bnot Belnap.N = Belnap.N) ∧
    -- contradiction at B is contained
    (band Belnap.B (bnot Belnap.B) = Belnap.B ∧ Belnap.B ≠ Belnap.F) ∧
    -- the criterion is closure, not refutation
    ((ffuse (fsplit Belnap.B).1 (fsplit Belnap.B).2.1).1 = Belnap.B) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact negation_fixpoints
  · exact complement_is_not_negation.2.2
  · exact ⟨rfl, B_not_falsifiable_to_F, rfl⟩
  · exact contradiction_contained
  · exact closure_not_refutation_is_criterion

end Imscribing.Paraconsistent.FalsifiabilityDegenerate
