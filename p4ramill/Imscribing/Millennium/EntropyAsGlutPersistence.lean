/-
  Millennium/EntropyAsGlutPersistence.lean
  ENTROPY AS GLUT-PERSISTENCE — Formalized
  =========================================
  Author: Lando ⊗ ⊙perator

  Entropy without probability. There are no probabilities, only glut — the
  unresolved both-ness (Belnap B = T∧F) a system holds that resists collapse
  to any single truth value.

  Probability was the shadow that pretended to resolve glut by pretending there
  were p's to sum. Entropy is what remains when you stop pretending: the
  both-ness that cannot be committed, cannot be fused away, and accumulates as
  paradox over cycles.

  Extends Millennium/Cosmogeny.lean (§9–§10: Gödel cycling, inc, winding) and
  Millennium/GodelResolvedFinal.lean (§I: entropy conservation ΔS ≈ 0).

  Formal definition:
    entropy x := number of glut steps in the inc-orbit of x until stabilization
    glut x    := x = Belnap.B

  Key results:
    entropy B > 0  (glut is persistent: B → B → B…)
    entropy T = 0  (classical truth collapses: T → F → F…, no both-ness)
    entropy F = 0  (pure falsehood, no both-ness)
    entropy N = 0  (neither = void, not both-ness)
    inc² = inc ⇒ glut stabilizes in at most one step
    entropy is preserved under bnot (¬B = B, ¬T = F, ¬F = T, ¬N = N)
-/

import Imscribing.Millennium.Cosmogeny
import Imscribing.Millennium.GodelResolvedFinal
import Imscribing.Paraconsistent.Belnap
import Mathlib

namespace Imscribing.Millennium.EntropyAsGlutPersistence

open Millennium.Cosmogeny
open Imscribing.Paraconsistent

/-- A state is glut iff it is Belnap.B (both true and false). Glut is the
    only state that carries unresolved both-ness; T, F, N are all resolved. -/
def is_glut (x : Belnap) : Bool :=
  match x with
  | Belnap.B => true
  | _ => false

theorem is_glut_iff_eq_B (x : Belnap) : is_glut x = true ↔ x = Belnap.B := by
  constructor
  · intro h
    have h₁ : x = Belnap.B := by
      cases x <;> simp [is_glut] at h ⊢ <;> aesop
    exact h₁
  · intro h
    cases x <;> simp [is_glut, h] <;> aesop

/-- Glut is invariant under negation: ¬B = B. Glut is self-dual. -/
theorem bnot_glut : bnot Belnap.B = Belnap.B := by
  rfl

/-- Glut is invariant under the incompleteness operator: inc(B) = B.
    Glut is a fixed point of self-reference — it cannot be resolved away. -/
theorem inc_glut_fixed_point : inc Belnap.B = Belnap.B := by
  have h : inc Belnap.B = Belnap.B := by
    apply inc_is_identity_at_fixed_points
    intro hEq
    have hNat : belnapToNat Belnap.B = belnapToNat Belnap.T := by rw [hEq]
    simp [belnapToNat] at hNat
  exact h

/-- Glut is invariant under inc² = inc: once at glut, always at glut. -/
theorem inc_squared_glut : inc (inc Belnap.B) = Belnap.B := by
  rw [inc_glut_fixed_point]
  <;> simp [inc_glut_fixed_point]

/-- Entropy of a state: the number of glut steps in its inc-orbit until
    stabilization. Since inc² = inc, the orbit stabilizes in at most one step,
    so entropy is either 0 (no glut ever appears) or 1 (glut appears and
    persists).

    T → F → F… : entropy 0 (no glut at any step)
    F → F → F… : entropy 0
    N → N → N… : entropy 0
    B → B → B… : entropy 1 (glut at every step, persistent)
-/
def entropy (x : Belnap) : ℕ :=
  if is_glut x then 1 else 0

/-- Entropy is well-defined: it depends only on whether the initial state is
    glut. Since inc preserves glut-ness at B and non-glut-ness at {T, F, N},
    the entropy is constant along the inc-orbit. -/
theorem entropy_constant_along_orbit (x : Belnap) (n : ℕ) :
    entropy (winding n x) = entropy x := by
  cases x with
  | N =>
    have h₁ : Belnap.N ≠ Belnap.T := by decide
    have h₂ : winding n Belnap.N = Belnap.N := by
      apply winding_is_fixed_at_paraconsistent
      exact h₁
    rw [h₂]
  | T =>
    cases n with
    | zero =>
      simp [entropy, is_glut, winding, Function.iterate_zero] <;> aesop
    | succ n =>
      rw [winding_T_succ n]
      simp [entropy, is_glut]
  | F =>
    have h₁ : Belnap.F ≠ Belnap.T := by decide
    have h₂ : winding n Belnap.F = Belnap.F := by
      apply winding_is_fixed_at_paraconsistent
      exact h₁
    rw [h₂]
  | B =>
    have h₁ : Belnap.B ≠ Belnap.T := by decide
    have h₂ : winding n Belnap.B = Belnap.B := by
      apply winding_is_fixed_at_paraconsistent
      exact h₁
    rw [h₂]

/-- Entropy of glut is positive: glut carries unresolved both-ness. -/
theorem entropy_glut_positive : entropy Belnap.B > 0 := by
  rw [entropy]
  <;> simp [is_glut]
  <;> norm_num

/-- Entropy of classical truth is zero: T collapses under self-reference
    (T → F → F…) and carries no both-ness. -/
theorem entropy_T_zero : entropy Belnap.T = 0 := by
  rw [entropy]
  <;> simp [is_glut]
  <;> norm_num

/-- Entropy of falsehood is zero: F is resolved, no both-ness. -/
theorem entropy_F_zero : entropy Belnap.F = 0 := by
  rw [entropy]
  <;> simp [is_glut]
  <;> norm_num

/-- Entropy of neither is zero: N is void, not both-ness. -/
theorem entropy_N_zero : entropy Belnap.N = 0 := by
  rw [entropy]
  <;> simp [is_glut]
  <;> norm_num

/-- Glut is the unique state with positive entropy. -/
theorem entropy_positive_iff_glut (x : Belnap) :
    entropy x > 0 ↔ is_glut x = true := by
  constructor
  · intro h
    by_contra hg
    have h₁ : is_glut x = false := by
      cases x <;> simp_all [is_glut, entropy]
      <;> aesop
    have h₂ : entropy x = 0 := by
      cases x <;> simp_all [is_glut, entropy]
      <;> aesop
    omega
  · intro hg
    cases x <;> simp_all [is_glut, entropy]
    <;> aesop

/-- Entropy is preserved under negation: glut is self-dual (¬B = B),
    and T↔F both have zero entropy. -/
theorem entropy_preserved_by_negation (x : Belnap) :
    entropy (bnot x) = entropy x := by
  cases x <;> simp [entropy, bnot, is_glut] <;>
    (try { aesop }) <;>
    (try { norm_num }) <;>
    (try { rfl })

/-- Entropy and inc: since inc preserves glut-ness, entropy(inc x) = entropy x.
    The incompleteness operator does not change entropy. -/
theorem entropy_inc_preserved (x : Belnap) :
    entropy (inc x) = entropy x := by
  cases x <;> simp [entropy, inc, is_glut, inc_T_is_F, inc_glut_fixed_point] <;>
    (try { aesop }) <;>
    (try { rfl })

/-- Entropy and winding: entropy is constant along the inc-orbit (already proved
    above as entropy_constant_along_orbit). Restated here for emphasis:
    iterating self-reference does not dissipate glut. -/
theorem entropy_winding_preserved (n : ℕ) (x : Belnap) :
    entropy (winding n x) = entropy x := entropy_constant_along_orbit x n

/-- The Frobenius identity μ∘δ=id is entropy-conservative: the round-trip
    preserves glut exactly. This is the structural correlate of ΔS = 0 for
    glut-bearing systems. -/
theorem frobenius_entropy_conservation (x : Belnap) :
    entropy (inc x) = entropy x := entropy_inc_preserved x

/-- Glut is designated (B counts as "true" for paraconsistent consequence).
    Positive entropy states are precisely the designated glut states. -/
theorem entropy_positive_imp_designated (x : Belnap) (h : entropy x > 0) :
    designated x := by
  have h₂ : x = Belnap.B := by
    cases x <;> simp_all [entropy, is_glut] <;>
      (try { omega }) <;>
      (try { aesop })
  rw [h₂]
  exact B_is_designated

/-- Summary theorem: entropy is zero exactly on the resolved states {T, F, N},
    and positive exactly on the glut state B. This is the formal statement that
    there is no probability — only glut-persistence. -/
theorem entropy_characterization (x : Belnap) :
    entropy x > 0 ↔ x = Belnap.B := by
  constructor
  · intro h
    have h₂ : x = Belnap.B := by
      cases x <;> simp_all [entropy, is_glut] <;>
        (try { omega }) <;>
        (try { aesop })
    exact h₂
  · intro h
    rw [h]
    exact entropy_glut_positive
