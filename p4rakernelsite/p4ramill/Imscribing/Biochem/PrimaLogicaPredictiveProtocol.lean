import Mathlib

/-!
# Predictive-validation protocol (SCAFFOLD, NOT COMPILED)

Formalizes the standard under which constants such as the reference distances and the stiffness
rule are judged: held-out data, named baselines, and parameters frozen before testing.

What Lean checks here is the protocol's logical structure (no leakage, a minimum test size,
strict wins against every named baseline). Lean does not check that a predictor actually wins.
That is an empirical fact, supplied as a hypothesis, and the datasets and baselines are
inputs. Uses `∑ x ∈ s, f x` (current Mathlib); older versions need `∑ x in s, f x`.
-/

namespace Imscribing.PrimaLogica.Validation

/-- Mean squared error of predictor `f` against `target` on a finite test set. -/
noncomputable def risk {P : Type} (S : Finset P) (target f : P → ℝ) : ℝ :=
  (∑ p ∈ S, (f p - target p) ^ 2) / (S.card : ℝ)

theorem risk_nonneg {P : Type} (S : Finset P) (target f : P → ℝ) :
    0 ≤ risk S target f :=
  div_nonneg (Finset.sum_nonneg fun p _ => sq_nonneg _) (Nat.cast_nonneg _)

/-- `f` strictly beats `g` on `S`. -/
def Beats {P : Type} (S : Finset P) (target f g : P → ℝ) : Prop :=
  risk S target f < risk S target g

theorem Beats.trans {P : Type} {S : Finset P} {target f g h : P → ℝ}
    (h1 : Beats S target f g) (h2 : Beats S target g h) :
    Beats S target f h :=
  lt_trans h1 h2

theorem Beats.irrefl {P : Type} (S : Finset P) (target f : P → ℝ) :
    ¬ Beats S target f f :=
  lt_irrefl _

/-- A protocol over proteins `P` with parameter space `Θ`.
    `fit` sees targets only on `train` (`fit_local`), so the parameters are frozen
    before any test target is consulted. -/
structure Protocol (P Θ : Type) where
  train : Finset P
  test : Finset P
  disjoint : Disjoint train test
  minTest : ℕ
  minTest_pos : 0 < minTest
  minTest_le : minTest ≤ test.card
  fit : (P → ℝ) → Θ
  fit_local : ∀ t t' : P → ℝ, (∀ p ∈ train, t p = t' p) → fit t = fit t'
  model : Θ → P → ℝ

namespace Protocol

variable {P Θ : Type} (π : Protocol P Θ)

/-- The final predictor, trained from targets `t`. -/
def predictor (t : P → ℝ) : P → ℝ := π.model (π.fit t)

/-- No leakage: changing test targets cannot change the trained predictor. -/
theorem no_leak (t t' : P → ℝ) (h : ∀ p ∈ π.train, t p = t' p) :
    π.predictor t = π.predictor t' := by
  unfold predictor
  rw [π.fit_local t t' h]

/-- The test set is nonempty, so risk is a genuine mean. -/
theorem test_nonempty : π.test.Nonempty := by
  have : 0 < π.test.card := lt_of_lt_of_le π.minTest_pos π.minTest_le
  exact Finset.card_pos.mp this

/-- Empirical claim, stated as a proposition. It is NOT provable from the protocol.
    It says the trained predictor strictly beats every named baseline on the test set. -/
def WinsAll (t : P → ℝ) (baselines : List (P → ℝ)) : Prop :=
  ∀ b ∈ baselines, Beats π.test t (π.predictor t) b

/-- If it wins against all baselines, it wins against any one of them. -/
theorem WinsAll.beats {t : P → ℝ} {baselines : List (P → ℝ)}
    (h : π.WinsAll t baselines) {b : P → ℝ} (hb : b ∈ baselines) :
    Beats π.test t (π.predictor t) b :=
  h b hb

/-- Winning on the held-out set is meaningful only if the test targets were
    unused in fitting. Replacing test targets leaves the predictor unchanged. -/
theorem winsAll_stable_under_test_change
    (t t' : P → ℝ) (hagree : ∀ p ∈ π.train, t p = t' p) :
    π.predictor t = π.predictor t' :=
  π.no_leak t t' hagree

end Protocol

end Imscribing.PrimaLogica.Validation
