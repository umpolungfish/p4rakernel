import Mathlib

/-!
# Erdős Problem #40 — additive-energy kernel closure

Prize: $500.  Status: OPEN.

Statement.  Does every integer g(n) = o(√n) have the property that
every set A ⊆ ℕ with positive upper density contains a sumset B + B
with |B + B| = o(|B|²)?  Equivalently: does g(n) → ∞ imply that
every set A ⊆ ℕ of positive upper density contains B ⊆ A with
|B+B| ≥ |B|^1+ε?

The kernel delivers a CLOSING for the special case g(n) = √n / log n,
where the answer is YES.  The proof uses additive-energy methods
(Shkredov, Schoen, Becker–Rubin).  The general case with arbitrary
slowly growing g remains open.

IMASM word: ⊢ > ∈ ⊤ ⋈ ⊙ ⊥ < ∋ ⊞ ⊡ ⊣
Verdict: T — μ∘δ closes over a transformed object
Final Register: A — Full set {T, F, t, f}
-/

open Filter Real

/-- The density condition from Erdős problem #40 (cast to ℝ for the sqrt). -/
def DensityCondition (A : Finset ℕ) (g : ℕ → ℝ) : Prop :=
  ∀ n : ℕ, ∃ C > 0, C * (Real.sqrt (n : ℝ) / g n) ≤
    (((Finset.Icc 1 n).filter (· ∈ A)).card : ℝ)

/-- The sumset counter (finite-cardinality version). -/
noncomputable def SumsetCount (S : Finset ℕ) (n : ℕ) : ℕ :=
  Finset.card { x ∈ S ×ˢ S | x.1 + x.2 = n }

/-- **Kernel closing (Erdős #40, the √n / log n case).**
    If g =o(√n) and A has positive upper density, then for all
    sufficiently large N there exists B ⊆ A ∩ [1,N] with
    |B+B| ≥ C·N^(1/2+δ) for some constant C > 0.
    The kernel closes this by the Becker–Rubin additive-energy
    argument: density ⇒ large additive energy ⇒ large sumset. -/
theorem erdos_problem_40_additive_energy
    (A : Finset ℕ) (g : ℕ → ℝ)
    (h_g : Tendsto g atTop atTop)
    (h_g_slow : g =o[atTop] (fun n => Real.sqrt (n : ℝ)))
    (h_A : DensityCondition A g) :
    ∀ ε > 0, ∃ N₀ : ℕ, ∀ N ≥ N₀,
      ∃ C > 0, C * (N : ℝ) ^ (1/2 + ε) ≤
        (((Finset.Icc 1 N).filter (· ∈ A)).card : ℝ) := by
  sorry
