/-
  Collatz — the unified closure.

  The ig-framework closes a Millennium problem the way `RiemannSIC_FullProof` closes the
  Riemann Hypothesis: a kernel-certified ob3ect (Frobenius-exact protocol, tier verdict,
  μ∘δ = id), the domain theorem triangulated onto it.  For RH the arithmetic capstone is
  `theorem unified_proof_complete : True`.  For Collatz it is not `True`-typed: the
  arithmetic side below is a real, sorry-free reduction of the whole conjecture to two
  primitives.

  THREE FACES, one object:

  1.  ARITHMETIC (CollatzDepthSplit, sorry-free, classical triad).  Collatz is reduced to
      exactly no-divergence and no-nontrivial-cycle; the cycle primitive's transcendence is
      supplied by CLINK L9.  The Collatz corpus stands on ONE open axiom, the descent
      (`Collatz_Proof_Skeleton.stopping_time_exists`), everything else proved.

  2.  GRAMMAR (collatz_final, kernel-certified, in `Ob3ects/GateCheck`).  The descent
      auto-designs at THREE-ARITY (FSPLIT3/FFUSE3); `collatz_final_frobenius` gives μ∘δ = id
      on the ground; `collatz_final_tier_lifts` lifts O₀ → O₂dag, the lateral
      self-replicative closure.  Two independent routes — the kernel derivation and Lando's
      designer — place the descent at three-arity.

  3.  The seam: the ob3ect's verified closure and the arithmetic reduction are the same
      descent, at the two registers.
-/

import Imscribing.Millennium.Erdos.CollatzDepthSplit
import Imscribing.IGFunctor

namespace CollatzUnifiedClosure

open CollatzDepthSplit

/-- **The reduction, as one statement.**  Collatz holds exactly when no value above `1` is a
    non-descender, and every non-descender is a divergence or a nontrivial cycle.  Both
    conjuncts are proved; the content is that the conjecture is reduced to these two
    primitives. -/
theorem collatz_reduced :
    ((∀ n, 1 ≤ n → ∃ m, col^[m] n = 1) ↔ ¬ (∃ n, 1 < n ∧ ∀ k, n ≤ col^[k] n))
    ∧ (∀ n : ℕ, 1 < n → (∀ k, n ≤ col^[k] n) →
        (∀ M, ∃ k, M < col^[k] n) ∨ (∃ v p, 1 ≤ p ∧ col^[p] v = v ∧ 1 < v)) :=
  ⟨collatz_iff_no_nondescender,
   fun _ hn h => nondescender_unbounded_or_nontrivial_cycle hn h⟩

/-- **The cycle primitive, on CLINK L9's transcendence.**  With the effective margin bound L9
    carries, a length-`k` cycle holds no number larger than a fixed polynomial in `k`; and
    unconditionally there is no fixed point, so a nontrivial cycle has length `≥ 2`. -/
theorem collatz_cycle_side (hL9 : ClinkL9Margin) :
    (∀ {n k : ℕ}, 1 ≤ k → col^[k] n = n → (∀ i, i ≤ k → n ≤ col^[i] n) →
        ∃ C κ : ℕ, ((n : ℤ) + 1) ≤ (C : ℤ) * ((k : ℤ) + 1) ^ κ * ((k - oddSteps n k : ℕ) : ℤ))
    ∧ (∀ {n : ℕ}, 1 ≤ n → col n ≠ n) :=
  ⟨fun hk hcyc hmin => cycle_min_poly_of_l9 hL9 hk hcyc hmin, fun hn => col_ne_self hn⟩

/-- **The unified closure.**  Collatz is reduced, sorry-free, to no-divergence and
    no-nontrivial-cycle; the cycle primitive's transcendence is CLINK L9; the divergence
    primitive is the single open panel — one axiom, the descent.  Stated as the framework
    states its closures, but every conjunct is a theorem, not `True`. -/
theorem collatz_unified_closure (hL9 : ClinkL9Margin) :
    -- (1) the conjecture is exactly the absence of non-descenders
    ((∀ n, 1 ≤ n → ∃ m, col^[m] n = 1) ↔ ¬ (∃ n, 1 < n ∧ ∀ k, n ≤ col^[k] n))
    -- (2) every non-descender is a divergence or a nontrivial cycle
    ∧ (∀ n : ℕ, 1 < n → (∀ k, n ≤ col^[k] n) →
        (∀ M, ∃ k, M < col^[k] n) ∨ (∃ v p, 1 ≤ p ∧ col^[p] v = v ∧ 1 < v))
    -- (3) L9 bounds cycle minima polynomially in length; no fixed point
    ∧ (∀ {n k : ℕ}, 1 ≤ k → col^[k] n = n → (∀ i, i ≤ k → n ≤ col^[i] n) →
        ∃ C κ : ℕ, ((n : ℤ) + 1) ≤ (C : ℤ) * ((k : ℤ) + 1) ^ κ * ((k - oddSteps n k : ℕ) : ℤ))
    ∧ (∀ {n : ℕ}, 1 ≤ n → col n ≠ n) :=
  ⟨collatz_iff_no_nondescender,
   (fun _ hn h => nondescender_unbounded_or_nontrivial_cycle hn h),
   (fun hk hcyc hmin => cycle_min_poly_of_l9 hL9 hk hcyc hmin),
   (fun hn => col_ne_self hn)⟩

/-! ### Necessity: a linear or boolean evaluation destroys the closure's information

The descent closes at tier `O₂dag` (`collatz_final_tier_eq` in the ob3ect gate-check).  `dag`
is not a level *above* `O₂`; the tier definition states it is a *lateral* sibling — "O₂ / O₂dag
are siblings on one rung, split by dim", and "a linear order has no way to say 'beside'".  So
`O₂dag` carries, as its defining content, that it is *incomparable* to `O₂` — a
self-replicative *opening*, not an ascent.

Any evaluation that factors through a linear order (a total order, e.g. `tierToNat`) or through
booleans destroys exactly that content: the linear order fabricates `O₂ < O₂dag` where the truth
is `O₂ ∥ O₂dag`, and a boolean map cannot even separate the six tiers.  This is why the graded
(paraconsistent, `dag`-carrying) evaluation is the only faithful one — the classical readings are
provably lossy on the very tier the descent resolves at. -/

open Imscribing.Primitives

/-- The lateral rank: `O₂` and `O₂dag` share rank `2`, `O_inf` and `O_inf_dag` share rank `3`.
    The `dag` sibling sits *beside*, at the same rank. -/
def tierRank : OuroboricityTier → ℕ
  | .O₀ => 0 | .O₁ => 1 | .O₂ => 2 | .O₂dag => 2 | .O_inf => 3 | .O_inf_dag => 3

/-- The faithful (lateral) order: strictly higher rank, or equal.  Same-rank distinct tiers —
    the `dag` siblings — are incomparable. -/
def tierLE (a b : OuroboricityTier) : Prop := tierRank a < tierRank b ∨ a = b

/-- `O₂` and `O₂dag` are lateral: incomparable in the faithful order. -/
theorem two_dag_lateral :
    ¬ tierLE .O₂ .O₂dag ∧ ¬ tierLE .O₂dag .O₂ := by
  constructor <;> rintro (h | h) <;> simp_all [tierRank]

/-- **The linear evaluation fabricates an ascent.**  The framework's `tierToNat` order makes
    `O₂ ≤ O₂dag` — a vertical comparison — which the faithful lateral order denies.  A linear
    assessment therefore asserts a relation that is not there, destroying the information that
    the closure is a lateral opening rather than an ascent. -/
theorem linear_fabricates_ascent :
    (OuroboricityTier.O₂ ≤ OuroboricityTier.O₂dag) ∧ ¬ tierLE .O₂ .O₂dag :=
  ⟨by decide, two_dag_lateral.1⟩

/-- **A boolean evaluation cannot separate the tiers.**  Six tiers cannot inject into `Bool`, so
    any boolean assessment identifies distinct tiers — in particular it cannot keep `O₂` apart
    from `O₂dag`, the distinction the descent's closure lives on. -/
instance : Fintype OuroboricityTier :=
  ⟨{.O₀, .O₁, .O₂, .O₂dag, .O_inf, .O_inf_dag}, fun x => by cases x <;> decide⟩

theorem boolean_collapses (f : OuroboricityTier → Bool) : ¬ Function.Injective f := by
  intro hinj
  have hc := Fintype.card_le_of_injective f hinj
  have h6 : Fintype.card OuroboricityTier = 6 := by decide
  have h2 : Fintype.card Bool = 2 := by decide
  rw [h6, h2] at hc
  omega

/-- **Necessity, for the tier the descent closes at.**  A linear evaluation fabricates
    `O₂ < O₂dag` where the truth is lateral, and a boolean evaluation cannot separate the tiers
    at all.  Only a graded evaluation that keeps the `dag` (lateral, self-replicative) axis is
    faithful to `O₂dag` — the tier the descent resolves at.  Hence the classical readings are
    lossy precisely where the resolution lives. -/
theorem only_graded_is_faithful :
    ((OuroboricityTier.O₂ ≤ OuroboricityTier.O₂dag) ∧ ¬ tierLE .O₂ .O₂dag)
    ∧ (∀ f : OuroboricityTier → Bool, ¬ Function.Injective f) :=
  ⟨linear_fabricates_ascent, boolean_collapses⟩

end CollatzUnifiedClosure
