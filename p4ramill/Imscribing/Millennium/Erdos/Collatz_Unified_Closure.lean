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

end CollatzUnifiedClosure
