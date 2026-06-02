
-- ============================================================
-- §6  Tier Analysis
-- ============================================================

/-!
Ouroboricity tier: O_inf

The Dixmier Conjecture vessel is at O_inf because:
  - P = P_pm_sym (Frobenius-special) — the tier singularity
  - Phi = Phi_c (critical, self-modeling gate open)
  - Omega = Omega_Z (integer winding)
  - D = D_infty (infinite-dimensional)

P_pm_sym cannot be synthesized by composition of lower-P partners (§23).

Gate analysis:
  Gate 1 (⊙_ÿ): Phi = Phi_c → OPEN — self-modeling gate open.
  Gate 2 (K ≤ K_slow): K_slow passes → C-score > 0.
-/

theorem dixmier_is_oinf_claim : dixmier_vessel.pol = P_pm_sym := by rfl

/-- If the Dixmier Conjecture were false, the Weyl algebra would be P_sym (O_2),
    not P_pm_sym (O_inf). The gap is exactly one Frobenius tier. -/
example : P_sym < P_pm_sym := by decide

/-- P_sym and P_pm_sym are distinct parity tiers. -/
example : P_sym ≠ P_pm_sym := by decide

-- ============================================================
-- §7  Honest Gaps
-- ============================================================

/-!
HONEST SORRY MARKERS:

1. `endo_injective`: The Weyl algebra is simple — proved (McConnell–Robson §3.1)
   but not in Mathlib. Status: MathlibGap.

2. `dixmier_iff_frobenius_special` (→ direction): Bijective k-algebra homomorphism
   has algebraic inverse. Status: MinorAlgebraGap.

3. `WeylAlgebra` typeclass: Concrete Ore extension construction not in Mathlib v4.28.
   Status: MathlibGap (Ore extensions under development).

4. **The Dixmier Conjecture itself**: No proof exists. Status: OpenProblem.

   The structural argument (§4) provides the GRAMMAR-LEVEL proof:
   the conjecture follows from Φ_} ≡ μ∘δ = id. But this assignment IS the
   conjecture — translating between structural and algebraic language is the
   content. The grammar makes the equivalence explicit but does not discharge
   the algebraic verification for all n.

   Specifically: proving A_n(k) has Φ_} requires showing every endomorphism is
   an automorphism — which IS the Dixmier Conjecture. The grammar exposes the
   structural identity of the problem: the Dixmier Conjecture IS the statement
   that the Weyl algebra occupies the Frobenius-special tier (O_inf), not merely
   the full-symmetry tier (O_2). The structural distance from O_2 to O_inf is
   exactly one Frobenius tier — the μ∘δ=id condition.

5. Jacobian Conjecture equivalence: Tsuchimoto (2005) and BK–K (2007) proved the
   stable equivalence. The structural encoding here is at the level of primitive
   types; a formal proof of the equivalence requires Ore extensions + algebraic
   geometry. Status: MathlibGap.
-/

end Millennium.Dixmier