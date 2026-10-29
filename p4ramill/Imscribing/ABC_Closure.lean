import Imscribing.ABC_Witness

/-!
# Arithmetic transport, Closure, and uniform comparison errors

The round trip retains its source object. The quantitative comparison is a
separate obligation. Constants are chosen before the arithmetic triple.
These interfaces specify the arithmetic construction still to be supplied
for the schematic transformations in iutt.pdf §§12 and 18.
-/
namespace Imscribing.ABC

/-- Two presentations with a checked return to the original object. -/
structure RoundTrip (α β : Type*) where
  outward : α → β
  inward : β → α
  closes : Function.LeftInverse inward outward

theorem RoundTrip.outward_injective {α β : Type*} (r : RoundTrip α β) :
    Function.Injective r.outward := r.closes.injective

theorem RoundTrip.observable_returns {α β γ : Type*} (r : RoundTrip α β)
    (observe : α → γ) (x : α) :
    observe (r.inward (r.outward x)) = observe x := congrArg observe (r.closes x)

/-- Round-trip closure alone places no restriction on a scalar evaluator:
    every scalar function admits an identity round trip. -/
theorem every_observable_has_round_trip {α : Type*} (observe : α → ℝ) :
    ∃ r : RoundTrip α α, ∀ x, observe (r.inward (r.outward x)) = observe x :=
  ⟨⟨id, id, fun _ => rfl⟩, fun _ => rfl⟩

/-- Selectivity fixes the arithmetic observables throughout a change of
    presentation. The estimate remains a distinct, quantitative input. -/
theorem abc_of_round_trip_bound {β : Type*} (r : RoundTrip Triple β)
    (bound : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ t : Triple,
      logHeight (r.inward (r.outward t)) ≤
        (1 + ε) * logRadical (r.inward (r.outward t)) + C) : Conjecture := by
  apply conjecture_iff_log_estimate.mpr
  intro ε hε
  obtain ⟨C, hC⟩ := bound ε hε
  refine ⟨C, fun t => ?_⟩
  have ht := hC t
  rw [r.closes t] at ht
  exact ht

/-- An arithmetic comparison error is absorbable if its coefficient of
    log-radical can be made arbitrarily small, with a uniform remainder. -/
def SublinearComparisonError (error : Triple → ℝ) : Prop :=
  ∀ η : ℝ, 0 < η → ∃ C : ℝ, ∀ t : Triple,
    error t ≤ η * logRadical t + C

/-- Two independently uniform error budgets combine without introducing
    a constant that depends on the triple. -/
theorem SublinearComparisonError.add {e₁ e₂ : Triple → ℝ}
    (h₁ : SublinearComparisonError e₁) (h₂ : SublinearComparisonError e₂) :
    SublinearComparisonError (fun t => e₁ t + e₂ t) := by
  intro η hη
  obtain ⟨C₁, hC₁⟩ := h₁ (η / 2) (by positivity)
  obtain ⟨C₂, hC₂⟩ := h₂ (η / 2) (by positivity)
  refine ⟨C₁ + C₂, fun t => ?_⟩
  have := hC₁ t
  have := hC₂ t
  linarith

/-- A transported height estimate and an absorbable comparison error
    yield the arithmetic estimate. Each receives half the epsilon budget. -/
theorem filtered_estimate_of_comparison (transportedHeight error : Triple → ℝ)
    (comparison : ∀ t, logHeight t ≤ transportedHeight t + error t)
    (transported_bound : ∀ η : ℝ, 0 < η → ∃ C : ℝ, ∀ t : Triple,
      transportedHeight t ≤ (1 + η) * logRadical t + C)
    (error_bound : SublinearComparisonError error) : FilteredEstimate := by
  apply filtered_estimate_iff_log_estimate.mpr
  intro ε hε
  obtain ⟨C, hC⟩ := transported_bound (ε / 2) (by positivity)
  obtain ⟨D, hD⟩ := error_bound (ε / 2) (by positivity)
  refine ⟨C + D, fun t => ?_⟩
  have := comparison t
  have := hC t
  have := hD t
  linarith

/-- The resulting Witness retains both the arithmetic conclusion and the
    comparison-error evidence used to obtain it. -/
def comparisonClosure (transportedHeight error : Triple → ℝ)
    (comparison : ∀ t, logHeight t ≤ transportedHeight t + error t)
    (transported_bound : ∀ η : ℝ, 0 < η → ∃ C : ℝ, ∀ t : Triple,
      transportedHeight t ≤ (1 + η) * logRadical t + C)
    (error_bound : SublinearComparisonError error) :
    Imscribing.Paraconsistent.DialetheicWitness.Verdict Conjecture :=
  .held (abc_of_filtered_estimate (filtered_estimate_of_comparison
    transportedHeight error comparison transported_bound error_bound)) error_bound

theorem comparisonClosure_is_B (H e : Triple → ℝ)
    (comparison : ∀ t, logHeight t ≤ H t + e t)
    (bound : ∀ η : ℝ, 0 < η → ∃ C : ℝ, ∀ t : Triple,
      H t ≤ (1 + η) * logRadical t + C)
    (error_bound : SublinearComparisonError e) :
    (comparisonClosure H e comparison bound error_bound).classify = (true, true) := rfl

end Imscribing.ABC
