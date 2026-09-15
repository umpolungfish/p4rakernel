import Imscribing.ABC
import Imscribing.Paraconsistent.DialetheicWitness

/-!
# abc Witness and Closure

The existing `Verdict.held` retains two established facts with a compiled B
tag. Each Witness below names those facts. The arithmetic Closure consumes
the uniform filtered estimate and retains the filtration's non-factorization.
-/
namespace Imscribing.ABC

open Imscribing.Paraconsistent.DialetheicWitness

/-- On the same triple 1+8=9: radical 6 and height exceeding that radical. -/
def primeSupportWitness : Verdict (rad one_eight_nine = 6) :=
  .held example_radical naive_radical_bound_fails

theorem primeSupportWitness_is_B : primeSupportWitness.classify = (true, true) := rfl

/-- Exact height recovery by the weighted evaluator, held alongside its
    inability to factor through the position-blind scalar evaluator. -/
def filteredRepresentationWitness :
    Verdict (∀ t : Triple, IUTT.weighted (arithmeticPacket t) = logHeight t) :=
  .held packet_height_calibration IUTT.weighted_does_not_factor

theorem filteredRepresentationWitness_is_B :
    filteredRepresentationWitness.classify = (true, true) := rfl

/-- Arithmetic Closure: the supplied uniform estimate yields abc, while the
    tensor-position distinction remains held in the same Witness. -/
def arithmeticClosure (estimate : FilteredEstimate) : Verdict Conjecture :=
  .held (abc_of_filtered_estimate estimate) IUTT.tensor_weighted_no_factor

theorem arithmeticClosure_is_B (estimate : FilteredEstimate) :
    (arithmeticClosure estimate).classify = (true, true) := rfl

/-- A runtime observation of the concrete arithmetic Witness constructor. -/
def primeSupportClass : Bool × Bool := primeSupportWitness.classify
theorem primeSupportClass_is_B : primeSupportClass = (true, true) := rfl

#print axioms primeSupportWitness
#print axioms filteredRepresentationWitness
#print axioms arithmeticClosure
#print axioms primeSupportClass_is_B

/-! ## Filtered estimate and log estimate held in one Witness -/

/-- Both fields come from the supplied filtered estimate and its checked
    arithmetic reformulation. The constructor tag is compiled data. -/
def abcVerdict (h_filtered : FilteredEstimate) : Verdict LogEstimate :=
  .held (filtered_estimate_iff_log_estimate.mp h_filtered) h_filtered

theorem abcVerdict_is_B (h_filtered : FilteredEstimate) :
    (abcVerdict h_filtered).classify = (true, true) := rfl

/-- Extract the arithmetic conclusion from a verdict with positive support. -/
theorem abc_of_verdict (v : Verdict LogEstimate) (positive : v.classify.1 = true) :
    Conjecture := by
  cases v with
  | proved h => exact conjecture_iff_log_estimate.mpr h
  | held h _ => exact conjecture_iff_log_estimate.mpr h
  | refuted _ => simp [Verdict.classify] at positive
  | admitted => simp [Verdict.classify] at positive

theorem abc_from_filtered_via_verdict (h_filtered : FilteredEstimate) : Conjecture :=
  abc_of_verdict (abcVerdict h_filtered) rfl

/-- PLift makes proof content a Type suitable for Option. Missing positive
    support returns none; it is not replaced by an arithmetic conclusion. -/
def abc_of_verdict_refined (v : Verdict LogEstimate) : Option (PLift Conjecture) :=
  match v with
  | .proved h => some ⟨conjecture_iff_log_estimate.mpr h⟩
  | .held h _ => some ⟨conjecture_iff_log_estimate.mpr h⟩
  | .refuted _ => none
  | .admitted => none

theorem verdict_extraction_tracks_positive (v : Verdict LogEstimate) :
    (abc_of_verdict_refined v).isSome = v.classify.1 := by cases v <;> rfl

theorem abc_of_held_verdict {Q : Prop} (h_log : LogEstimate) (h_Q : Q) : Conjecture :=
  abc_of_verdict (.held h_log h_Q) rfl

/-- A Witness is Type-valued, so this is a definition rather than a theorem. -/
def iutt_abc_dialetheia (h_filtered : FilteredEstimate) : Verdict LogEstimate :=
  abcVerdict h_filtered

theorem quality_bounded_of_held_verdict (v : Verdict LogEstimate)
    (positive : v.classify.1 = true) :
    ∃ Q : ℝ, ∀ t : Triple, quality t ≤ Q := by
  cases v with
  | proved h => exact quality_bounded_of_log_estimate h
  | held h _ => exact quality_bounded_of_log_estimate h
  | refuted _ => simp [Verdict.classify] at positive
  | admitted => simp [Verdict.classify] at positive

/-- Total case split retains N as well as F for verdicts without positive support. -/
theorem quality_bound_or_nonpositive (v : Verdict LogEstimate) :
    (∃ Q : ℝ, ∀ t : Triple, quality t ≤ Q) ∨
      v.classify = (false, true) ∨ v.classify = (false, false) := by
  cases v with
  | proved h => exact Or.inl (quality_bounded_of_log_estimate h)
  | held h _ => exact Or.inl (quality_bounded_of_log_estimate h)
  | refuted _ => exact Or.inr (Or.inl rfl)
  | admitted => exact Or.inr (Or.inr rfl)

theorem abc_from_held_witness :
    (∃ Q : Prop, ∃ _ : LogEstimate, ∃ _ : Q, True) → Conjecture := by
  rintro ⟨Q, h_log, h_Q, _⟩
  exact abc_of_held_verdict h_log h_Q

end Imscribing.ABC
