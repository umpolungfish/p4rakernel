import Imscribing.ABC_Exhaustion

/-! # Finite enclosures, tails, and a countable epsilon basis -/
namespace Imscribing.ABC

/-- An enclosure contains the exact maximum, not merely a rounded sample. -/
structure WindowEnclosure (ε : ℝ) (N : ℕ) where
  lower : ℝ
  upper : ℝ
  lower_le : lower ≤ windowMaximum ε N
  le_upper : windowMaximum ε N ≤ upper

theorem WindowEnclosure.bounds_sample {ε : ℝ} {N : ℕ}
    (e : WindowEnclosure ε N) (t : Triple) (ht : t.c ≤ N + 2) :
    discrepancy ε t ≤ e.upper :=
  (discrepancy_le_windowMaximum ε N t ((mem_arithmeticWindow N t).mpr ht)).trans
    e.le_upper

/-- The finite part and the unobserved tail have separate evidence.
    Tail control is a proof field, not inferred from the finite enclosure. -/
structure TailCertificate (ε : ℝ) where
  cutoff : ℕ
  enclosure : WindowEnclosure ε cutoff
  tailUpper : ℝ
  tail_bound : ∀ t : Triple, cutoff + 2 < t.c → discrepancy ε t ≤ tailUpper

theorem TailCertificate.uniform_bound {ε : ℝ} (cert : TailCertificate ε) :
    ∀ t : Triple, discrepancy ε t ≤ max cert.enclosure.upper cert.tailUpper := by
  intro t
  by_cases ht : t.c ≤ cert.cutoff + 2
  · exact (cert.enclosure.bounds_sample t ht).trans (le_max_left _ _)
  · exact (cert.tail_bound t (by omega)).trans (le_max_right _ _)

theorem discrepancy_antitone (t : Triple) : Antitone (fun ε => discrepancy ε t) := by
  intro ε δ h
  have := mul_nonneg (sub_nonneg.mpr h) (logRadical_pos t).le
  unfold discrepancy
  nlinarith

theorem windowMaximum_antitone (N : ℕ) : Antitone (fun ε => windowMaximum ε N) := by
  intro ε δ h
  apply windowMaximum_le
  intro t ht
  exact (discrepancy_antitone t h).trans (discrepancy_le_windowMaximum ε N t ht)

/-- Positive reciprocal exponents form a cofinal test family near zero. -/
def ReciprocalDiscrepancyBounds : Prop :=
  ∀ n : ℕ, ∃ C : ℝ, ∀ t : Triple, discrepancy (1 / ((n : ℝ) + 1)) t ≤ C

theorem abc_iff_reciprocal_bounds : Conjecture ↔ ReciprocalDiscrepancyBounds := by
  constructor
  · intro h n
    exact conjecture_iff_uniform_discrepancy.mp h _ (by positivity)
  · intro h
    apply conjecture_iff_uniform_discrepancy.mpr
    intro ε hε
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt hε
    obtain ⟨C, hC⟩ := h n
    exact ⟨C, fun t => (discrepancy_antitone t hn.le).trans (hC t)⟩

theorem abc_of_reciprocal_tail_certificates
    (cert : ∀ n : ℕ, TailCertificate (1 / ((n : ℝ) + 1))) : Conjecture := by
  apply abc_iff_reciprocal_bounds.mpr
  intro n
  exact ⟨_, (cert n).uniform_bound⟩

def certifiedSpectralClosure
    (cert : ∀ n : ℕ, TailCertificate (1 / ((n : ℝ) + 1))) :
    Imscribing.Paraconsistent.DialetheicWitness.Verdict Conjecture :=
  .held (abc_of_reciprocal_tail_certificates cert)
    (uniform_spectral_iff_abc.mpr (abc_of_reciprocal_tail_certificates cert))

theorem certifiedSpectralClosure_is_B
    (cert : ∀ n : ℕ, TailCertificate (1 / ((n : ℝ) + 1))) :
    (certifiedSpectralClosure cert).classify = (true, true) := rfl

end Imscribing.ABC
