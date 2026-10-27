import Imscribing.Millennium.HornTorusGeometry

namespace Imscribing.TorusFrameReadout

open HornTorus

/-- I retain the tube angle first, matching the existing horn construction. -/
noncomputable def surface (R r u v : ℝ) : Point :=
  ((R + r * Real.cos u) * Real.cos v,
   (R + r * Real.cos u) * Real.sin v, r * Real.sin u)

noncomputable def normal (u v : ℝ) : Point :=
  (Real.cos u * Real.cos v, Real.cos u * Real.sin v, Real.sin u)

noncomputable def centerline (R v : ℝ) : Point :=
  (R * Real.cos v, R * Real.sin v, 0)

theorem source_horn (R u v : ℝ) : surface R R u v = horn R u v := by
  apply Prod.ext
  · simp only [surface, horn]; ring
  · apply Prod.ext <;> simp only [surface, horn] <;> ring

/-- I recover the centreline by subtracting the carried normal displacement. -/
theorem normal_centerline (R r u v : ℝ) :
    ((surface R r u v).1 - r * (normal u v).1,
     (surface R r u v).2.1 - r * (normal u v).2.1,
     (surface R r u v).2.2 - r * (normal u v).2.2) = centerline R v := by
  apply Prod.ext
  · simp only [surface, normal, centerline]; ring
  · apply Prod.ext <;> simp only [surface, normal, centerline] <;> ring

def pairedMagnitude (t c : ℝ) : ℝ := max (t * (1 + c)) |t + c|
def completedMagnitude (t c : ℝ) : ℝ := max (pairedMagnitude t c) |c|

lemma inner_le_completed (t c : ℝ) : t * (1 + c) ≤ completedMagnitude t c :=
  le_trans (le_max_left _ _) (le_max_left _ _)

lemma outer_le_completed (t c : ℝ) : |t + c| ≤ completedMagnitude t c :=
  le_trans (le_max_right _ _) (le_max_left _ _)

lemma normal_le_completed (t c : ℝ) : |c| ≤ completedMagnitude t c :=
  le_max_right _ _

/-- The retained normal and deformed frame give a positive uniform channel bound. -/
theorem completed_half_lower (t c : ℝ) : t / 2 ≤ completedMagnitude t c := by
  by_cases h : t / 2 ≤ |c|
  · exact le_trans h (normal_le_completed t c)
  · have hc := neg_abs_le c
    have htc : t / 2 ≤ t + c := by linarith
    exact le_trans htc (le_trans (le_abs_self _) (outer_le_completed t c))

theorem completed_positive {t : ℝ} (ht : 0 < t) (c : ℝ) :
    0 < completedMagnitude t c :=
  lt_of_lt_of_le (half_pos ht) (completed_half_lower t c)

/-- Both spatial channels collapse together exactly at the coincident horn throat. -/
theorem paired_zero_iff {t c : ℝ} (ht : 0 < t) (hc : -1 ≤ c) :
    pairedMagnitude t c = 0 ↔ t = 1 ∧ c = -1 := by
  constructor
  · intro h
    have hi : t * (1 + c) ≤ pairedMagnitude t c := le_max_left _ _
    have ho : |t + c| ≤ pairedMagnitude t c := le_max_right _ _
    rw [h] at hi ho
    have hn : 0 ≤ t * (1 + c) := mul_nonneg (le_of_lt ht) (by linarith)
    have hi0 : t * (1 + c) = 0 := le_antisymm hi hn
    have hc0 : 1 + c = 0 := (mul_eq_zero.mp hi0).resolve_left (ne_of_gt ht)
    have ho0 : t + c = 0 := abs_eq_zero.mp (le_antisymm ho (abs_nonneg _))
    exact ⟨by linarith, by linarith⟩
  · rintro ⟨rfl, rfl⟩
    norm_num [pairedMagnitude]

theorem open_pair_lower {t c : ℝ} (hc : -1 ≤ c) :
    t - 1 ≤ pairedMagnitude t c :=
  le_trans (by linarith) (le_trans (le_abs_self _) (le_max_right _ _))

#print axioms normal_centerline
#print axioms completed_positive
#print axioms paired_zero_iff

end Imscribing.TorusFrameReadout
