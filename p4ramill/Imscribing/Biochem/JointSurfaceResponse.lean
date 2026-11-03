import Mathlib

/-! Reduced native one-probe joint response, with the geometric guard retained.
This diagnoses the response model's preference; it is not a protein theorem.
-/
namespace Imscribing.Biochem.JointSurfaceResponse

noncomputable def potential (a b c length distance : ℝ) : ℝ :=
  -(a+b*length/distance+c*length*length/(distance*distance))

theorem retained_work (a b c length boundary distance : ℝ)
    (hb : boundary ≠ 0) (hd : distance ≠ 0) :
    potential a b c length distance - potential a b c length boundary =
      (distance-boundary)/(distance*boundary)*
        (b*length+c*length*length*(distance+boundary)/(distance*boundary)) := by
  unfold potential
  field_simp
  <;> ring

/-- Positive response coefficients select the admitted lower separation.
The full conformation still needs its atom and orientation constraints. -/
theorem source_pair_favors_guard_boundary (a b c length boundary distance : ℝ)
    (hb : 0 ≤ b) (hc : 0 ≤ c) (hl : 0 < length) (hboundary : 0 < boundary)
    (admitted : boundary ≤ distance) :
    potential a b c length boundary ≤ potential a b c length distance := by
  have hd : 0 < distance := lt_of_lt_of_le hboundary admitted
  have gap : 0 ≤ distance-boundary := sub_nonneg.mpr admitted
  have work := retained_work a b c length boundary distance (ne_of_gt hboundary) (ne_of_gt hd)
  have nonnegative : 0 ≤ (distance-boundary)/(distance*boundary)*
      (b*length+c*length*length*(distance+boundary)/(distance*boundary)) := by positivity
  linarith

#print axioms retained_work
#print axioms source_pair_favors_guard_boundary
end Imscribing.Biochem.JointSurfaceResponse
