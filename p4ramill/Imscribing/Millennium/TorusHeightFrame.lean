import Mathlib.Tactic.Ring

namespace Imscribing.TorusHeightFrame

variable {A : Type*} [CommRing A]

/-- The homogeneous signed-height circle identity works over the source ring. -/
theorem homogeneous_height_norm (h : A) :
    (h ^ 2 - 1) ^ 2 + (2 * h) ^ 2 = (h ^ 2 + 1) ^ 2 := by
  ring

/-- Normalization requires an actual denominator inverse; nonunits are held. -/
theorem normalized_height_norm (h u : A) (hu : (h ^ 2 + 1) * u = 1) :
    ((h ^ 2 - 1) * u) ^ 2 + ((2 * h) * u) ^ 2 = 1 := by
  calc
    _ = ((h ^ 2 - 1) ^ 2 + (2 * h) ^ 2) * u ^ 2 := by ring
    _ = ((h ^ 2 + 1) * u) ^ 2 := by rw [homogeneous_height_norm]; ring
    _ = 1 := by rw [hu]; ring

/-- Normal subtraction is polynomial, including at a collapsed source point. -/
theorem normal_centerline (R r ca sa cb sb : A) :
    ((R * ca + r * (ca * cb)) - r * (ca * cb),
     (R * sa + r * (sa * cb)) - r * (sa * cb), r * sb - r * sb) =
    (R * ca, R * sa, 0) := by
  apply Prod.ext
  · ring
  · apply Prod.ext
    · ring
    · ring

/-- The complete miniature and outer frame share their coherent normal. -/
theorem miniature_correspondence (R r ca sa cb sb : A) :
    ((R * ca + r * (ca * cb)) - (R * ca + R * (ca * cb)),
     (R * sa + r * (sa * cb)) - (R * sa + R * (sa * cb)), r * sb - R * sb) =
    ((r - R) * (ca * cb), (r - R) * (sa * cb), (r - R) * sb) := by
  apply Prod.ext
  · ring
  · apply Prod.ext
    · ring
    · ring

/-- The projected normal recovers the tube coordinate in the same ring. -/
theorem projected_tube (ca sa cb : A) (hc : ca ^ 2 + sa ^ 2 = 1) :
    (ca * cb) * ca + (sa * cb) * sa = cb := by
  calc
    _ = cb * (ca ^ 2 + sa ^ 2) := by ring
    _ = cb := by rw [hc]; ring

/-- Exact height zero reaches the source horn throat; directions remain carried. -/
theorem height_zero_throat (h u ca sa : A) (hz : h = 0)
    (hu : (h ^ 2 + 1) * u = 1) :
    (ca * (1 + (h ^ 2 - 1) * u), sa * (1 + (h ^ 2 - 1) * u), (2 * h) * u) =
    (0, 0, 0) := by
  subst h
  have hu1 : u = 1 := by simpa using hu
  simp [hu1]

/-- Product closure is separate from the proper-divisor requirement. -/
theorem height_zero_product (p q n h scale : A)
    (relation : p * q = n + h * scale) (hz : h = 0) : p * q = n := by
  simpa [hz] using relation

#print axioms normalized_height_norm
#print axioms normal_centerline
#print axioms height_zero_throat

end Imscribing.TorusHeightFrame
