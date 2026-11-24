import Mathlib.Tactic.Ring

namespace Imscribing.TorusSourceMetric

variable {A : Type*} [CommRing A]

/-- Exact homogeneous radii avoid a numerical square root in the source bank. -/
theorem source_radii (p q n : A) :
    (p + q) ^ 2 - ((p - q) ^ 2 + 4 * n) = 4 * (p * q - n) := by
  ring

/-- Fuse of the internal half-sum/difference returns the source pair. -/
theorem source_split_fuse (p q half : A) (h : 2 * half = 1) :
    (half * (p + q) + half * (p - q),
     half * (p + q) - half * (p - q)) = (p, q) := by
  apply Prod.ext
  · calc
      _ = (2 * half) * p := by ring
      _ = p := by rw [h]; ring
  · calc
      _ = (2 * half) * q := by ring
      _ = q := by rw [h]; ring

/-- The product relation is the difference of the source metric radii. -/
theorem inner_product_defect (u v n : A) :
    (u + v) * (u - v) - n = u ^ 2 - (v ^ 2 + n) := by
  ring

/-- A complementary integer representative carries the full signed height. -/
theorem complementary_lift (p q n scale height : A)
    (h : p * q = n + height * scale) :
    p * (q - scale) = n + (height - p) * scale := by
  calc
    _ = p * q - p * scale := by ring
    _ = n + (height - p) * scale := by rw [h]; ring

/-- The real source Gram observable uses both off-diagonal entries. -/
theorem source_gram_defect (p q n : A) :
    p * q + n * (1 * (-1)) = p * q - n := by
  ring

/-- The sphere split retains its complementary direction as well as its sum. -/
theorem sphere_pair_orthogonality
    (sx sy sz ex ey ez : A)
    (h : sx ^ 2 + sy ^ 2 + sz ^ 2 = ex ^ 2 + ey ^ 2 + ez ^ 2) :
    (sx + ex) * (sx - ex) + (sy + ey) * (sy - ey) +
      (sz + ez) * (sz - ez) = 0 := by
  calc
    _ = (sx ^ 2 + sy ^ 2 + sz ^ 2) - (ex ^ 2 + ey ^ 2 + ez ^ 2) := by ring
    _ = 0 := by rw [h]; ring

#print axioms source_radii
#print axioms source_split_fuse
#print axioms complementary_lift

end Imscribing.TorusSourceMetric
