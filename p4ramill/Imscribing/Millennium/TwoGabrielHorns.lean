import Mathlib
import Imscribing.Millennium.HornTorusGeometry
open Imscribing.HornTorus
namespace Imscribing.Millennium.TwoGabrielHorns
noncomputable section

/-- The two Gabriel horns: the upper sheet u in [0,pi] (z >= 0) and the lower
    sheet u in [pi,2pi] (z <= 0). They are mirror images across z=0. -/
def upperHorn (R u v : ℝ) : Point := horn R u v
def lowerHorn (R u v : ℝ) : Point := horn R (2 * Real.pi - u) v

theorem lowerHorn_mirror (R u v : ℝ) :
    lowerHorn R u v = ((horn R u v).1, (horn R u v).2.1, -((horn R u v).2.2)) := by
  unfold lowerHorn horn
  simp [Real.sin_two_pi_sub, Real.cos_two_pi_sub]

/-- The stitching seams: both sheets meet at the outer equator u=0 and at the
    pinch u=pi. At the pinch the whole v-circle self-identifies to the origin:
    that is the self-reference (F(F) / re-entry). -/
theorem two_horns_stitched (R : ℝ) :
    upperHorn R 0 = lowerHorn R 0 ∧
    upperHorn R Real.pi = lowerHorn R Real.pi ∧
    (∀ v : ℝ, upperHorn R Real.pi v = origin) := by
  refine ⟨?_, ?_, ?_⟩
  · funext v
    unfold upperHorn lowerHorn
    rw [show 2 * Real.pi - 0 = 2 * Real.pi by ring]
    simp [horn, Real.cos_two_pi, Real.sin_two_pi]
  · funext v
    unfold upperHorn lowerHorn
    rw [show 2 * Real.pi - Real.pi = Real.pi by ring]
  · intro v
    unfold upperHorn horn origin
    simp [Real.cos_pi, Real.sin_pi]

/-- The self-referenced horn: identifying the whole v-circle at the pinch to
    one point is the re-entry. -/
theorem horn_self_reference (R : ℝ) :
    (∀ v : ℝ, horn R Real.pi v = origin) ∧
    horn R 0 0 = (2 * R, 0, 0) := by
  refine ⟨?_, ?_⟩
  · intro v
    unfold horn origin
    simp [Real.cos_pi, Real.sin_pi]
  · simpa [gamma] using gamma_zero R

