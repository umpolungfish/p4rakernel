import Imscribing.Biochem.PrimaLogicaMechanicalGlut
import Imscribing.Paraconsistent.TemporalSemantics

enable_trilattice

/-! Native joint potential read by the ensemble's own successor description.
The first coordinate is an observed separation, the second the retained
internal center. Their coefficients are the carried membership extents.
The whole executing conformation supplies all such observations together. -/
namespace Imscribing.Biochem.NativeEnsembleSuccessor

noncomputable section

def potential (c p n r q : ℝ) :=
  c * (p+n) * (r-q)^2 / 2 + c*p*(p+n)*q^2/(2*n)
def radialForce (c p n r q : ℝ) := c*(p+n)*(r-q)
def centerForce (c p n r q : ℝ) := c*(p+n)*((p+n)*q/n-r)

theorem radial_increment (c p n r q h : ℝ) :
    potential c p n (r+h) q - potential c p n r q =
      h*radialForce c p n r q + c*(p+n)*h^2/2 := by
  unfold potential radialForce
  ring

theorem center_increment (c p n r q h : ℝ) (hn : n ≠ 0) :
    potential c p n r (q+h) - potential c p n r q =
      h*centerForce c p n r q + c*(p+n)^2*h^2/(2*n) := by
  unfold potential centerForce
  field_simp
  <;> ring

theorem simultaneous_increment (c p n r q a b : ℝ) (hn : n ≠ 0) :
    potential c p n (r+a) (q+b) - potential c p n r q =
      a*radialForce c p n r q + b*centerForce c p n r q +
      c*(p+n)*(a-b)^2/2 + c*p*(p+n)*b^2/(2*n) := by
  unfold potential radialForce centerForce
  field_simp
  <;> ring

theorem normalized_torsion_direction (force quantum : ℝ) :
    force * (-quantum^2*force) = -(quantum*force)^2 := by ring

theorem projected_release_direction (force extent : ℝ) :
    force * (-extent^2*max force 0) ≤ 0 := by
  by_cases h : 0 ≤ force
  · rw [max_eq_left h]
    have hsq : 0 ≤ (extent*force)^2 := sq_nonneg _
    nlinarith
  · rw [max_eq_right (le_of_lt (lt_of_not_ge h))]
    simp

theorem inclusion_retains_the_added_force (c p n d a b r q : ℝ) :
    radialForce c p n r q + radialForce d a b r q - radialForce c p n r q =
      radialForce d a b r q := by ring

#print axioms radial_increment
#print axioms center_increment
#print axioms simultaneous_increment
#print axioms normalized_torsion_direction
#print axioms projected_release_direction
#print axioms inclusion_retains_the_added_force
end
end Imscribing.Biochem.NativeEnsembleSuccessor
