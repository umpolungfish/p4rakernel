import Mathlib

/-! Transport of the existing mixed contact Gram into retained local frames.
No contact admission or molecular angle table is supplied by these identities.
The proton fixed-point equation and mechanical minimum use one quadratic. -/
namespace Imscribing.Biochem.DirectionalContactGram

abbrev Point := ℝ × ℝ × ℝ
abbrev Rows := Point × Point × Point
def dot (x y : Point) := x.1*y.1+x.2.1*y.2.1+x.2.2*y.2.2
def sub (x y : Point) : Point := (x.1-y.1,x.2.1-y.2.1,x.2.2-y.2.2)
def scale (a : ℝ) (x : Point) : Point := (a*x.1,a*x.2.1,a*x.2.2)
def add (x y : Point) : Point := (x.1+y.1,x.2.1+y.2.1,x.2.2+y.2.2)
def applyRows (r : Rows) (x : Point) : Point := (dot r.1 x,dot r.2.1 x,dot r.2.2 x)
def transpose (r : Rows) : Rows :=
  ((r.1.1,r.2.1.1,r.2.2.1),
   (r.1.2.1,r.2.1.2.1,r.2.2.2.1),
   (r.1.2.2,r.2.1.2.2,r.2.2.2.2))

structure Symmetric where
  xx : ℝ
  xy : ℝ
  xz : ℝ
  yy : ℝ
  yz : ℝ
  zz : ℝ

def act (m : Symmetric) (x : Point) : Point :=
  (m.xx*x.1+m.xy*x.2.1+m.xz*x.2.2,
   m.xy*x.1+m.yy*x.2.1+m.yz*x.2.2,
   m.xz*x.1+m.yz*x.2.1+m.zz*x.2.2)
def energy (m : Symmetric) (b : Point) (constant : ℝ) (x : Point) : ℝ :=
  dot x (act m x)-2*dot b x+constant

def frameMatrix (pd pa c : ℝ) (r : Rows) : Symmetric :=
  ⟨pd+pa+2*c*r.1.1, c*(r.1.2.1+r.2.1.1), c*(r.1.2.2+r.2.2.1),
   pd+pa+2*c*r.2.1.2.1, c*(r.2.1.2.2+r.2.2.2.1),pd+pa+2*c*r.2.2.2.2⟩
def frameFirst (pa c : ℝ) (r : Rows) (d : Point) : Point :=
  add (scale pa d) (scale c (applyRows (transpose r) d))
def sourcePotential (pd pa c : ℝ) (r : Rows) (d x : Point) :=
  pd*dot x x+pa*dot (sub x d) (sub x d)+2*c*dot x (applyRows (transpose r) (sub x d))

theorem transported_source_gram (pd pa c : ℝ) (r : Rows) (d x : Point) :
    energy (frameMatrix pd pa c r) (frameFirst pa c r d) (pa*dot d d) x =
      sourcePotential pd pa c r d x := by
  simp only [energy,frameMatrix,frameFirst,sourcePotential,act,dot,sub,add,scale,applyRows,transpose]
  ring

/-- A diagonal source has no orientation cross-term. The frame alternatives
remain carried; their evaluation reduces exactly, without a small-value cutoff. -/
theorem diagonal_source_orientation_independent (pd pa : ℝ) (r s : Rows) (d x : Point) :
    sourcePotential pd pa 0 r d x = sourcePotential pd pa 0 s d x := by
  simp [sourcePotential]

theorem complete_square (m : Symmetric) (b root x : Point) (constant : ℝ)
    (stationary : act m root = b) :
    energy m b constant x-energy m b constant root =
      dot (sub x root) (act m (sub x root)) := by
  simp only [energy]
  rw [← stationary]
  simp only [dot,act,sub]
  ring

theorem fixed_point_is_mechanical_minimum (m : Symmetric) (b root x : Point) (constant : ℝ)
    (stationary : act m root = b)
    (positive : ∀ v, 0 ≤ dot v (act m v)) :
    energy m b constant root ≤ energy m b constant x := by
  have equality := complete_square m b root x constant stationary
  have nonnegative := positive (sub x root)
  linarith

/-- Identifying the proton operands of retained candidate alternatives adds
exactly their quadratic root dispersion. The source alternative index therefore
cannot be erased without changing the same mechanical response. -/
theorem conditional_roots_retain_response {ι : Type*} (indices : Finset ι)
    (m : Symmetric) (b : ι → Point) (constant : ι → ℝ)
    (roots : ι → Point) (shared : Point)
    (stationary : ∀ i ∈ indices, act m (roots i) = b i) :
    (∑ i ∈ indices, energy m (b i) (constant i) shared) -
      (∑ i ∈ indices, energy m (b i) (constant i) (roots i)) =
      ∑ i ∈ indices, dot (sub shared (roots i)) (act m (sub shared (roots i))) := by
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  exact complete_square m (b i) (roots i) shared (constant i) (stationary i hi)

#print axioms conditional_roots_retain_response
/-- A rejected squared-distance predicate supplies a tangent normal on the
same retained coordinates. This is the exact boundary action used by each
halfspace contraction, without an added distance threshold. -/
theorem rejected_predicate_tangent (normal force : Point)
    (nonzero : dot normal normal ≠ 0) :
    dot normal (sub force (scale (dot normal force / dot normal normal) normal)) = 0 := by
  have linear : dot normal (sub force (scale (dot normal force / dot normal normal) normal)) =
      dot normal force - (dot normal force / dot normal normal) * dot normal normal := by
    simp only [dot,sub,scale]
    ring
  rw [linear, div_mul_cancel₀ _ nonzero, sub_self]

/-- A rejected native inequality retains its actual clearance, rather than
being silently replaced by a zero-clearance tangent condition. -/
theorem rejected_predicate_affine_boundary (normal step : Point) (clearance : ℝ)
    (nonzero : dot normal normal ≠ 0) :
    clearance + dot normal
      (add step (scale ((-clearance-dot normal step)/dot normal normal) normal)) = 0 := by
  have linear : dot normal
      (add step (scale ((-clearance-dot normal step)/dot normal normal) normal)) =
      dot normal step + ((-clearance-dot normal step)/dot normal normal)*dot normal normal := by
    simp only [dot,add,scale]
    ring
  rw [linear, div_mul_cancel₀ _ nonzero]
  ring

/-- The same clearance-preserving contraction on the complete finite native
coordinate register, including every backbone and sidechain generator. -/
theorem finite_coordinate_affine_boundary {n : ℕ} (row step : Fin n → ℝ)
    (clearance : ℝ) (nonzero : (∑ i, row i * row i) ≠ 0) :
    clearance + (∑ i, row i * (step i +
      ((-clearance-(∑ j, row j * step j))/(∑ j, row j * row j))*row i)) = 0 := by
  let delta := (-clearance-(∑ j, row j * step j))/(∑ j, row j * row j)
  have linear : (∑ i, row i * (step i + delta*row i)) =
      (∑ i, row i*step i) + delta*(∑ i, row i*row i) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  change clearance + (∑ i, row i * (step i + delta*row i)) = 0
  rw [linear]
  dsimp [delta]
  rw [div_mul_cancel₀ _ nonzero]
  ring

#print axioms finite_coordinate_affine_boundary
#print axioms rejected_predicate_affine_boundary
#print axioms rejected_predicate_tangent
#print axioms transported_source_gram
#print axioms complete_square
#print axioms fixed_point_is_mechanical_minimum
#print axioms diagonal_source_orientation_independent
end Imscribing.Biochem.DirectionalContactGram
