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

#print axioms transported_source_gram
#print axioms complete_square
#print axioms fixed_point_is_mechanical_minimum
#print axioms diagonal_source_orientation_independent
end Imscribing.Biochem.DirectionalContactGram
