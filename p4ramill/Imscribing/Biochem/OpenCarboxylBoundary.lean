import Mathlib

/-! Inventory and frame identities for the unfused terminal carboxyl port.
These establish the open-chain count and the chosen source-frame lift.
They do not determine an absolute bond length or a native fold. -/
namespace Imscribing.Biochem.OpenCarboxylBoundary

theorem retained_oxygen_count (n : ℕ) (nonempty : 0 < n) :
    2*n-(n-1)=n+1 := by omega

abbrev Point := ℝ × ℝ × ℝ
def dot (x y : Point) := x.1*y.1+x.2.1*y.2.1+x.2.2*y.2.2
def halfTurn (a x : Point) : Point :=
  (2*dot a x*a.1-x.1, 2*dot a x*a.2.1-x.2.1,
   2*dot a x*a.2.2-x.2.2)

theorem axial_projection (a x : Point) (unit : dot a a=1) :
    dot a (halfTurn a x)=dot a x := by
  have h : dot a (halfTurn a x) = 2*dot a x*dot a a-dot a x := by
    simp only [dot,halfTurn]; ring
  rw [h,unit]; ring

theorem squared_length (a x : Point) (unit : dot a a=1) :
    dot (halfTurn a x) (halfTurn a x)=dot x x := by
  have h : dot (halfTurn a x) (halfTurn a x) =
      dot x x+4*(dot a x)^2*(dot a a-1) := by
    simp only [dot,halfTurn]; ring
  rw [h,unit]; ring

#print axioms retained_oxygen_count
#print axioms axial_projection
#print axioms squared_length
end Imscribing.Biochem.OpenCarboxylBoundary
