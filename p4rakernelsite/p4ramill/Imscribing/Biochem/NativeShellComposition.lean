import Imscribing.Biochem.NativeOrbitalTransfer

/-! Exact composition of the existing native Glut readout on indexed shells.
The source remains a list of FOUR occupancies. Counts are additive observers;
they do not replace the retained placements or select a filling branch. -/
namespace Imscribing.PrimaLogica.NativeOrbitalTransfer
open Imscribing.Paraconsistent.Orbital

def shellUp (s : List OrbitalState) : Nat := (s.map up).sum
def shellDown (s : List OrbitalState) : Nat := (s.map down).sum

theorem pair_glut_composition (a b : OrbitalState) :
    spinGlutDouble (up a + up b) (down a + down b) =
      2 * (up a * down b + up b * down a +
        pairedCount a * (1 + up b + down b) +
        pairedCount b * (1 + up a + down a)) := by
  cases a <;> cases b <;> decide

theorem single_glut (a : OrbitalState) :
    spinGlutDouble (up a) (down a) = 2 * pairedCount a := by
  cases a <;> decide

theorem pair_glut_sum (a : OrbitalState) (s : List OrbitalState) :
    (s.map fun b => spinGlutDouble (up a + up b) (down a + down b)).sum =
      2 * (up a * shellDown s + down a * shellUp s +
        pairedCount a * (s.length + shellUp s + shellDown s) +
        shellPaired s * (1 + up a + down a)) := by
  induction s with
  | nil => simp [shellUp, shellDown, shellPaired]
  | cons b s ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons, pair_glut_composition,
      shellUp, shellDown, shellPaired] at *
    rw [ih]
    ring

/-- A subtraction-free whole-shell identity, valid at every shell size. -/
theorem shell_glut_closed (s : List OrbitalState) :
    shellGlutDouble s + 6 * shellPaired s =
      2 * shellUp s * shellDown s +
        2 * shellPaired s * (s.length + shellUp s + shellDown s) := by
  induction s with
  | nil => simp [shellGlutDouble, shellUp, shellDown, shellPaired]
  | cons a s ih =>
    rw [shellGlutDouble, single_glut, pair_glut_sum]
    cases a <;>
      simp only [shellUp, shellDown, shellPaired, List.map_cons, List.sum_cons,
        List.length_cons, up, down, pairedCount] at * <;> nlinarith

/-- Full fusion adds each cross-shell pair once, retaining the two source
shells and their internal Glut. No valence or interaction coefficient is input. -/
theorem shell_glut_fusion (a b : List OrbitalState) :
    shellGlutDouble (a ++ b) = shellGlutDouble a + shellGlutDouble b +
      2 * (shellUp a * shellDown b + shellUp b * shellDown a +
        shellPaired a * (b.length + shellUp b + shellDown b) +
        shellPaired b * (a.length + shellUp a + shellDown a)) := by
  have ha := shell_glut_closed a
  have hb := shell_glut_closed b
  have hab := shell_glut_closed (a ++ b)
  simp only [shellUp, shellDown, shellPaired, List.map_append, List.sum_append,
    List.length_append] at *
  nlinarith

theorem shell_glut_fusion_associative (a b c : List OrbitalState) :
    shellGlutDouble ((a ++ b) ++ c) = shellGlutDouble (a ++ (b ++ c)) := by
  rw [List.append_assoc]

#print axioms pair_glut_composition
#print axioms pair_glut_sum
#print axioms shell_glut_closed
#print axioms shell_glut_fusion
#print axioms shell_glut_fusion_associative
end Imscribing.PrimaLogica.NativeOrbitalTransfer
