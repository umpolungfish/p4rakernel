import Mathlib
import Imscribing.PrimeWhorlCore
import Imscribing.PrimeWhorlBurau

/-!
# Live-phase braid transport on a *single* stitched construction

Prime Whorl records a different invertible Burau phase for every signed
crossing, separately on the interior and exterior frame. The exterior frame
uses the opposite sign, as in `unified_holonomy.js`. This is an ordered
*phase-labelled transport*, not (without further constraints) a B₄ group
representation: one may not apply the constant-t Artin relations to arbitrary
live-phase words.

The fork's `StitchedState` contains exactly ONE geometric `Punctum`. Four
Burau coordinates per arithmetic bank do NOT create four geometric punctures.
-/

namespace Imscribing.PrimeWhorl
namespace Burau

variable {R : Type*} [CommRing R]

/-- Extract the positive generator for a four-strand word letter. -/
def generator (phase : UnitPhase R) (index : Fin 3) : Strand4 R ≃ Strand4 R :=
  if index.val = 0 then sigma1 phase
  else if index.val = 1 then sigma2 phase
  else sigma3 phase

/-- Signed generator: negative words use precisely the stored inverse. -/
def signedGenerator (phase : UnitPhase R) (letter : Letter) :
    Strand4 R ≃ Strand4 R :=
  if letter.positive then generator phase letter.index
  else (generator phase letter.index).symm

/-- Reverse a signed letter without changing its strand index. -/
def opposite (letter : Letter) : Letter :=
  { letter with positive := !letter.positive }

@[simp] theorem opposite_opposite (letter : Letter) :
    opposite (opposite letter) = letter := by
  cases letter with
  | mk i positive => cases positive <;> rfl

/-- A recorded live step has two *independent* unit-phase certificates. -/
structure LiveStep (R : Type*) [CommRing R] where
  letter : Letter
  interiorPhase : UnitPhase R
  exteriorPhase : UnitPhase R

/-- Apply independent invertible actions to the two deformed frames. -/
def pairTransport (f g : Strand4 R ≃ Strand4 R) :
    (Strand4 R × Strand4 R) ≃ (Strand4 R × Strand4 R) where
  toFun xy := (f xy.1, g xy.2)
  invFun xy := (f.symm xy.1, g.symm xy.2)
  left_inv := by intro ⟨p, q⟩; simp
  right_inv := by intro ⟨p, q⟩; simp

/-- Each real live step is an invertible signed crossing on BOTH bank readings;
    exterior orientation is mirrored without equating its phase to interior. -/
def liveAction (step : LiveStep R) :
    (Strand4 R × Strand4 R) ≃ (Strand4 R × Strand4 R) :=
  pairTransport
    (signedGenerator step.interiorPhase step.letter)
    (signedGenerator step.exteriorPhase (opposite step.letter))

/-- Adapt the live phase-labelled step to the existing fork `SignedCrossing`.
    The action retains its phases internally; `LiveStep` retains them explicitly. -/
def asSignedCrossing (step : LiveStep R) : SignedCrossing (Strand4 R) where
  label := step.letter
  action := liveAction step

/-- Every phase-labelled sequence gives invertible paired transport.
    Reverse the sequence *for column-vector application*, so that chronological
    letters `[g1,g2]` act as `M(g1) * M(g2)`, matching the JS forward matrix
    accumulation `M ← M * generator`. The historical record stays chronological. -/
def liveWordAction (steps : List (LiveStep R)) :
    (Strand4 R × Strand4 R) ≃ (Strand4 R × Strand4 R) :=
  wordAction ((steps.map asSignedCrossing).reverse)

/-- The braid updates the existing bank readings, but retains one geometrical
    punctum and records the steps in chronological order, as the browser does.
    For this JS matrix-product convention use `live_reconstruction` below;
    generic `reconstructBanks` in the scaffold uses a different word order. -/
def applyLiveWord (s : StitchedState (Strand4 R))
    (steps : List (LiveStep R)) : StitchedState (Strand4 R) :=
  let xy := liveWordAction steps (banks s)
  { s with interior := xy.1, exterior := xy.2,
           history := s.history ++ (steps.map asSignedCrossing) }

/-- Retain the complete source state and the chronological phase-bearing
    history. `current` is the semantic replay of *one continuing execution*;
    an optimized driver may cache its accumulated operator. In particular,
    this definition never treats an appended batch as a new source/trial. -/
structure LiveExecution (R : Type*) [CommRing R] where
  origin : StitchedState (Strand4 R)
  steps : List (LiveStep R)

/-- The currently reconstructed state, with all previous steps accounted for. -/
def current (run : LiveExecution R) : StitchedState (Strand4 R) :=
  applyLiveWord run.origin run.steps

/-- Continue the *same* history; no repinning, no changing N, no new trial. -/
def advance (run : LiveExecution R) (extra : List (LiveStep R)) : LiveExecution R :=
  { run with steps := run.steps ++ extra }

/-- Stop/resume equivalence at the level of complete replayed state: batching
    an operation sequence does not change the resulting construction. -/
theorem advance_is_batch_independent (run : LiveExecution R)
    (a b : List (LiveStep R)) :
    current (advance (advance run a) b) =
      current (advance run (a ++ b)) := by
  simp [current, advance, List.append_assoc]

/-- A live word never changes the source or the single tether point. -/
theorem live_retains_source (s : StitchedState (Strand4 R))
    (steps : List (LiveStep R)) :
    (applyLiveWord s steps).source = s.source := rfl

theorem live_retains_punctum (s : StitchedState (Strand4 R))
    (steps : List (LiveStep R)) :
    (applyLiveWord s steps).punctum = s.punctum := rfl

theorem live_retains_geometry (s : StitchedState (Strand4 R))
    (steps : List (LiveStep R)) :
    (applyLiveWord s steps).geometry = s.geometry := rfl

/-- Reconstruction is an inverse *of the recorded steps*, including both
    live phase sequences. No assumption of phase constancy is needed. -/
theorem live_reconstruction (s : StitchedState (Strand4 R))
    (steps : List (LiveStep R)) :
    (liveWordAction steps).symm (banks (applyLiveWord s steps)) =
      banks s := by
  change (liveWordAction steps).symm
    ((liveWordAction steps) (banks s)) = banks s
  exact (liveWordAction steps).symm_apply_apply (banks s)

/-- Transport preserves all source-side data stored in the persistent record,
    and recovery does not simply read `s.source` as the reconstructed bank. -/
theorem live_reconstruct_from_copy (N : Nat) (site : Punctum)
    (x : Strand4 R) (steps : List (LiveStep R)) :
    (liveWordAction steps).symm
      (banks (applyLiveWord (copySource N site x) steps)) = (x, x) := by
  simpa [banks, copySource] using
    live_reconstruction (copySource N site x) steps

/-- Actual negative-phase reversal is the inverse of the same signed step.
    Importantly, `step.interiorPhase` and `step.exteriorPhase` are NOT swapped. -/
theorem live_step_reversible (step : LiveStep R)
    (pq : Strand4 R × Strand4 R) :
    (liveAction step).symm ((liveAction step) pq) = pq := by
  exact (liveAction step).symm_apply_apply pq

/-- The algebra also supports exact reconstruction after a certified,
    invertible deformation of the already stitched paired readings. -/
theorem deform_braid_reconstruct
    (deformation : (Strand4 R × Strand4 R) ≃
                    (Strand4 R × Strand4 R))
    (steps : List (LiveStep R)) (original : Strand4 R × Strand4 R) :
    deformation.symm ((liveWordAction steps).symm
      ((liveWordAction steps) (deformation original))) = original := by
  simp

end Burau
end Imscribing.PrimeWhorl
