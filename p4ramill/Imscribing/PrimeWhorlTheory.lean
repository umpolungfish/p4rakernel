import Mathlib
import Init.Paraconsistent
import Imscribing.PrimeWhorlCore
import Imscribing.PrimeWhorlBurau
import Imscribing.PrimeWhorlLiveBraid
import Imscribing.PrimeWhorlPaperCarrier

/-!
# Prime Whorl: one mathematical construction

One source modulus, one marked sphere-skin punctum, two tethered arithmetic
realizations, deformation, a signed four-strand Burau action, a non-explosive
information carrier, and source-derived factor certification.

The construction *computes* a defect from the transformed frames. A successful
readout contains an exact divisor theorem. A concrete cubic punctum phase gives
braid-generated witnesses for 299 and 5917.

No particular factor, or fact that a divisor must occur for every composite,
is built into the definition of the construction.
-/

namespace Imscribing.PrimeWhorl.Theory

open Lean
open Imscribing.PrimeWhorl
open Imscribing.PrimeWhorl.Burau

/-! ## Paraconsistent evidence: inconsistent support is a live state -/

def truthSupported (X : Paper.Carrier) : Prop := Paper.Atom.T ∈ X

def falsitySupported (X : Paper.Carrier) : Prop := Paper.Atom.F ∈ X

def isGlut (X : Paper.Carrier) : Prop :=
  truthSupported X ∧ falsitySupported X

/-- A contradiction at one proposition does not designate an unrelated one.
    This is an explicit countervaluation to explosion. -/
theorem retained_glut_does_not_explode :
    ∃ v : Bool → Paper.Carrier,
       isGlut (v true) ∧ ¬ truthSupported (v false) := by
  refine ⟨(fun b => if b then Set.univ else {Paper.Atom.F}), ?_⟩
  simp [isGlut, truthSupported, falsitySupported]

/-- The middle information arm is not discarded by decomposition/fusion. -/
theorem information_reconnection (X : Paper.Carrier) :
    Paper.mu3 (Paper.delta3 X) = X :=
  Paper.mu3_delta3 X

/-! ## One source, one punctum, two transformed readings -/

abbrev Fibre (N : Nat) [NeZero N] := Strand4 (ZMod N)
abbrev Frames (N : Nat) [NeZero N] := Fibre N × Fibre N

/-- A single source-marked construction, not two separately pinned spheres.
    The braid fibre has four arithmetic coordinates, not four skin punctures. -/
structure Whorl (N : Nat) [NeZero N] where
  stitch : Punctum
  shape : Geometry
  sourceReading : Fibre N
  deformation : Frames N ≃ Frames N
  liveBraid : List (LiveStep (ZMod N))
  retainedInformation : Paper.Carrier
  filtrationCut : Fin 12

/-- Both copies originate in exactly the same marked source reading. -/
def Whorl.copied {N : Nat} [NeZero N] (w : Whorl N) : Frames N :=
  (w.sourceReading, w.sourceReading)

/-- Deform, then apply the entire phase-bearing signed braid to the copies. -/
def Whorl.transformed {N : Nat} [NeZero N] (w : Whorl N) : Frames N :=
  liveWordAction w.liveBraid (w.deformation w.copied)

/-- Reconstruction acts on the *transformed frames*, not on a stored factor. -/
def Whorl.reconstruct {N : Nat} [NeZero N] (w : Whorl N) : Frames N :=
  w.deformation.symm ((liveWordAction w.liveBraid).symm w.transformed)

/-- Full source reconstruction, despite different intermediate frame readings. -/
theorem Whorl.reconstruction {N : Nat} [NeZero N] (w : Whorl N) :
    w.reconstruct = w.copied := by
  simp [Whorl.reconstruct, Whorl.transformed, Whorl.copied]

/-- The point is not replaced by deforming or braiding the copies. -/
def Whorl.withMoreBraid {N : Nat} [NeZero N]
    (w : Whorl N) (steps : List (LiveStep (ZMod N))) : Whorl N :=
  { w with liveBraid := w.liveBraid ++ steps }

theorem Whorl.stitch_retained {N : Nat} [NeZero N]
    (w : Whorl N) (steps : List (LiveStep (ZMod N))) :
    (w.withMoreBraid steps).stitch = w.stitch := rfl

/-- Paraconsistent glut remains an engaged state during continuous braiding. -/
theorem Whorl.glut_retained {N : Nat} [NeZero N]
    (w : Whorl N) (steps : List (LiveStep (ZMod N)))
    (h : isGlut w.retainedInformation) :
    isGlut (w.withMoreBraid steps).retainedInformation := h

/-- Move the observer cut through one of twelve sectors without changing the
    source, its unique stitch point, or its existing braided realizations. -/
def Whorl.rotateCut {N : Nat} [NeZero N] (w : Whorl N) : Whorl N :=
  { w with filtrationCut :=
      ⟨(w.filtrationCut.val + 1) % 12, Nat.mod_lt _ (by decide)⟩ }

theorem Whorl.rotating_cut_preserves_reconstruction {N : Nat} [NeZero N]
    (w : Whorl N) : (w.rotateCut).reconstruct = w.reconstruct := rfl

theorem Whorl.rotating_cut_preserves_stitch {N : Nat} [NeZero N]
    (w : Whorl N) : (w.rotateCut).stitch = w.stitch := rfl

/-- Stop/resume and one uninterrupted continuation are the same mathematics. -/
theorem Whorl.continuation_assoc {N : Nat} [NeZero N]
    (w : Whorl N) (a b : List (LiveStep (ZMod N))) :
    (w.withMoreBraid a).withMoreBraid b = w.withMoreBraid (a ++ b) := by
  simp [Whorl.withMoreBraid, List.append_assoc]

/-! ## Genuine relational observation and operative carrier -/

/-- A cross-frame defect produced after deformation and the live braid.
    The representative `val` is taken only at arithmetic readout. -/
def Whorl.crossDefect {N : Nat} [NeZero N] (w : Whorl N) : ZMod N :=
  w.transformed.1.x0 - w.transformed.2.x0

/-- Memberships are earned by nontrivial transformed relationships.
    N: retained source, T: interior changed, F: exterior changed,
    B: cross-frame difference. The native carrier stores all four memberships. -/
noncomputable def Whorl.operativeCarrier {N : Nat} [NeZero N]
    (w : Whorl N) : Lean.Sixteen3 := by
  classical
  exact Lean.Sixteen3.ofMask
    (1 + (if w.transformed.1 = w.sourceReading then 0 else 2)
       + (if w.transformed.2 = w.sourceReading then 0 else 4)
       + (if w.transformed.1 = w.transformed.2 then 0 else 8))

/-- Full support is a checkable property of the actual transformed readings;
    it is not obtained by setting the target mask unconditionally. -/
theorem Whorl.full_carrier_of_relations {N : Nat} [NeZero N]
    (w : Whorl N)
    (hp : w.transformed.1 ≠ w.sourceReading)
    (hq : w.transformed.2 ≠ w.sourceReading)
    (hpq : w.transformed.1 ≠ w.transformed.2) :
    w.operativeCarrier = Lean.Sixteen3.ofMask 15 := by
  simp [Whorl.operativeCarrier, hp, hq, hpq]

/-- One observation clock, with separate strand and layer coordinates. -/
def strandSector (k : Fin 12) : Fin 4 := ⟨k.val % 4, Nat.mod_lt _ (by decide)⟩
def layerSector (k : Fin 12) : Fin 3 := ⟨k.val % 3, Nat.mod_lt _ (by decide)⟩

theorem sectors_four_ten_share_layer :
    layerSector ⟨4, by decide⟩ = layerSector ⟨10, by decide⟩ := by decide

theorem sectors_four_ten_have_different_strands :
    strandSector ⟨4, by decide⟩ ≠ strandSector ⟨10, by decide⟩ := by decide

/-! ## The divisor theorem is a readout of the same braid construction -/

/-- The divisor is never an assumed interior or exterior channel value.
    It is the GCD of the original modulus with the generated cross-frame defect. -/
structure FactorReadout {N : Nat} [NeZero N] (w : Whorl N) where
  divisor : Nat
  fromDefect : divisor = Nat.gcd N w.crossDefect.val
  proper : 1 < divisor ∧ divisor < N ∧ divisor ∣ N

/-- Construct a certified factor from the transformed braided copies,
    or return none. No factor is furnished to the initialization. -/
def Whorl.extract {N : Nat} [NeZero N]
    (w : Whorl N) : Option (FactorReadout w) := by
  let d := Nat.gcd N w.crossDefect.val
  if hlo : 1 < d then
    if hhi : d < N then
      exact some {
        divisor := d
        fromDefect := rfl
        proper := ⟨hlo, hhi, Nat.gcd_dvd_left N w.crossDefect.val⟩
      }
    else
      exact none
  else
    exact none

/-- One theorem about the construction: exact reconstructed origin together
    with exact, certified factor extraction from its braided relational defect. -/
theorem Whorl.reconstructs_and_factors {N : Nat} [NeZero N]
    (w : Whorl N) (out : FactorReadout w)
    (h : w.extract = some out) :
    w.reconstruct = w.copied ∧
    out.divisor = Nat.gcd N w.crossDefect.val ∧
    1 < out.divisor ∧ out.divisor < N ∧ out.divisor ∣ N := by
  exact ⟨w.reconstruction, out.fromDefect,
         out.proper.1, out.proper.2.1, out.proper.2.2⟩

/-! ## A concrete mirrored Artin crossing produces a cubic punctum defect -/

/-- One source-derived braid fibre; both copies receive this same fibre. -/
def canonical (R : Type*) [CommRing R] : Strand4 R :=
  ⟨1, 0, 0, 0⟩

/-- Signed σ₁ on the interior, signed σ₁⁻¹ on the exterior, with the
    SAME recorded unit parameter. This is a genuine Burau crossing. -/
def mirroredStep {R : Type*} [CommRing R]
    (phase : UnitPhase R) : LiveStep R where
  letter := { index := ⟨0, by decide⟩, positive := true }
  interiorPhase := phase
  exteriorPhase := phase

def mirroredBraid {R : Type*} [CommRing R]
    (phase : UnitPhase R) : Strand4 R × Strand4 R :=
  liveWordAction [mirroredStep phase] (canonical R, canonical R)

/-- The actual Burau blocks give opposing first coordinates 1-t and 0. -/
theorem mirrored_first_coordinates {R : Type*} [CommRing R]
    (phase : UnitPhase R) :
    (mirroredBraid phase).1.x0 = 1 - phase.t ∧
    (mirroredBraid phase).2.x0 = 0 := by
  constructor
  · change (1 - phase.t) * 1 + phase.t * 0 = 1 - phase.t
    ring
  · rfl

/-- The *relational* braid defect is 1-t, not a supplied divisor. -/
theorem mirrored_defect {R : Type*} [CommRing R]
    (phase : UnitPhase R) :
    (mirroredBraid phase).1.x0 - (mirroredBraid phase).2.x0 =
       1 - phase.t := by
  obtain ⟨hp, hq⟩ := mirrored_first_coordinates phase
  rw [hp, hq, sub_zero]

/-- The punctum address a supplies a cubic phase a³. Its invertibility is
    an explicit arithmetic condition; no invalid inverse is silently used. -/
def cubicPhase (N : Nat) [NeZero N] (a inv : Nat)
    (h : ((a : ZMod N) ^ 3) * (inv : ZMod N) = 1) :
    UnitPhase (ZMod N) :=
  ⟨(a : ZMod N) ^ 3, (inv : ZMod N), h⟩

theorem cubic_braid_defect (N : Nat) [NeZero N]
    (a inv : Nat) (h : ((a : ZMod N) ^ 3) * (inv : ZMod N) = 1) :
    (mirroredBraid (cubicPhase N a inv h)).1.x0 -
      (mirroredBraid (cubicPhase N a inv h)).2.x0 =
      1 - (a : ZMod N) ^ 3 := by
  exact mirrored_defect (cubicPhase N a inv h)

/-- A source with one punctum, two copies of one arithmetic fibre, and one
    mirrored signed Artin crossing. The carrier is *observed*, not stipulated. -/
def canonicalWhorl (N : Nat) [NeZero N]
    (stitch : Punctum) (phase : UnitPhase (ZMod N)) : Whorl N where
  stitch := stitch
  shape := .horn
  sourceReading := canonical (ZMod N)
  deformation := Equiv.refl _
  liveBraid := [mirroredStep phase]
  retainedInformation := Set.univ
  filtrationCut := ⟨0, by decide⟩

/-- The same Whorl object's observable defect equals the Burau cubic defect. -/
theorem canonicalWhorl_defect (N : Nat) [NeZero N]
    (stitch : Punctum) (phase : UnitPhase (ZMod N)) :
    (canonicalWhorl N stitch phase).crossDefect = 1 - phase.t := by
  change (mirroredBraid phase).1.x0 -
    (mirroredBraid phase).2.x0 = 1 - phase.t
  exact mirrored_defect phase

/-- The interior is changed by the signed crossing, independently of phase. -/
theorem mirrored_interior_changed {R : Type*}
    [CommRing R] [Nontrivial R] (phase : UnitPhase R) :
    (mirroredBraid phase).1 ≠ canonical R := by
  intro heq
  have h := congrArg (fun v : Strand4 R => v.x1) heq
  change (1 : R) = 0 at h
  exact one_ne_zero h

/-- The exterior is changed by the inverse crossing, independently of phase. -/
theorem mirrored_exterior_changed {R : Type*}
    [CommRing R] [Nontrivial R] (phase : UnitPhase R) :
    (mirroredBraid phase).2 ≠ canonical R := by
  intro heq
  have h := congrArg (fun v : Strand4 R => v.x0) heq
  change (0 : R) = 1 at h
  exact one_ne_zero h.symm

/-- When the unit phase is not 1, the two tethered braid images differ. -/
theorem mirrored_frames_distinct {R : Type*} [CommRing R]
    (phase : UnitPhase R) (ht : phase.t ≠ 1) :
    (mirroredBraid phase).1 ≠ (mirroredBraid phase).2 := by
  intro heq
  have h := congrArg (fun v : Strand4 R => v.x0) heq
  obtain ⟨hp, hq⟩ := mirrored_first_coordinates phase
  have h' : 1 - phase.t = 0 := by simpa [hp, hq] using h
  have ht' : phase.t = 1 := by
    calc
      phase.t = 1 - (1 - phase.t) := by ring
      _ = 1 := by rw [h']; ring
  exact ht ht'

/-- The actual signed crossing produces the full native operative carrier
    precisely by making interior, exterior, and cross relations nontrivial. -/
theorem canonicalWhorl_full {N : Nat} [NeZero N]
    [Nontrivial (ZMod N)] (stitch : Punctum)
    (phase : UnitPhase (ZMod N)) (ht : phase.t ≠ 1) :
    (canonicalWhorl N stitch phase).operativeCarrier =
      Lean.Sixteen3.ofMask 15 := by
  apply Whorl.full_carrier_of_relations
  · simpa [canonicalWhorl, Whorl.transformed, Whorl.copied]
      using mirrored_interior_changed phase
  · simpa [canonicalWhorl, Whorl.transformed, Whorl.copied]
      using mirrored_exterior_changed phase
  · simpa [canonicalWhorl, Whorl.transformed, Whorl.copied]
      using mirrored_frames_distinct phase ht

/-- Source 299, punctum 9: 9³ is a modular unit with inverse 105. -/
instance : Fact (1 < 299) := ⟨by decide⟩
instance : Fact (1 < 5917) := ⟨by decide⟩

def phase299 : UnitPhase (ZMod 299) :=
  cubicPhase 299 9 105 (by decide)

/-- Source 5917, punctum 13: 13³ is a modular unit with inverse 2502. -/
def phase5917 : UnitPhase (ZMod 5917) :=
  cubicPhase 5917 13 2502 (by decide)

/-- The horn-collision numerical defect 169 is the same cubic cross-defect. -/
theorem source299_braid_defect :
    ((mirroredBraid phase299).1.x0 - (mirroredBraid phase299).2.x0).val = 169 := by
  rw [mirrored_defect]
  decide

/-- The braid-trace numerical defect 3721 is the same cubic cross-defect. -/
theorem source5917_braid_defect :
    ((mirroredBraid phase5917).1.x0 - (mirroredBraid phase5917).2.x0).val = 3721 := by
  rw [mirrored_defect]
  decide

/-- These are *exact factor extraction theorems* from braid-derived defects. -/
theorem source299_braid_finds_13 :
    Nat.gcd 299
      ((mirroredBraid phase299).1.x0 - (mirroredBraid phase299).2.x0).val = 13 := by
  rw [source299_braid_defect]
  decide

theorem source5917_braid_finds_61 :
    Nat.gcd 5917
      ((mirroredBraid phase5917).1.x0 - (mirroredBraid phase5917).2.x0).val = 61 := by
  rw [source5917_braid_defect]
  decide

/-- The two braid-generated extracted values are certified proper divisors. -/
theorem source299_proper : 1 < 13 ∧ 13 < 299 ∧ 13 ∣ 299 := by decide

theorem source5917_proper : 1 < 61 ∧ 61 < 5917 ∧ 61 ∣ 5917 := by decide


/-! ## Whole-construction source examples: braid, glut, carrier, recovery, divisor -/

def source299 : Whorl 299 :=
  canonicalWhorl 299 ⟨9, 0, 0⟩ phase299

def source5917 : Whorl 5917 :=
  canonicalWhorl 5917 ⟨13, 0, 0⟩ phase5917

theorem source299_full_carrier :
    source299.operativeCarrier = Lean.Sixteen3.ofMask 15 := by
  exact canonicalWhorl_full (N := 299) ⟨9, 0, 0⟩ phase299 (by decide)

theorem source5917_full_carrier :
    source5917.operativeCarrier = Lean.Sixteen3.ofMask 15 := by
  exact canonicalWhorl_full (N := 5917) ⟨13, 0, 0⟩ phase5917 (by decide)

theorem source299_cross_is_mirrored :
    source299.crossDefect =
      (mirroredBraid phase299).1.x0 - (mirroredBraid phase299).2.x0 := by
  calc
    source299.crossDefect = 1 - phase299.t :=
      canonicalWhorl_defect 299 ⟨9, 0, 0⟩ phase299
    _ = _ := (mirrored_defect phase299).symm

theorem source5917_cross_is_mirrored :
    source5917.crossDefect =
      (mirroredBraid phase5917).1.x0 - (mirroredBraid phase5917).2.x0 := by
  calc
    source5917.crossDefect = 1 - phase5917.t :=
      canonicalWhorl_defect 5917 ⟨13, 0, 0⟩ phase5917
    _ = _ := (mirrored_defect phase5917).symm

theorem source299_full_theorem :
    isGlut source299.retainedInformation ∧
    source299.reconstruct = source299.copied ∧
    source299.operativeCarrier = Lean.Sixteen3.ofMask 15 ∧
    source299.crossDefect.val = 169 ∧
    Nat.gcd 299 source299.crossDefect.val = 13 ∧
    1 < 13 ∧ 13 < 299 ∧ 13 ∣ 299 := by
  refine ⟨?_, source299.reconstruction, source299_full_carrier, ?_, ?_,
          source299_proper.1, source299_proper.2.1,
          source299_proper.2.2⟩
  · simp [isGlut, truthSupported, falsitySupported, source299, canonicalWhorl]
  · rw [source299_cross_is_mirrored]
    exact source299_braid_defect
  · rw [source299_cross_is_mirrored]
    exact source299_braid_finds_13

theorem source5917_full_theorem :
    isGlut source5917.retainedInformation ∧
    source5917.reconstruct = source5917.copied ∧
    source5917.operativeCarrier = Lean.Sixteen3.ofMask 15 ∧
    source5917.crossDefect.val = 3721 ∧
    Nat.gcd 5917 source5917.crossDefect.val = 61 ∧
    1 < 61 ∧ 61 < 5917 ∧ 61 ∣ 5917 := by
  refine ⟨?_, source5917.reconstruction, source5917_full_carrier, ?_, ?_,
          source5917_proper.1, source5917_proper.2.1,
          source5917_proper.2.2⟩
  · simp [isGlut, truthSupported, falsitySupported, source5917, canonicalWhorl]
  · rw [source5917_cross_is_mirrored]
    exact source5917_braid_defect
  · rw [source5917_cross_is_mirrored]
    exact source5917_braid_finds_61

end Imscribing.PrimeWhorl.Theory
