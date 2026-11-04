import Mathlib
import Init.Paraconsistent

/-!
# Prime Whorl: marked-source, tethered braid transport

Designed for umpolungfish/p4rakernel (branch `p4rakernel`).  The carrier is
**the fork's own** `Lean.Sixteen3`, not a replacement four-valued type.

This module proves the invertible *transport/reconstruction specification*.
A `SignedCrossing` carries an explicit equivalence; the general construction
is **not** a proof of the Artin braid relations or of a faithful Burau action.
The geometric mark is single and remains the same through copy, deformation,
and transport; interior/exterior are roles, not asserted prime factors.
-/

namespace Imscribing.PrimeWhorl

open Lean

/-- Three geometry phases; a single marked point is retained in each phase. -/
inductive Geometry where
  | contractedSphere
  | horn
  | ring
  deriving Repr, DecidableEq

/-- One punctum. Both arithmetic readings use this *same* spatial site. -/
structure Punctum where
  address : Nat
  thetaQ : Nat
  phiQ : Nat
  deriving Repr, DecidableEq

/-- A signed Artin-letter *label*. Its interpretation is provided separately. -/
structure Letter where
  index : Fin 3
  positive : Bool
  deriving Repr, DecidableEq

/-- An explicitly invertible meaning for a signed letter on the two banks.
    Relations between such meanings (including Artin relations) are additional
    obligations, not implicit in the presence of the letter label. -/
structure SignedCrossing (R : Type*) where
  label : Letter
  action : (R × R) ≃ (R × R)

/-- A finite, ordered composition of retained crossing actions. -/
def wordAction {R : Type*} : List (SignedCrossing R) → (R × R) ≃ (R × R)
  | [] => Equiv.refl _
  | c :: cs => c.action.trans (wordAction cs)

/-- A single-source configuration with *one* geometric punctum, two readings,
    one shared diagnostic carrier, and retained executable action history. -/
structure StitchedState (R : Type*) where
  source : Nat
  punctum : Punctum
  geometry : Geometry
  interior : R
  exterior : R
  carrier : Sixteen3
  history : List (SignedCrossing R)

/-- Initial copy: two coincident readings of the same source value, with one
    punctum field, not two independently chosen points. -/
def copySource {R : Type*} (N : Nat) (site : Punctum) (x : R) :
    StitchedState R where
  source := N
  punctum := site
  geometry := .contractedSphere
  interior := x
  exterior := x
  carrier := Sixteen3.ofMask 1
  history := []

/-- Pure expansion does not replace the source or create a second punctum. -/
def expandHorn {R : Type*} (s : StitchedState R) : StitchedState R :=
  { s with geometry := .horn }

/-- The horn can be further realized as a ring without repinning. -/
def expandRing {R : Type*} (s : StitchedState R) : StitchedState R :=
  { s with geometry := .ring }

/-- An asymmetric, possibly lossy deformation. Only source/mark retention is
    automatic; recovering both banks requires an invertibility certificate. -/
def deform {R : Type*} (f g : R → R) (s : StitchedState R) :
    StitchedState R :=
  { s with interior := f s.interior, exterior := g s.exterior }

/-- The two bank values constitute the paired arithmetic realization. -/
def banks {R : Type*} (s : StitchedState R) : R × R :=
  (s.interior, s.exterior)

/-- Apply an *ordered* word to the existing banks; do not restart the sphere. -/
def applyWord {R : Type*} (s : StitchedState R)
    (w : List (SignedCrossing R)) : StitchedState R :=
  let xy := wordAction w (banks s)
  { s with interior := xy.1, exterior := xy.2,
           history := s.history ++ w }

/-- Driver observations are accumulated by the fork's native information join.
    This is not a divisor certificate and does not force a carrier atom. -/
def recordSupport {R : Type*} (s : StitchedState R)
    (observed : Sixteen3) : StitchedState R :=
  { s with carrier := Sixteen3.join_i s.carrier observed }

/-- Source identity and the one geometric mark are not changed by transport. -/
theorem applyWord_retains_source {R : Type*} (s : StitchedState R)
    (w : List (SignedCrossing R)) : (applyWord s w).source = s.source := rfl

theorem applyWord_retains_punctum {R : Type*} (s : StitchedState R)
    (w : List (SignedCrossing R)) : (applyWord s w).punctum = s.punctum := rfl

theorem applyWord_retains_geometry {R : Type*} (s : StitchedState R)
    (w : List (SignedCrossing R)) : (applyWord s w).geometry = s.geometry := rfl

theorem expandHorn_retains_punctum {R : Type*} (s : StitchedState R) :
    (expandHorn s).punctum = s.punctum := rfl

theorem expandRing_retains_punctum {R : Type*} (s : StitchedState R) :
    (expandRing s).punctum = s.punctum := rfl

theorem deform_retains_source {R : Type*} (f g : R → R)
    (s : StitchedState R) : (deform f g s).source = s.source := rfl

theorem deform_retains_punctum {R : Type*} (f g : R → R)
    (s : StitchedState R) : (deform f g s).punctum = s.punctum := rfl

theorem support_retains_punctum {R : Type*} (s : StitchedState R)
    (a : Sixteen3) : (recordSupport s a).punctum = s.punctum := rfl

/-- Every individual word has a genuinely defined inverse on both banks. -/
theorem word_reconstruction {R : Type*} (s : StitchedState R)
    (w : List (SignedCrossing R)) :
    (wordAction w).symm (banks (applyWord s w)) = banks s := by
  change (wordAction w).symm ((wordAction w) (banks s)) = banks s
  exact (wordAction w).symm_apply_apply (banks s)

/-- The retained full action history is stronger than a bare word of labels. -/
def reconstructBanks {R : Type*} (s : StitchedState R) : R × R :=
  (wordAction s.history).symm (banks s)

/-- Initial copies reconstruct without reading the stored source as a shortcut:
    the inverse word is applied to the *transformed bank values*. -/
theorem reconstruct_from_first_word {R : Type*}
    (N : Nat) (site : Punctum) (x : R) (w : List (SignedCrossing R)) :
    reconstructBanks (applyWord (copySource N site x) w) = (x, x) := by
  change (wordAction w).symm ((wordAction w) (x, x)) = (x, x)
  exact (wordAction w).symm_apply_apply (x, x)

/-- A concrete nonidentity, reversible two-bank *toy action*.
    This is a shear, not a claimed representation of B₄. -/
def shear {R : Type*} [AddCommGroup R] : (R × R) ≃ (R × R) where
  toFun xy := (xy.1, xy.2 + xy.1)
  invFun xy := (xy.1, xy.2 - xy.1)
  left_inv := by
    intro ⟨p, q⟩
    simp
  right_inv := by
    intro ⟨p, q⟩
    simp

example : (shear (R := ℤ)) (1, 0) = (1, 1) := by
  norm_num [shear]

example : (shear (R := ℤ)).symm ((shear (R := ℤ)) (1, 0)) = (1, 0) := by
  exact (shear (R := ℤ)).symm_apply_apply (1, 0)

/-- Invertible deform-then-braid still reconstructs the complete paired reading.
    The statement *requires* both actions to be equivalences; it does not
    assert arbitrary geometric collapse is invertible. -/
theorem reconstruction_after_deformation {R : Type*}
    (D B : (R × R) ≃ (R × R)) (x : R × R) :
    D.symm (B.symm (B (D x))) = x := by
  simp

end Imscribing.PrimeWhorl
