import Mathlib
import Imscribing.PrimeWhorlCore

/-!
# Four-strand unreduced Burau braids

This is the unreduced Burau two-coordinate block:

  positive: [[1-t,t],[1,0]]
  inverse:  [[0,1],[t⁻¹,1-t⁻¹]].

The same unit parameter is used for every letter when proving the Artin relations.
The independent per-letter, per-channel live-phase interpretation is in
`PrimeWhorlLiveBraid.lean`; it is *not* asserted to obey the constant-parameter
braid relations. The four coordinates are braid strands, not puncture sites.
-/

namespace Imscribing.PrimeWhorl
namespace Burau

variable {R : Type*} [CommRing R]

/-- A phase and an explicitly certified inverse. For `ZMod N`, a phase is
    admissible exactly when it is a unit; the nonunit-phase obstruction checks
    `gcd(t,N)=1` and otherwise records the GCD witness instead of inverting. -/
structure UnitPhase (R : Type*) [CommRing R] where
  t : R
  tinv : R
  mul_inv : t * tinv = 1

theorem UnitPhase.inv_mul (phase : UnitPhase R) :
    phase.tinv * phase.t = 1 := by
  calc
    phase.tinv * phase.t = phase.t * phase.tinv := mul_comm _ _
    _ = 1 := phase.mul_inv

/-- Ordered coordinate pair: one positive Artin generator acts here. -/
def pairForward (phase : UnitPhase R) (xy : R × R) : R × R :=
  ((1 - phase.t) * xy.1 + phase.t * xy.2, xy.1)

/-- Exact negative generator, with the *same* saved phase. -/
def pairBackward (phase : UnitPhase R) (xy : R × R) : R × R :=
  (xy.2, phase.tinv * xy.1 + (1 - phase.tinv) * xy.2)

theorem pair_left_inverse (phase : UnitPhase R) (xy : R × R) :
    pairBackward phase (pairForward phase xy) = xy := by
  rcases xy with ⟨a, b⟩
  apply Prod.ext
  · rfl
  · change phase.tinv * ((1 - phase.t) * a + phase.t * b) +
        (1 - phase.tinv) * a = b
    calc
      _ = (1 - phase.tinv * phase.t) * a +
          (phase.tinv * phase.t) * b := by ring
      _ = b := by rw [phase.inv_mul]; ring

theorem pair_right_inverse (phase : UnitPhase R) (xy : R × R) :
    pairForward phase (pairBackward phase xy) = xy := by
  rcases xy with ⟨a, b⟩
  apply Prod.ext
  · change (1 - phase.t) * b +
      phase.t * (phase.tinv * a + (1 - phase.tinv) * b) = a
    calc
      _ = (phase.t * phase.tinv) * a +
          (1 - phase.t * phase.tinv) * b := by ring
      _ = a := by rw [phase.mul_inv]; ring
  · rfl

/-- The two-strand Burau block as a genuine equivalence. -/
def pairEquiv (phase : UnitPhase R) : (R × R) ≃ (R × R) where
  toFun := pairForward phase
  invFun := pairBackward phase
  left_inv := pair_left_inverse phase
  right_inv := pair_right_inverse phase

/-- Four strands; no geometric puncture is added by this four-dimensional
    *arithmetic* braid fibre. The marked sphere point lives in `StitchedState`. -/
@[ext] structure Strand4 (R : Type*) where
  x0 : R
  x1 : R
  x2 : R
  x3 : R
  deriving Repr

/-- Reorder coordinates so that the crossing pair occupies the first slot. -/
def pack01 : Strand4 R ≃ ((R × R) × (R × R)) where
  toFun v := ((v.x0, v.x1), (v.x2, v.x3))
  invFun v := ⟨v.1.1, v.1.2, v.2.1, v.2.2⟩
  left_inv := by intro ⟨a, b, c, d⟩; rfl
  right_inv := by intro ⟨⟨a, b⟩, ⟨c, d⟩⟩; rfl

def pack12 : Strand4 R ≃ ((R × R) × (R × R)) where
  toFun v := ((v.x1, v.x2), (v.x0, v.x3))
  invFun v := ⟨v.2.1, v.1.1, v.1.2, v.2.2⟩
  left_inv := by intro ⟨a, b, c, d⟩; rfl
  right_inv := by intro ⟨⟨a, b⟩, ⟨c, d⟩⟩; rfl

def pack23 : Strand4 R ≃ ((R × R) × (R × R)) where
  toFun v := ((v.x2, v.x3), (v.x0, v.x1))
  invFun v := ⟨v.2.1, v.2.2, v.1.1, v.1.2⟩
  left_inv := by intro ⟨a, b, c, d⟩; rfl
  right_inv := by intro ⟨⟨a, b⟩, ⟨c, d⟩⟩; rfl

/-- Apply an equivalence to the designated pair, leaving other strands alone. -/
def liftPair (e : (R × R) ≃ (R × R)) :
    ((R × R) × (R × R)) ≃ ((R × R) × (R × R)) where
  toFun v := (e v.1, v.2)
  invFun v := (e.symm v.1, v.2)
  left_inv := by intro ⟨a, b⟩; simp
  right_inv := by intro ⟨a, b⟩; simp

/-- σ₁: braid the first and second strands. -/
def sigma1 (phase : UnitPhase R) : Strand4 R ≃ Strand4 R :=
  (pack01 (R := R)).trans
    ((liftPair (pairEquiv phase)).trans ((pack01 (R := R)).symm))

/-- σ₂: braid the second and third strands. -/
def sigma2 (phase : UnitPhase R) : Strand4 R ≃ Strand4 R :=
  (pack12 (R := R)).trans
    ((liftPair (pairEquiv phase)).trans ((pack12 (R := R)).symm))

/-- σ₃: braid the third and fourth strands. -/
def sigma3 (phase : UnitPhase R) : Strand4 R ≃ Strand4 R :=
  (pack23 (R := R)).trans
    ((liftPair (pairEquiv phase)).trans ((pack23 (R := R)).symm))

@[simp] theorem sigma1_apply (phase : UnitPhase R) (v : Strand4 R) :
    sigma1 phase v =
      ⟨(1 - phase.t) * v.x0 + phase.t * v.x1, v.x0, v.x2, v.x3⟩ := rfl

@[simp] theorem sigma2_apply (phase : UnitPhase R) (v : Strand4 R) :
    sigma2 phase v =
      ⟨v.x0, (1 - phase.t) * v.x1 + phase.t * v.x2, v.x1, v.x3⟩ := rfl

@[simp] theorem sigma3_apply (phase : UnitPhase R) (v : Strand4 R) :
    sigma3 phase v =
      ⟨v.x0, v.x1, (1 - phase.t) * v.x2 + phase.t * v.x3, v.x2⟩ := rfl

/-- Artin relation σ₁σ₂σ₁ = σ₂σ₁σ₂, verified on all four coordinates. -/
theorem braid12 (phase : UnitPhase R) (v : Strand4 R) :
    sigma1 phase (sigma2 phase (sigma1 phase v)) =
    sigma2 phase (sigma1 phase (sigma2 phase v)) := by
  ext <;> simp [sigma1_apply, sigma2_apply] <;> ring

/-- Artin relation σ₂σ₃σ₂ = σ₃σ₂σ₃. -/
theorem braid23 (phase : UnitPhase R) (v : Strand4 R) :
    sigma2 phase (sigma3 phase (sigma2 phase v)) =
    sigma3 phase (sigma2 phase (sigma3 phase v)) := by
  ext <;> simp [sigma2_apply, sigma3_apply] <;> ring

/-- Distant generators commute: σ₁σ₃ = σ₃σ₁. -/
theorem braid13 (phase : UnitPhase R) (v : Strand4 R) :
    sigma1 phase (sigma3 phase v) =
    sigma3 phase (sigma1 phase v) := by
  ext <;> simp [sigma1_apply, sigma3_apply] <;> ring

/-- The Artin relations hold as equalities of invertible operators. -/
theorem artin12_equiv (phase : UnitPhase R) :
    ((sigma1 phase).trans (sigma2 phase)).trans (sigma1 phase) =
    ((sigma2 phase).trans (sigma1 phase)).trans (sigma2 phase) := by
  apply Equiv.ext
  intro v
  exact braid12 phase v

theorem artin23_equiv (phase : UnitPhase R) :
    ((sigma2 phase).trans (sigma3 phase)).trans (sigma2 phase) =
    ((sigma3 phase).trans (sigma2 phase)).trans (sigma3 phase) := by
  apply Equiv.ext
  intro v
  exact braid23 phase v

theorem artin13_equiv (phase : UnitPhase R) :
    (sigma1 phase).trans (sigma3 phase) =
    (sigma3 phase).trans (sigma1 phase) := by
  apply Equiv.ext
  intro v
  exact braid13 phase v

/-- At fixed `t`, the 4×4 matrix action preserves the constant strand vector. -/
def constantStrands (x : R) : Strand4 R := ⟨x,x,x,x⟩

theorem sigma1_constant (phase : UnitPhase R) (x : R) :
    sigma1 phase (constantStrands x) = constantStrands x := by
  ext <;> simp [constantStrands, sigma1_apply] <;> ring

theorem sigma2_constant (phase : UnitPhase R) (x : R) :
    sigma2 phase (constantStrands x) = constantStrands x := by
  ext <;> simp [constantStrands, sigma2_apply] <;> ring

theorem sigma3_constant (phase : UnitPhase R) (x : R) :
    sigma3 phase (constantStrands x) = constantStrands x := by
  ext <;> simp [constantStrands, sigma3_apply] <;> ring

/-- A positive Burau crossing is not the identity on a nontrivial ring.
    This is a **braid action** claim, not a statement about link closure. -/
theorem sigma1_is_nontrivial [Nontrivial R] (phase : UnitPhase R) :
    sigma1 phase (⟨1, 0, 0, 0⟩ : Strand4 R) ≠ ⟨1, 0, 0, 0⟩ := by
  intro h
  have hz : (1 : R) = 0 := by
    simpa [sigma1_apply] using congrArg (fun v : Strand4 R => v.x1) h
  exact one_ne_zero hz

end Burau
end Imscribing.PrimeWhorl
