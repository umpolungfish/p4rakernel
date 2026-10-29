import Imscribing.Paraconsistent.CombinatoryFixedPoint

/-!
Programs for all three native lattice orders. Seeded operations have explicit
least information fixed points, and S/K composition preserves reduction
evidence. Injection and retention give two distinct order-sensitive programs.
-/

namespace Imscribing.Paraconsistent.TrilatticePrograms

open CombinatoryReentry
local infixl:70 " @@ " => Term.app

theorem lattice_idempotent (op : LatticeOp) (x : Lean.Sixteen3) :
    op.apply x x = x := by
  rcases x with ⟨n, t, f, b⟩
  cases op <;> cases n <;> cases t <;> cases f <;> cases b <;> decide

/-- Apply a native operation with a retained first operand. -/
def withSeed (op : LatticeOp) (seed : Lean.Sixteen3) : Term :=
  .lattice op @@ .datum seed

theorem withSeed_apply (op : LatticeOp) (seed x : Lean.Sixteen3) :
    Steps (withSeed op seed @@ .datum x) (.datum (op.apply seed x)) :=
  lattice_apply op seed x

/-- Every seeded join or meet settles from information bottom in one tick. -/
def seedPoint (op : LatticeOp) (seed : Lean.Sixteen3) : Lean.Sixteen3 :=
  op.apply seed Lean.Sixteen3.none

theorem seedPoint_fixed (op : LatticeOp) (seed : Lean.Sixteen3) :
    op.apply seed (seedPoint op seed) = seedPoint op seed := by
  rcases seed with ⟨n, t, f, b⟩
  cases op <;> cases n <;> cases t <;> cases f <;> cases b <;> decide

theorem seedPoint_least (op : LatticeOp) (seed x : Lean.Sixteen3) :
    op.apply seed x = x → Lean.Sixteen3.le_i (seedPoint op seed) x = true := by
  rcases seed with ⟨n, t, f, b⟩
  rcases x with ⟨xn, xt, xf, xb⟩
  cases op <;> cases n <;> cases t <;> cases f <;> cases b <;>
    cases xn <;> cases xt <;> cases xf <;> cases xb <;> decide

/-- The same seeded operation descends from information top in one tick. -/
def seedCeiling (op : LatticeOp) (seed : Lean.Sixteen3) : Lean.Sixteen3 :=
  op.apply seed Lean.Sixteen3.all

theorem seedCeiling_fixed (op : LatticeOp) (seed : Lean.Sixteen3) :
    op.apply seed (seedCeiling op seed) = seedCeiling op seed := by
  rcases seed with ⟨n, t, f, b⟩
  cases op <;> cases n <;> cases t <;> cases f <;> cases b <;> decide

theorem seedCeiling_greatest (op : LatticeOp) (seed x : Lean.Sixteen3) :
    op.apply seed x = x → Lean.Sixteen3.le_i x (seedCeiling op seed) = true := by
  rcases seed with ⟨n, t, f, b⟩
  rcases x with ⟨xn, xt, xf, xb⟩
  cases op <;> cases n <;> cases t <;> cases f <;> cases b <;>
    cases xn <;> cases xt <;> cases xf <;> cases xb <;> decide

/-- Duplicate a state across the two arguments of a native lattice operation. -/
def diagonal (op : LatticeOp) : Term := .s @@ .lattice op @@ .i

theorem diagonal_apply (op : LatticeOp) (x : Lean.Sixteen3) :
    Steps (diagonal op @@ .datum x) (.datum x) := by
  have h : Steps (diagonal op @@ .datum x) (.datum (op.apply x x)) :=
    .cons (.substitution (.lattice op) .i (.datum x))
      (.cons (.right (.lattice op @@ .datum x) (.identity (.datum x)))
        (.cons (.lattice op x x) (.refl _)))
  rw [lattice_idempotent] at h
  exact h

def inject (seed : Lean.Sixteen3) : Term := withSeed .joinInformation seed
def retain (frame : Lean.Sixteen3) : Term := withSeed .meetInformation frame

/-- Retain the part of a seeded result lying in the chosen information frame. -/
def retainAfterInject (frame seed : Lean.Sixteen3) : Term :=
  after (retain frame) (inject seed)

/-- Inject evidence after the frame has retained its portion of the input. -/
def injectAfterRetain (frame seed : Lean.Sixteen3) : Term :=
  after (inject seed) (retain frame)

theorem retainAfterInject_apply (frame seed x : Lean.Sixteen3) :
    Steps (retainAfterInject frame seed @@ .datum x)
      (.datum (Lean.Sixteen3.meet_i frame (Lean.Sixteen3.join_i seed x))) :=
  after_apply _ _ x _ _ (withSeed_apply .joinInformation seed x)
    (withSeed_apply .meetInformation frame _)

theorem injectAfterRetain_apply (frame seed x : Lean.Sixteen3) :
    Steps (injectAfterRetain frame seed @@ .datum x)
      (.datum (Lean.Sixteen3.join_i seed (Lean.Sixteen3.meet_i frame x))) :=
  after_apply _ _ x _ _ (withSeed_apply .meetInformation frame x)
    (withSeed_apply .joinInformation seed _)

end Imscribing.Paraconsistent.TrilatticePrograms
