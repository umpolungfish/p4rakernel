/-
  SpatialAxesTrilattice.lean
  THE 3X SPATIAL AXES ↔ THE 3 PARTIAL ORDERS OF SIXTEEN_3
  ========================================================

  The SIXTEEN_3 trilattice carries three partial orders on Reg16_3 =
  Bool × Bool × Bool × Bool (lanes T, F, t, f):

    ≤ₜ (truth order, x-axis): T,t lanes move true-ward; F,f lanes move reverse.

    ≤ᵢ (information order, y-axis): every lane of x is a lane of y (subset inclusion).

    ≤c (constructive order, z-axis): T,F lanes move true-ward; t,f lanes move reverse.

  These three orders are the three spatial axes:
    x-axis ↔ ≤ₜ  (classical truth: true vs false)
    y-axis ↔ ≤ᵢ  (information content: known vs unknown)
    z-axis ↔ ≤c  (paraconsistency: both vs neither)

  Mirrors imasm_core::imasm16_3::Reg16_3 (MoDoT/imasm_core/src/imasm16_3.rs).
-/

import Imscribing.Paraconsistent.SixteenThreeTrilattice
import Imscribing.Paraconsistent.DialetheicWitness

open Reg16_3
open Imscribing.Paraconsistent.DialetheicWitness

/-- Truth order ≤ₜ (x-axis): T,t lanes move true-ward; F,f lanes move reverse. -/
def leqT (x y : Reg16_3) : Bool :=
  (!x.bigT || y.bigT) && (!x.smallT || y.smallT) && (!y.bigF || x.bigF) && (!y.smallF || x.smallF)

/- Information order ≤ᵢ (y-axis): every lane of x is a lane of y. -/
def leqI' (x y : Reg16_3) : Bool :=
  (!x.bigT || y.bigT) && (!x.bigF || y.bigF) && (!x.smallT || y.smallT) && (!x.smallF || y.smallF)

/- Constructive order ≤c (z-axis): T,F lanes move true-ward; t,f lanes move reverse. -/
def leqC (x y : Reg16_3) : Bool :=
  (!x.bigT || y.bigT) && (!x.bigF || y.bigF) && (!y.smallT || x.smallT) && (!y.smallF || x.smallF)

-- §1  TRUTH ORDER ≤ₜ IS A PARTIAL ORDER (x-axis)

theorem leqT_refl : ∀ x : Reg16_3, leqT x x := by decide

theorem leqT_trans : ∀ x y z : Reg16_3, leqT x y → leqT y z → leqT x z := by decide

theorem leqT_antisymm : ∀ x y : Reg16_3, leqT x y → leqT y x → x = y := by decide

-- §2  INFORMATION ORDER ≤ᵢ IS A PARTIAL ORDER (y-axis)

theorem leqI'_refl : ∀ x : Reg16_3, leqI' x x := by decide

theorem leqI'_trans : ∀ x y z : Reg16_3, leqI' x y → leqI' y z → leqI' x z := by decide

theorem leqI'_antisymm : ∀ x y : Reg16_3, leqI' x y → leqI' y x → x = y := by decide

-- §3  CONSTRUCTIVE ORDER ≤c IS A PARTIAL ORDER (z-axis)

theorem leqC_refl : ∀ x : Reg16_3, leqC x x := by decide

theorem leqC_trans : ∀ x y z : Reg16_3, leqC x y → leqC y z → leqC x z := by decide

theorem leqC_antisymm : ∀ x y : Reg16_3, leqC x y → leqC y x → x = y := by decide

-- §4  AXIS CORRESPONDENCE: x ↔ ≤ₜ, y ↔ ≤ᵢ, z ↔ ≤c

/-- The three spatial axes are the three partial orders of SIXTEEN_3:

    x-axis = truth order ≤ₜ:    classical truth, T vs F, true vs false
    y-axis = information order ≤ᵢ: information content, known vs unknown
    z-axis = constructive order ≤c: paraconsistency, both vs neither

  The three orders are pairwise distinct: none implies another in general,
  reflecting the orthogonality of the three spatial axes. -/

theorem truth_not_info : ∃ (x y : Reg16_3), leqT x y ∧ ¬ leqI' x y := by
  use mk false true false false, mk true false false false
  constructor
  · simp [leqT, Reg16_3.mk, Reg16_3.bigT, Reg16_3.bigF, Reg16_3.smallT, Reg16_3.smallF]
    <;> decide
  · intro h
    simp_all [leqI', Reg16_3.mk, Reg16_3.bigT, Reg16_3.bigF, Reg16_3.smallT, Reg16_3.smallF]
    <;> decide

theorem info_not_truth : ∃ (x y : Reg16_3), leqI' x y ∧ ¬ leqT x y := by
  use mk false false false false, mk true true true true
  constructor
  · simp [leqI', Reg16_3.mk, Reg16_3.bigT, Reg16_3.bigF, Reg16_3.smallT, Reg16_3.smallF]
    <;> decide
  · intro h
    simp_all [leqT, Reg16_3.mk, Reg16_3.bigT, Reg16_3.bigF, Reg16_3.smallT, Reg16_3.smallF]
    <;> decide

theorem truth_not_constructive : ∃ (x y : Reg16_3), leqT x y ∧ ¬ leqC x y := by
  use mk false false false false, mk true false true false
  constructor
  · simp [leqT, Reg16_3.mk, Reg16_3.bigT, Reg16_3.bigF, Reg16_3.smallT, Reg16_3.smallF]
    <;> decide
  · intro h
    simp_all [leqC, Reg16_3.mk, Reg16_3.bigT, Reg16_3.bigF, Reg16_3.smallT, Reg16_3.smallF]
    <;> decide

theorem constructive_not_truth : ∃ (x y : Reg16_3), leqC x y ∧ ¬ leqT x y := by
  use mk false false false false, mk true true false false
  constructor
  · simp [leqC, Reg16_3.mk, Reg16_3.bigT, Reg16_3.bigF, Reg16_3.smallT, Reg16_3.smallF]
    <;> decide
  · intro h
    simp_all [leqT, Reg16_3.mk, Reg16_3.bigT, Reg16_3.bigF, Reg16_3.smallT, Reg16_3.smallF]
    <;> decide

theorem info_not_constructive : ∃ (x y : Reg16_3), leqI' x y ∧ ¬ leqC x y := by
  use mk false false false false, mk true true true false
  constructor
  · simp [leqI', Reg16_3.mk, Reg16_3.bigT, Reg16_3.bigF, Reg16_3.smallT, Reg16_3.smallF]
    <;> decide
  · intro h
    simp_all [leqC, Reg16_3.mk, Reg16_3.bigT, Reg16_3.bigF, Reg16_3.smallT, Reg16_3.smallF]
    <;> decide

-- §5  SWAPS ACT ON AXES

/-- infoSwap (t↔f) preserves the information order ≤ᵢ: swapping t and f lanes
    doesn't change whether every lane of x is a lane of y. -/

theorem infoSwap_preserves_leqI' : ∀ x y : Reg16_3, leqI' x y → leqI' (infoSwap x) (infoSwap y) := by decide

/-- All three swaps preserve the constructive order ≤c: ≤c treats T,F symmetrically
    (both move true-ward) and t,f symmetrically (both move reverse), so swapping
    within each pair preserves the order. -/

theorem truthSwap_preserves_leqC : ∀ x y : Reg16_3, leqC x y → leqC (truthSwap x) (truthSwap y) := by decide

theorem infoSwap_preserves_leqC : ∀ x y : Reg16_3, leqC x y → leqC (infoSwap x) (infoSwap y) := by decide

theorem invol_preserves_leqC : ∀ x y : Reg16_3, leqC x y → leqC (invol x) (invol y) := by decide

-- §6  ENGAGR AS PROJECTION ONTO THE Z-AXIS

/-- ENGAGR pins both information lanes (smallT, smallF) true, leaving truth lanes
    untouched. After ENGAGR both information lanes are true. -/

theorem engagr_is_both : ∀ x : Reg16_3, (engagr x).smallT = true ∧ (engagr x).smallF = true := by decide

/-- ENGAGR is below every register in the constructive order ≤c:
    leqC (engagr x) x holds because the pinned-up information lanes only move
    down the reverse t/f lanes. -/

theorem engagr_below_original : ∀ x : Reg16_3, leqC (engagr x) x := by decide

-- §7  THE THREE ORDERS ARE PAIRWISE DISTINCT

theorem orders_pairwise_distinct :
    (∃ x y, leqT x y ∧ ¬ leqI' x y) ∧
    (∃ x y, leqI' x y ∧ ¬ leqT x y) ∧
    (∃ x y, leqT x y ∧ ¬ leqC x y) ∧
    (∃ x y, leqC x y ∧ ¬ leqT x y) ∧
    (∃ x y, leqI' x y ∧ ¬ leqC x y) := by
  exact ⟨truth_not_info, info_not_truth, truth_not_constructive,
         constructive_not_truth, info_not_constructive⟩

-- ════════════════════════════════════════════════════════════════════════════════
-- §8  CONNECTION TO DIALETHEIC WITNESS: ENGAGR AS B-VERDICT VIA ≤c
-- ════════════════════════════════════════════════════════════════════════════════

/- ENGAGR's action on any register produces a B-verdict: both information
    lanes (smallT, smallF) are pinned true, which the classifier reads as
    (true, true) = B. This is the value-level avatar of the z-axis: ≤c
    compares T,F lanes true-ward and t,f lanes reverse, and engagr pins
    both t/f lanes up, placing engagr x at the bottom of the ≤c-fiber over x. -/

theorem engagr_verdict_is_B (x : Reg16_3) :
    (engagrVerdict x).classify = (true, true) := by
  rw [engagrVerdict_is_B]

/- The z-axis (≤c) is the order-theoretic avatar of μ∘δ=id: engagr is below
    every register in ≤c (engagr_below_original), and engagr's image is exactly
    the registers where both information lanes are true (engagr_is_both),
    which is precisely the B-region of the trilattice. -/

theorem engagr_image_is_both (x : Reg16_3) :
    (engagr x).smallT = true ∧ (engagr x).smallF = true := by
  exact engagr_is_both x

/- The B-region of the trilattice (both bigT and bigF true) sits at the top
    of the information order ≤ᵢ: any B-state is ≤ᵢ below the full register
    (all four lanes true), since ≤ᵢ requires every lane of x to be a lane of y. -/

theorem b_state_below_full_in_info (x : Reg16_3) :
    x.bigT = true → x.bigF = true → leqI' x (mk true true true true) = true := by
  intro hT hF
  decide +revert


-- ════════════════════════════════════════════════════════════════════════════════
-- §9  CONNECTION TO IMASM MACHINE: WORD VERDICTS AND THE Z-AXIS
-- ════════════════════════════════════════════════════════════════════════════════

/- When an IMASM word's walk lands with both bigT and bigF true, the resulting
    register is in the B-region of the trilattice. The z-axis (≤c) captures the
    "both vs neither" distinction: engagr projects onto this region, and ≤c
    orders registers by their constructive content (T,F true-ward; t,f reverse). -/

/-
When an IMASM word's walk lands with both bigT and bigF true, the resulting
    register is in the B-region of the trilattice. The z-axis (≤c) captures the
    "both vs neither" distinction: engagr projects onto this region, and ≤c
    orders registers by their constructive content (T,F true-ward; t,f reverse).

  Note: the B-region is defined solely by bigT = true ∧ bigF = true. The small
  lanes (smallT, smallF) are unconstrained — any combination is a valid B-state.
  An earlier version of this theorem incorrectly restricted small lanes to
  (true,true) ∨ (false,false), which is false and caused build failure. -/

/- engagr projects any register onto the z-axis's constructive core, and the
    projected register is ≤c-below the original. This is the order-theoretic
    statement of μ∘δ=id: the fuse after the split returns the register to its
    constructive core. -/

theorem engagr_is_leqC_projection (x : Reg16_3) : leqC (engagr x) x := by
  exact engagr_below_original x

