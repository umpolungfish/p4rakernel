import Imscribing.Primitives.CLU
import Imscribing.Paraconsistent.CombinatoryDynamics

/-!
P11 strengthening (2026-11-18).
`CLU.kTier` maps energy E to the discrete grade ⌊E / CLU(b)⌋ — the number of
observer-relative units in E. `CombinatoryDynamics.Clock` advances a Nat tick.
Binding: if energy accumulates at CLU(b) per tick (E = n·CLU(b)), the kTier
grade is exactly n. The perceiver's base b therefore sets the clock's grade
granularity. No new axiom; kTier and the floor law are already proved.
-/
namespace Imscribing.CLUClockGranularity

open Imscribing.Primitives.CLUPrimitives
open Imscribing.Paraconsistent
open Imscribing.Paraconsistent.CombinatoryDynamics
open Imscribing.Paraconsistent.CombinatoryReentry
open Imscribing.Primitives
local infixl:70 " @@ " => Term.app

/-- Energy of exactly n CLU units maps to grade n. This is the clock's tick
    granularity: one CLU(b) of energy per grade step. -/
theorem kTier_of_nat_clu (b : ℝ) (hb_pos : b > 0) (hb_ne_one : b ≠ 1)
    (hb_gt_one : b > 1) (n : Nat) :
    kTier b hb_pos hb_ne_one ((n : ℝ) * CLU_of_base b hb_pos hb_ne_one) = n := by
  unfold kTier
  have hCLUpos : CLU_of_base b hb_pos hb_ne_one > 0 := CLU_of_base_pos_gt_one b hb_gt_one
  have hdiv : (n : ℝ) * CLU_of_base b hb_pos hb_ne_one / CLU_of_base b hb_pos hb_ne_one = (n : ℝ) := by
    field_simp [ne_of_gt hCLUpos]
  rw [hdiv]
  simp

/-- The grade advances strictly with each accumulated CLU unit. -/
theorem kTier_step (b : ℝ) (hb_pos : b > 0) (hb_ne_one : b ≠ 1)
    (hb_gt_one : b > 1) (n : Nat) :
    kTier b hb_pos hb_ne_one ((n : ℝ) * CLU_of_base b hb_pos hb_ne_one) <
      kTier b hb_pos hb_ne_one (((n + 1 : Nat) : ℝ) * CLU_of_base b hb_pos hb_ne_one) := by
  rw [kTier_of_nat_clu b hb_pos hb_ne_one hb_gt_one n,
      kTier_of_nat_clu b hb_pos hb_ne_one hb_gt_one (n + 1)]
  exact Nat.lt_succ_self n

/-- The Clock relays the grade to a native state: reading at tick = grade n
    gives the native state at that grade. Tick n is the grade of energy n·CLU(b). -/
theorem clock_read_at_clu_grade {program : Term} {seed : Lean.Sixteen3}
    (clock : Clock program seed) (b : ℝ) (hb_pos : b > 0) (hb_ne_one : b ≠ 1)
    (hb_gt_one : b > 1) (n : Nat) :
    clock.read (kTier b hb_pos hb_ne_one ((n : ℝ) * CLU_of_base b hb_pos hb_ne_one)) =
      clock.read n := by
  rw [kTier_of_nat_clu b hb_pos hb_ne_one hb_gt_one n]

/-- One CLU of energy corresponds to one program step at that grade: the clock's
    program_tick composed with the CLU grade bind. -/
theorem clu_grade_program_tick {program : Term} {seed : Lean.Sixteen3}
    (clock : Clock program seed) (b : ℝ) (hb_pos : b > 0) (hb_ne_one : b ≠ 1)
    (hb_gt_one : b > 1) (n : Nat) :
    Steps (program @@ .datum (clock.read (kTier b hb_pos hb_ne_one
              ((n : ℝ) * CLU_of_base b hb_pos hb_ne_one))))
      (.datum (clock.read (kTier b hb_pos hb_ne_one
              (((n + 1 : Nat) : ℝ) * CLU_of_base b hb_pos hb_ne_one)))) := by
  rw [kTier_of_nat_clu b hb_pos hb_ne_one hb_gt_one n,
      kTier_of_nat_clu b hb_pos hb_ne_one hb_gt_one (n + 1)]
  exact clock.program_tick n

/-- The decimal observer: tick n is the grade of n·ln(10) nats. -/
theorem kTier10_of_nat_clu (n : Nat) :
    kTier10 ((n : ℝ) * Real.log 10) = n := by
  exact kTier_of_nat_clu 10 (by norm_num) (by norm_num) (by norm_num) n

end Imscribing.CLUClockGranularity
