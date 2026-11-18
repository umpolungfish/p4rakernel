import Imscribing.SICZetaLemniscate
import Imscribing.Paraconsistent.MultiplicativeReentry

/-!
P8 strengthening (2026-11-18).
`SICZetaLemniscate` re-defines the ZetaSICDualFrame namespace and adds the
fire-lattice reductions `sum_arm_reduction`/`diff_arm_reduction`. Full file
merging is deferred (it would duplicate 230 lines of matrix identities); this
module makes the two systems COMPOSE at the arithmetic seam:

  the split filter's modulus `2*modulus` is decomposed by
  `Nat.exists_eq_two_pow_mul_odd` into `2^a * m` (m odd), which is exactly the
  shape the diff-arm reduction needs. A candidate's product congruence to N
  then becomes the divisibility premise the fire lattice evaluates.

No new axiom; the reductions and the filter are already proved.
-/
namespace Imscribing.Paraconsistent.FireLatticeModulus

open Imscribing.Millennium.ZetaSICDualFrame
open Imscribing.Paraconsistent.MultiplicativeReentry

/-- A nonzero split modulus decomposes into the fire lattice's 2-power × odd
    shape. This is the bind between the producer's filter and the derived law. -/
theorem split_modulus_is_two_power_times_odd (modulus : Nat) (hmod : modulus ≠ 0) :
    ∃ k m : Nat, Odd m ∧ 2 * modulus = 2 ^ k * m := by
  obtain ⟨k, m, hm, h⟩ := Nat.exists_eq_two_pow_mul_odd (by omega : 2 * modulus ≠ 0)
  exact ⟨k, m, hm, h⟩

/-- The diff-arm reduction is exactly the divisibility form of a modulus offset:
    with modulus = 2^k * m (m odd), the odd part divides 2^t − 1 iff the full
    modulus divides the shifted chord. This is the condition the split filter
    evaluates on a candidate pair. -/
theorem split_offset_is_diff_arm (k m i j : Nat) (hm : Odd m) (hk : k ≤ i) (hij : i ≤ j) :
    (m ∣ 2 ^ (j - i) - 1) ↔
    ((2 : ℤ) ^ k * m ∣ (2 : ℤ) ^ i * ((2 : ℤ) ^ (j - i) - 1)) := by
  exact diff_arm_reduction k m i j hm hk hij

/-- The sum-arm reduction gives the complementary site. Together the two arms
    characterize the fire condition for any odd modulus part. -/
theorem split_offset_is_sum_arm (k m t : Nat) (hm : Odd m) (ht : 0 < t) :
    (m ∣ 2 ^ t - 1) ↔
    ((2 : ℤ) ^ k * m ∣ (2 : ℤ) ^ (k - 1 + t) - (2 : ℤ) ^ (k - 1) * (m + 1)) := by
  exact sum_arm_reduction k m t hm ht

/-- A candidate admitted by the split filter satisfies a product congruence
    modulo the decomposed modulus. The congruence is the same 2-power × odd
    divisibility that the fire lattice decides. -/
theorem admitted_candidate_congruence {N modulus : Nat} {pair candidate : Pair}
    (h : candidate ∈ split N modulus pair) :
    multiply candidate % (2 * modulus) = N % (2 * modulus) ∧
    multiply candidate ≤ N := by
  unfold split at h
  split_ifs at h with bound
  · exact (Finset.mem_filter.mp h).2
  · simp at h

/-- The reconciliation statement: the producer's filter and the fire law share
    one odd modulus part. Both facts hold on the same candidate. -/
theorem fire_lattice_binds_split {N modulus : Nat} {pair candidate : Pair}
    (hmod : modulus ≠ 0) (h : candidate ∈ split N modulus pair) :
    (∃ k m, Odd m ∧ 2 * modulus = 2 ^ k * m) ∧
    multiply candidate % (2 * modulus) = N % (2 * modulus) := by
  exact ⟨split_modulus_is_two_power_times_odd modulus hmod,
         (admitted_candidate_congruence h).1⟩

end Imscribing.Paraconsistent.FireLatticeModulus
