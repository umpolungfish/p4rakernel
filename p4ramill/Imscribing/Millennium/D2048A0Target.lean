import Mathlib
import Imscribing.Millennium.SIC_D2048_A0Stratum
open SIC.D2048.A0Stratum
namespace Imscribing.Millennium.D2048A0Target
noncomputable section

/-- The d=2048 a=0 stratum obligation is fully specified as a computable
    predicate on the modulus data N : Nat -> F2048. The engine checks that
    the eleven orbit-representative overlaps equal 1/2049. The generator
    `gen_lean_2048_a0.py` that pins N is NOT in the checkout and the manifest
    records deep_vanish_floor:false, so no witness is claimed. -/
theorem a0_stratum_target :
    a0_b_values = [1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024] ∧
    rTarget = rK [1/2049, 0] ∧
    (∀ N : ℕ → F2048, a0_slots_admitted N = true →
      ∀ b ∈ a0_b_values, a0_overlap_sq_eq N b = true) := by
  refine ⟨rfl, rfl, ?_⟩
  intro N h b hb
  unfold a0_slots_admitted at h
  simpa [List.all_eq_true] using (List.all_eq_true.mp h b hb)

