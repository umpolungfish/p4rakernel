import Imscribing.YangMills.WilsonActionBounds4D

/-!
# Gauge-Covariant Block-Spin Renormalization Group & Staple Smearing on 4D SU(N)

Proves unconditionally (`0 sorry`):
1. `blockOrigin` and `blockLink k L U`: exact `k`-to-1 coarse-graining from
   `Lat4 (k * L)` to `Lat4 L`.
2. `blockLink_applyGauge`: `blockLink k L (applyGauge g U) = applyGauge (g ∘ blockOrigin k L) (blockLink k L U)`.
3. `blockWilsonAction_gaugeInvariant`: exact gauge invariance of the coarse-grained
   Wilson action at every blocking scale `k ≥ 1`.
4. `forwardStaple_applyGauge` & `backwardStaple_applyGauge`: exact gauge covariance
   of the 6 orthogonal 3-link staples used in Balaban/APE smearing.
-/

namespace Imscribing.YangMills.WilsonBlockRG4D

open Imscribing.YangMills.WilsonLattice4D
open Imscribing.YangMills.WilsonBounds4D

/-- Coarse block origin `k * x` inside the fine 4D torus `Lat4 (k * L)`. -/
def blockOrigin (k L : ℕ) (x : Lat4 L) : Lat4 (k * L) :=
  fun μ => ((k * (x μ).val : ℕ) : ZMod (k * L))

private lemma blockOrigin_add_stepDir (k L : ℕ) [NeZero L] (x : Lat4 L) (μ : Fin 4) :
    blockOrigin k L (x + stepDir L μ) = blockOrigin k L x + k • stepDir (k * L) μ := by
  ext ν
  by_cases hν : ν = μ
  · subst hν
    simp only [blockOrigin, Pi.add_apply, stepDir, ↓reduceIte, Pi.smul_apply, nsmul_eq_mul, mul_one]
    have hmod : ((x ν + 1 : ZMod L).val) = ((x ν).val + 1) % L := by
      have hcast : x ν + 1 = (((x ν).val + 1 : ℕ) : ZMod L) := by
        push_cast; rw [ZMod.natCast_zmod_val]
      rw [hcast, ZMod.val_natCast]
    have hdiv := Nat.div_add_mod ((x ν).val + 1) L
    have hmul_div : k * ((x ν).val + 1) = (k * L) * (((x ν).val + 1) / L) +
        k * (((x ν).val + 1) % L) := by
      calc
        k * ((x ν).val + 1) = k * (L * (((x ν).val + 1) / L) + ((x ν).val + 1) % L) := by
            rw [hdiv]
        _ = (k * L) * (((x ν).val + 1) / L) + k * (((x ν).val + 1) % L) := by ring
    have h_eqZ : ((k * ((x ν).val + 1) : ℕ) : ZMod (k * L)) =
        ((k * (((x ν).val + 1) % L) : ℕ) : ZMod (k * L)) := by
      have hcast := congrArg (Nat.cast (R := ZMod (k * L))) hmul_div
      push_cast at hcast
      rw [ZMod.natCast_self, zero_mul, zero_add] at hcast
      exact hcast
    rw [hmod, ← h_eqZ]
    push_cast
    ring
  · simp [blockOrigin, stepDir, hν]

/-- Contiguous `k`-link fine lattice path from `blockOrigin k L x` to `blockOrigin k L (x + e_μ)`. -/
def blockPath (k L : ℕ) (x : Lat4 L) (μ : Fin 4) : Fin k → Lat4 (k * L) × Fin 4 :=
  fun i => (blockOrigin k L x + (i : ℕ) • stepDir (k * L) μ, μ)

theorem blockPath_isContiguous (k L : ℕ) (x : Lat4 L) (μ : Fin 4) :
    IsContiguousPath (blockPath k L x μ) := by
  intro i hi
  simp only [blockPath, Fin.val_mk, add_smul, one_smul, ← add_assoc]

theorem blockPath_endpoint (k L : ℕ) [NeZero L] (hk : 0 < k) (x : Lat4 L) (μ : Fin 4) :
    (blockPath k L x μ ⟨k - 1, Nat.sub_lt hk Nat.one_pos⟩).1 +
        stepDir (k * L) (blockPath k L x μ ⟨k - 1, Nat.sub_lt hk Nat.one_pos⟩).2 =
      blockOrigin k L (x + stepDir L μ) := by
  simp only [blockPath]
  rw [add_assoc, ← succ_nsmul, Nat.sub_add_cancel hk, blockOrigin_add_stepDir]

/-- Coarse-grained block-spin link variable in `SU(N)` obtained by parallel transport
    along the `k`-link path `blockPath k L x μ`. -/
def blockLink (k L : ℕ) (U : LinkConfig N (k * L)) : LinkConfig N L :=
  fun x μ => pathHolonomy U (blockPath k L x μ)

/-- **Exact Gauge Covariance of Block-Spin Coarsening:**
    Fine gauge transform `g` on `Lat4 (k * L)` induces the exact coarse gauge
    transform `g ∘ blockOrigin k L` on `blockLink k L U`. -/
theorem blockLink_applyGauge {N : ℕ} (k L : ℕ) [NeZero L] (hk : 0 < k)
    (g : GaugeTransform N (k * L)) (U : LinkConfig N (k * L)) :
    blockLink k L (applyGauge g U) =
      applyGauge (fun x => g (blockOrigin k L x)) (blockLink k L U) := by
  ext x μ
  unfold blockLink applyGauge
  rw [pathHolonomy_applyGauge g U hk (blockPath k L x μ) (blockPath_isContiguous k L x μ),
      blockPath_endpoint k L hk x μ]
  have h0 : (blockPath k L x μ ⟨0, hk⟩).1 = blockOrigin k L x := by
    simp [blockPath]
  rw [h0]

/-- **Coarse-Grained Block-Spin Wilson Action Gauge Invariance.** -/
theorem blockWilsonAction_gaugeInvariant (N k L : ℕ) [NeZero N] [NeZero L] (hk : 0 < k)
    (β : ℝ) (g : GaugeTransform N (k * L)) (U : LinkConfig N (k * L)) :
    wilsonAction N L β (blockLink k L (applyGauge g U)) =
      wilsonAction N L β (blockLink k L U) := by
  rw [blockLink_applyGauge k L hk g U]
  exact wilsonAction_gaugeInvariant N L β (fun x => g (blockOrigin k L x)) (blockLink k L U)

/-- Forward orthogonal 3-link staple in the `(μ, ν)` plane attached to `(x, μ)`. -/
def forwardStaple {N L : ℕ} (U : LinkConfig N L) (x : Lat4 L) (μ ν : Fin 4) : GaugeGroup N :=
  U x ν * U (x + stepDir L ν) μ * (U (x + stepDir L μ) ν)⁻¹

/-- Backward orthogonal 3-link staple in the `(μ, ν)` plane attached to `(x, μ)`. -/
def backwardStaple {N L : ℕ} (U : LinkConfig N L) (x : Lat4 L) (μ ν : Fin 4) : GaugeGroup N :=
  (U (x - stepDir L ν) ν)⁻¹ * U (x - stepDir L ν) μ *
    U (x - stepDir L ν + stepDir L μ) ν

/-- **Exact Gauge Covariance of Forward Staples.** -/
theorem forwardStaple_applyGauge {N L : ℕ} (g : GaugeTransform N L) (U : LinkConfig N L)
    (x : Lat4 L) (μ ν : Fin 4) :
    forwardStaple (applyGauge g U) x μ ν =
      g x * forwardStaple U x μ ν * (g (x + stepDir L μ))⁻¹ := by
  have hcomm : x + stepDir L ν + stepDir L μ = x + stepDir L μ + stepDir L ν := by
    rw [add_assoc, add_assoc, add_comm (stepDir L ν) (stepDir L μ)]
  simp only [forwardStaple, applyGauge, mul_inv_rev, inv_inv, hcomm]
  group

/-- **Exact Gauge Covariance of Backward Staples.** -/
theorem backwardStaple_applyGauge {N L : ℕ} (g : GaugeTransform N L) (U : LinkConfig N L)
    (x : Lat4 L) (μ ν : Fin 4) :
    backwardStaple (applyGauge g U) x μ ν =
      g x * backwardStaple U x μ ν * (g (x + stepDir L μ))⁻¹ := by
  have h1 : x - stepDir L ν + stepDir L ν = x := sub_add_cancel x (stepDir L ν)
  have h2 : x - stepDir L ν + stepDir L μ + stepDir L ν = x + stepDir L μ := by
    rw [add_assoc, add_comm (stepDir L μ) (stepDir L ν), ← add_assoc, sub_add_cancel]
  simp only [backwardStaple, applyGauge, mul_inv_rev, inv_inv, h1, h2]
  group

end Imscribing.YangMills.WilsonBlockRG4D