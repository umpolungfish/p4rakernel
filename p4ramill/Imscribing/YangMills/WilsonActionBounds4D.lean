import Imscribing.YangMills.WilsonLattice4D

/-!
# 4D SU(N) Wilson Action Bounds & Contiguous Path Holonomy (`0 sorry`)
-/

namespace Imscribing.YangMills.WilsonBounds4D

open Imscribing.YangMills.WilsonLattice4D

theorem gaugeGroup_row_norm_sq_sum {N : ℕ} (A : GaugeGroup N) (i : Fin N) :
    (∑ j : Fin N, ‖(A : Matrix (Fin N) (Fin N) ℂ) i j‖ ^ 2) = 1 := by
  have hU : (A : Matrix (Fin N) (Fin N) ℂ) * star (A : Matrix (Fin N) (Fin N) ℂ) = 1 :=
    Matrix.mem_unitaryGroup_iff.mp (Matrix.mem_specialUnitaryGroup_iff.mp A.prop).1
  have hii : ((A : Matrix (Fin N) (Fin N) ℂ) * star (A : Matrix (Fin N) (Fin N) ℂ)) i i = 1 := by
    rw [hU, Matrix.one_apply_eq]
  have hsum : (∑ j : Fin N, ((‖(A : Matrix (Fin N) (Fin N) ℂ) i j‖ ^ 2 : ℝ) : ℂ)) = 1 := by
    simpa [Matrix.mul_apply, Matrix.star_apply, Complex.mul_conj, Complex.normSq_eq_norm_sq] using hii
  have hre := congrArg Complex.re hsum
  rw [Complex.re_sum] at hre
  simpa [sq] using hre

theorem gaugeGroup_entry_norm_le_one {N : ℕ} (A : GaugeGroup N) (i j : Fin N) :
    ‖(A : Matrix (Fin N) (Fin N) ℂ) i j‖ ≤ 1 := by
  have hsq : ‖(A : Matrix (Fin N) (Fin N) ℂ) i j‖ ^ 2 ≤ 1 := by
    calc
      ‖(A : Matrix (Fin N) (Fin N) ℂ) i j‖ ^ 2
          ≤ ∑ k : Fin N, ‖(A : Matrix (Fin N) (Fin N) ℂ) i k‖ ^ 2 :=
              Finset.single_le_sum (fun x _ => sq_nonneg ‖(A : Matrix (Fin N) (Fin N) ℂ) i x‖) (Finset.mem_univ j)
      _ = 1 := gaugeGroup_row_norm_sq_sum A i
  nlinarith [norm_nonneg ((A : Matrix (Fin N) (Fin N) ℂ) i j)]

theorem realTrace_abs_le {N : ℕ} (A : GaugeGroup N) :
    |realTrace A| ≤ (N : ℝ) := by
  unfold realTrace
  rw [Matrix.trace, Complex.re_sum]
  simp only [Matrix.diag_apply]
  calc
    |∑ i : Fin N, ((A : Matrix (Fin N) (Fin N) ℂ) i i).re|
        ≤ ∑ i : Fin N, |((A : Matrix (Fin N) (Fin N) ℂ) i i).re| :=
            Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin N, (1 : ℝ) :=
          Finset.sum_le_sum fun i _ =>
            le_trans (Complex.abs_re_le_norm _) (gaugeGroup_entry_norm_le_one A i i)
    _ = (N : ℝ) := by simp [Finset.sum_const]

theorem plaquette_density_bounds {N : ℕ} [NeZero N] (A : GaugeGroup N) :
    0 ≤ 1 - realTrace A / (N : ℝ) ∧ 1 - realTrace A / (N : ℝ) ≤ 2 := by
  have hN : (0 : ℝ) < (N : ℝ) := Nat.cast_pos.mpr (NeZero.pos N)
  obtain ⟨hlo, hhi⟩ := abs_le.mp (realTrace_abs_le A)
  have hd1 : -1 ≤ realTrace A / (N : ℝ) := by
    rw [le_div_iff₀ hN]; linarith
  have hd2 : realTrace A / (N : ℝ) ≤ 1 := by
    rw [div_le_iff₀ hN]; linarith
  exact ⟨by linarith, by linarith⟩

theorem wilsonAction_nonneg {N L : ℕ} [NeZero N] [NeZero L] {β : ℝ} (hβ : 0 ≤ β) (U : LinkConfig N L) :
    0 ≤ wilsonAction N L β U := by
  unfold wilsonAction
  refine mul_nonneg hβ (Finset.sum_nonneg fun x _ => Finset.sum_nonneg fun μ _ =>
    Finset.sum_nonneg fun ν _ => (plaquette_density_bounds _).1)

theorem wilsonAction_le {N L : ℕ} [NeZero N] [NeZero L] {β : ℝ} (hβ : 0 ≤ β) (U : LinkConfig N L) :
    wilsonAction N L β U ≤ 32 * β * ((Fintype.card (Lat4 L) : ℕ) : ℝ) := by
  unfold wilsonAction
  have hsum : (∑ x : Lat4 L, ∑ μ : Fin 4, ∑ ν : Fin 4,
      (1 - realTrace (plaquetteHolonomy U x μ ν) / (N : ℝ))) ≤
      32 * ((Fintype.card (Lat4 L) : ℕ) : ℝ) := by
    calc
      (∑ x : Lat4 L, ∑ μ : Fin 4, ∑ ν : Fin 4,
          (1 - realTrace (plaquetteHolonomy U x μ ν) / (N : ℝ)))
          ≤ ∑ _x : Lat4 L, ∑ _μ : Fin 4, ∑ _ν : Fin 4, (2 : ℝ) :=
              Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun μ _ =>
                Finset.sum_le_sum fun ν _ => (plaquette_density_bounds _).2
      _ = 32 * ((Fintype.card (Lat4 L) : ℕ) : ℝ) := by
            simp [Finset.sum_const, Finset.card_univ]; ring
  calc
    β * ∑ x : Lat4 L, ∑ μ : Fin 4, ∑ ν : Fin 4,
        (1 - realTrace (plaquetteHolonomy U x μ ν) / (N : ℝ))
        ≤ β * (32 * ((Fintype.card (Lat4 L) : ℕ) : ℝ)) :=
            mul_le_mul_of_nonneg_left hsum hβ
    _ = 32 * β * ((Fintype.card (Lat4 L) : ℕ) : ℝ) := by ring

theorem gibbsWeight_pos_le_one {N L : ℕ} [NeZero N] [NeZero L] {β : ℝ} (hβ : 0 ≤ β) (U : LinkConfig N L) :
    0 < Real.exp (-wilsonAction N L β U) ∧ Real.exp (-wilsonAction N L β U) ≤ 1 :=
  ⟨Real.exp_pos _, Real.exp_le_one_iff.mpr (neg_nonpos.mpr (wilsonAction_nonneg hβ U))⟩

def IsContiguousPath {L k : ℕ} (γ : Fin k → Lat4 L × Fin 4) : Prop :=
  ∀ (i : ℕ) (hi : i + 1 < k),
    (γ ⟨i, Nat.lt_of_succ_lt hi⟩).1 + stepDir L (γ ⟨i, Nat.lt_of_succ_lt hi⟩).2 =
      (γ ⟨i + 1, hi⟩).1

def pathHolonomy {N L : ℕ} : ∀ {k : ℕ}, LinkConfig N L → (Fin k → Lat4 L × Fin 4) → GaugeGroup N
  | 0, _, _ => 1
  | 1, U, γ => U (γ 0).1 (γ 0).2
  | _ + 2, U, γ => U (γ 0).1 (γ 0).2 * pathHolonomy U (fun i => γ i.succ)

theorem pathHolonomy_applyGauge {N L k : ℕ} (g : GaugeTransform N L) (U : LinkConfig N L)
    (hk : 0 < k) (γ : Fin k → Lat4 L × Fin 4) (hcontig : IsContiguousPath γ) :
    pathHolonomy (applyGauge g U) γ =
      g (γ ⟨0, hk⟩).1 * pathHolonomy U γ *
        (g ((γ ⟨k - 1, Nat.sub_lt hk Nat.one_pos⟩).1 +
          stepDir L (γ ⟨k - 1, Nat.sub_lt hk Nat.one_pos⟩).2))⁻¹ := by
  induction k with
  | zero => exact absurd hk (lt_irrefl 0)
  | succ m ih =>
      cases m with
      | zero => simp [pathHolonomy, applyGauge]
      | succ m' =>
          let γ' : Fin (m' + 1) → Lat4 L × Fin 4 := fun i => γ i.succ
          have hcontig' : IsContiguousPath γ' := fun i hi => by
            simpa [γ'] using hcontig (i + 1) (Nat.succ_lt_succ hi)
          have h_tail := ih (Nat.succ_pos m') γ' hcontig'
          have h_join : (γ 0).1 + stepDir L (γ 0).2 = (γ 1).1 :=
            hcontig 0 (Nat.succ_lt_succ (Nat.succ_pos m'))
          change applyGauge g U (γ 0).1 (γ 0).2 * pathHolonomy (applyGauge g U) γ' = _
          rw [h_tail]
          change g (γ 0).1 * U (γ 0).1 (γ 0).2 * (g ((γ 0).1 + stepDir L (γ 0).2))⁻¹ *
              (g (γ 1).1 * pathHolonomy U γ' *
                (g ((γ ⟨m' + 1, _⟩).1 + stepDir L (γ ⟨m' + 1, _⟩).2))⁻¹) =
            g (γ 0).1 * (U (γ 0).1 (γ 0).2 * pathHolonomy U γ') *
              (g ((γ ⟨m' + 1, _⟩).1 + stepDir L (γ ⟨m' + 1, _⟩).2))⁻¹
          rw [h_join]
          group

theorem wilsonLoop_gaugeInvariant {N L k : ℕ} [NeZero N] (hk : 0 < k)
    (g : GaugeTransform N L) (U : LinkConfig N L)
    (γ : Fin k → Lat4 L × Fin 4) (hcontig : IsContiguousPath γ)
    (hclosed : (γ ⟨k - 1, Nat.sub_lt hk Nat.one_pos⟩).1 +
        stepDir L (γ ⟨k - 1, Nat.sub_lt hk Nat.one_pos⟩).2 = (γ ⟨0, hk⟩).1) :
    realTrace (pathHolonomy (applyGauge g U) γ) = realTrace (pathHolonomy U γ) := by
  rw [pathHolonomy_applyGauge g U hk γ hcontig, hclosed, realTrace_conj]

end Imscribing.YangMills.WilsonBounds4D
