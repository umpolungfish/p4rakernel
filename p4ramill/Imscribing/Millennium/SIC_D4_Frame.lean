import Mathlib
import Imscribing.Millennium.SIC_POVM_Stark
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000
namespace SIC.D4.Frame
open Millennium.SIC_POVM_Stark
noncomputable section

def s2 : ℝ := Real.sqrt 2
def s5 : ℝ := Real.sqrt 5
def uu : ℝ := Real.sqrt (2+s5)
lemma s2_sq : s2^2 = 2 := by rw [s2, Real.sq_sqrt] <;> norm_num
lemma uu_sq : uu^2 = 2 + s5 := by rw [uu, Real.sq_sqrt]; rw [s5]; positivity
lemma s5_sq : s5^2 = 5 := by rw [s5, Real.sq_sqrt] <;> norm_num
lemma uu_quartic : uu^4 = 4*uu^2 + 1 := by
  calc uu^4 = (uu^2)^2 := by ring
       _ = (2+s5)^2 := by rw [uu_sq]
       _ = 4*uu^2 + 1 := by rw [uu_sq]; nlinarith [s5_sq]
def v : Fin 4 → ℂ := ![
  ((1 + s2*uu - uu)/2 : ℝ) + ((s2 + uu - 1)/2 : ℝ) * Complex.I,
  1,
  ((1 - s2*uu + uu)/2 : ℝ) + ((s2 - uu - 1)/2 : ℝ) * Complex.I,
  ((1 - s2 : ℝ) : ℂ) * Complex.I]

lemma I2 : Complex.I^2 = -1 := by rw [pow_two, Complex.I_mul_I]
lemma I3 : Complex.I^3 = -Complex.I := by
  calc Complex.I^3 = Complex.I^2*Complex.I := by ring
       _ = -Complex.I := by rw [I2]; ring
lemma I4 : Complex.I^4 = 1 := by
  calc Complex.I^4 = (Complex.I^2)^2 := by ring
       _ = 1 := by rw [I2]; ring
lemma I5 : Complex.I^5 = Complex.I := by
  calc Complex.I^5 = Complex.I^4*Complex.I := by ring
       _ = Complex.I := by rw [I4]; ring
lemma I6 : Complex.I^6 = -1 := by
  calc Complex.I^6 = Complex.I^2 * Complex.I^4 := by ring
       _ = -1 := by simp [I4, I2]
lemma I7 : Complex.I^7 = -Complex.I := by
  calc Complex.I^7 = Complex.I^3 * Complex.I^4 := by ring
       _ = -Complex.I := by simp [I4, I3]
lemma I8 : Complex.I^8 = 1 := by
  calc Complex.I^8 = Complex.I^4 * Complex.I^4 := by ring
       _ = 1 := by simp [I4, I4]
lemma I9 : Complex.I^9 = Complex.I := by
  calc Complex.I^9 = Complex.I^5 * Complex.I^4 := by ring
       _ = Complex.I := by simp [I4, I5]
lemma I10 : Complex.I^10 = -1 := by
  calc Complex.I^10 = Complex.I^6 * Complex.I^4 := by ring
       _ = -1 := by simp [I4, I6]
lemma I11 : Complex.I^11 = -Complex.I := by
  calc Complex.I^11 = Complex.I^7 * Complex.I^4 := by ring
       _ = -Complex.I := by simp [I4, I7]
lemma I12 : Complex.I^12 = 1 := by
  calc Complex.I^12 = Complex.I^8 * Complex.I^4 := by ring
       _ = 1 := by simp [I4, I8]
lemma I13 : Complex.I^13 = Complex.I := by
  calc Complex.I^13 = Complex.I^9 * Complex.I^4 := by ring
       _ = Complex.I := by simp [I4, I9]
lemma I14 : Complex.I^14 = -1 := by
  calc Complex.I^14 = Complex.I^10 * Complex.I^4 := by ring
       _ = -1 := by simp [I4, I10]
lemma I15 : Complex.I^15 = -Complex.I := by
  calc Complex.I^15 = Complex.I^11 * Complex.I^4 := by ring
       _ = -Complex.I := by simp [I4, I11]
lemma I16 : Complex.I^16 = 1 := by
  calc Complex.I^16 = Complex.I^12 * Complex.I^4 := by ring
       _ = 1 := by simp [I4, I12]
lemma omega4 : omega_d 4 = Complex.I := by
  rw [omega_d]; norm_num
  rw [show (2 * Real.pi * Complex.I / (4:ℂ)) = (Real.pi / 2 : ℂ) * Complex.I by ring]
  apply Complex.ext
  · simp [Complex.exp_ofReal_mul_I_re, Real.cos_pi_div_two]
  · simp [Complex.exp_ofReal_mul_I_im, Real.sin_pi_div_two]

def N : ℝ := -s2*uu^2 - 3*s2 + 2*uu^2 + 6

lemma d4_inner_01 : wh_inner 4 v (D_ah 4 0 1 0 v) = ((2*s2*uu - 2*uu : ℝ) : ℂ) - ((2*s2 - 2 : ℝ) : ℂ) * Complex.I := by
  simp [v, D_ah, X_d, Z_d, omega4, wh_inner, Fin.sum_univ_four]
  ring_nf
  simp [I2,I3,I4,I5,I6,I7,I8,I9,I10,I11,I12,I13,I14,I15,I16, ← Complex.ofReal_pow, map_ofNat]
  norm_num
  try ring_nf
  try simp [s2_sq, uu_quartic, ← Complex.ofReal_pow]
  try ring_nf
  try simp [s2_sq, uu_quartic, ← Complex.ofReal_pow]
  try ring_nf

lemma d4_overlap_01 : 5 * Complex.normSq (wh_inner 4 v (D_ah 4 0 1 0 v)) = (N:ℝ)^2 := by
  rw [d4_inner_01]
  rw [Complex.normSq_apply]
  simp [← Complex.ofReal_pow]
  unfold N
  ring_nf
  simp [s2_sq, uu_quartic]
  ring_nf

lemma d4_inner_02 : wh_inner 4 v (D_ah 4 0 2 0 v) = ((-s2*uu^2 + s2 + 2*uu^2 - 2 : ℝ) : ℂ) := by
  simp [v, D_ah, X_d, Z_d, omega4, wh_inner, Fin.sum_univ_four]
  ring_nf
  simp [I2,I3,I4,I5,I6,I7,I8,I9,I10,I11,I12,I13,I14,I15,I16, ← Complex.ofReal_pow, map_ofNat]
  norm_num
  try ring_nf
  try simp [s2_sq, uu_quartic, ← Complex.ofReal_pow]
  try ring_nf
  try simp [s2_sq, uu_quartic, ← Complex.ofReal_pow]
  try ring_nf

lemma d4_overlap_02 : 5 * Complex.normSq (wh_inner 4 v (D_ah 4 0 2 0 v)) = (N:ℝ)^2 := by
  rw [d4_inner_02]
  rw [Complex.normSq_apply]
  simp [← Complex.ofReal_pow]
  unfold N
  ring_nf
  simp [s2_sq, uu_quartic]
  ring_nf

lemma d4_inner_03 : wh_inner 4 v (D_ah 4 0 3 0 v) = ((2*s2*uu - 2*uu : ℝ) : ℂ) - ((2 - 2*s2 : ℝ) : ℂ) * Complex.I := by
  simp [v, D_ah, X_d, Z_d, omega4, wh_inner, Fin.sum_univ_four]
  ring_nf
  simp [I2,I3,I4,I5,I6,I7,I8,I9,I10,I11,I12,I13,I14,I15,I16, ← Complex.ofReal_pow, map_ofNat]
  norm_num
  try ring_nf
  try simp [s2_sq, uu_quartic, ← Complex.ofReal_pow]
  try ring_nf
  try simp [s2_sq, uu_quartic, ← Complex.ofReal_pow]
  try ring_nf

lemma d4_overlap_03 : 5 * Complex.normSq (wh_inner 4 v (D_ah 4 0 3 0 v)) = (N:ℝ)^2 := by
  rw [d4_inner_03]
  rw [Complex.normSq_apply]
  simp [← Complex.ofReal_pow]
  unfold N
  ring_nf
  simp [s2_sq, uu_quartic]
  ring_nf

lemma d4_inner_10 : wh_inner 4 v (D_ah 4 1 0 0 v) = ((2*s2 - 2 : ℝ) : ℂ) - ((2*s2*uu - 2*uu : ℝ) : ℂ) * Complex.I := by
  simp [v, D_ah, X_d, Z_d, omega4, wh_inner, Fin.sum_univ_four]
  ring_nf
  simp [I2,I3,I4,I5,I6,I7,I8,I9,I10,I11,I12,I13,I14,I15,I16, ← Complex.ofReal_pow, map_ofNat]
  norm_num
  try ring_nf
  try simp [s2_sq, uu_quartic, ← Complex.ofReal_pow]
  try ring_nf
  try simp [s2_sq, uu_quartic, ← Complex.ofReal_pow]
  try ring_nf

lemma d4_overlap_10 : 5 * Complex.normSq (wh_inner 4 v (D_ah 4 1 0 0 v)) = (N:ℝ)^2 := by
  rw [d4_inner_10]
  rw [Complex.normSq_apply]
  simp [← Complex.ofReal_pow]
  unfold N
  ring_nf
  simp [s2_sq, uu_quartic]
  ring_nf

lemma d4_inner_11 : wh_inner 4 v (D_ah 4 1 1 0 v) = ((s2*uu - s2 - 2*uu + 2 : ℝ) : ℂ) - ((-s2*uu - s2 + 2*uu + 2 : ℝ) : ℂ) * Complex.I := by
  simp [v, D_ah, X_d, Z_d, omega4, wh_inner, Fin.sum_univ_four]
  ring_nf
  simp [I2,I3,I4,I5,I6,I7,I8,I9,I10,I11,I12,I13,I14,I15,I16, ← Complex.ofReal_pow, map_ofNat]
  norm_num
  try ring_nf
  try simp [s2_sq, uu_quartic, ← Complex.ofReal_pow]
  try ring_nf
  try simp [s2_sq, uu_quartic, ← Complex.ofReal_pow]
  try ring_nf

lemma d4_overlap_11 : 5 * Complex.normSq (wh_inner 4 v (D_ah 4 1 1 0 v)) = (N:ℝ)^2 := by
  rw [d4_inner_11]
  rw [Complex.normSq_apply]
  simp [← Complex.ofReal_pow]
  unfold N
  ring_nf
  simp [s2_sq, uu_quartic]
  ring_nf

lemma d4_inner_12 : wh_inner 4 v (D_ah 4 1 2 0 v) = ((2*s2*uu - 2*uu : ℝ) : ℂ) - ((2*s2 - 2 : ℝ) : ℂ) * Complex.I := by
  simp [v, D_ah, X_d, Z_d, omega4, wh_inner, Fin.sum_univ_four]
  ring_nf
  simp [I2,I3,I4,I5,I6,I7,I8,I9,I10,I11,I12,I13,I14,I15,I16, ← Complex.ofReal_pow, map_ofNat]
  norm_num
  try ring_nf
  try simp [s2_sq, uu_quartic, ← Complex.ofReal_pow]
  try ring_nf
  try simp [s2_sq, uu_quartic, ← Complex.ofReal_pow]
  try ring_nf

lemma d4_overlap_12 : 5 * Complex.normSq (wh_inner 4 v (D_ah 4 1 2 0 v)) = (N:ℝ)^2 := by
  rw [d4_inner_12]
  rw [Complex.normSq_apply]
  simp [← Complex.ofReal_pow]
  unfold N
  ring_nf
  simp [s2_sq, uu_quartic]
  ring_nf

lemma d4_inner_13 : wh_inner 4 v (D_ah 4 1 3 0 v) = ((-s2*uu - s2 + 2*uu + 2 : ℝ) : ℂ) - ((-s2*uu + s2 + 2*uu - 2 : ℝ) : ℂ) * Complex.I := by
  simp [v, D_ah, X_d, Z_d, omega4, wh_inner, Fin.sum_univ_four]
  ring_nf
  simp [I2,I3,I4,I5,I6,I7,I8,I9,I10,I11,I12,I13,I14,I15,I16, ← Complex.ofReal_pow, map_ofNat]
  norm_num
  try ring_nf
  try simp [s2_sq, uu_quartic, ← Complex.ofReal_pow]
  try ring_nf
  try simp [s2_sq, uu_quartic, ← Complex.ofReal_pow]
  try ring_nf

lemma d4_overlap_13 : 5 * Complex.normSq (wh_inner 4 v (D_ah 4 1 3 0 v)) = (N:ℝ)^2 := by
  rw [d4_inner_13]
  rw [Complex.normSq_apply]
  simp [← Complex.ofReal_pow]
  unfold N
  ring_nf
  simp [s2_sq, uu_quartic]
  ring_nf

lemma d4_inner_20 : wh_inner 4 v (D_ah 4 2 0 0 v) = ((s2*uu^2 - s2 - 2*uu^2 + 2 : ℝ) : ℂ) := by
  simp [v, D_ah, X_d, Z_d, omega4, wh_inner, Fin.sum_univ_four]
  ring_nf
  simp [I2,I3,I4,I5,I6,I7,I8,I9,I10,I11,I12,I13,I14,I15,I16, ← Complex.ofReal_pow, map_ofNat]
  norm_num
  try ring_nf
  try simp [s2_sq, uu_quartic, ← Complex.ofReal_pow]
  try ring_nf
  try simp [s2_sq, uu_quartic, ← Complex.ofReal_pow]
  try ring_nf

lemma d4_overlap_20 : 5 * Complex.normSq (wh_inner 4 v (D_ah 4 2 0 0 v)) = (N:ℝ)^2 := by
  rw [d4_inner_20]
  rw [Complex.normSq_apply]
  simp [← Complex.ofReal_pow]
  unfold N
  ring_nf
  simp [s2_sq, uu_quartic]
  ring_nf

lemma d4_inner_21 : wh_inner 4 v (D_ah 4 2 1 0 v) = ((2 - 2*s2 : ℝ) : ℂ) - ((2*s2*uu - 2*uu : ℝ) : ℂ) * Complex.I := by
  simp [v, D_ah, X_d, Z_d, omega4, wh_inner, Fin.sum_univ_four]
  ring_nf
  simp [I2,I3,I4,I5,I6,I7,I8,I9,I10,I11,I12,I13,I14,I15,I16, ← Complex.ofReal_pow, map_ofNat]
  norm_num
  try ring_nf
  try simp [s2_sq, uu_quartic, ← Complex.ofReal_pow]
  try ring_nf
  try simp [s2_sq, uu_quartic, ← Complex.ofReal_pow]
  try ring_nf

lemma d4_overlap_21 : 5 * Complex.normSq (wh_inner 4 v (D_ah 4 2 1 0 v)) = (N:ℝ)^2 := by
  rw [d4_inner_21]
  rw [Complex.normSq_apply]
  simp [← Complex.ofReal_pow]
  unfold N
  ring_nf
  simp [s2_sq, uu_quartic]
  ring_nf

lemma d4_inner_22 : wh_inner 4 v (D_ah 4 2 2 0 v) = ((s2*uu^2 - s2 - 2*uu^2 + 2 : ℝ) : ℂ) := by
  simp [v, D_ah, X_d, Z_d, omega4, wh_inner, Fin.sum_univ_four]
  ring_nf
  simp [I2,I3,I4,I5,I6,I7,I8,I9,I10,I11,I12,I13,I14,I15,I16, ← Complex.ofReal_pow, map_ofNat]
  norm_num
  try ring_nf
  try simp [s2_sq, uu_quartic, ← Complex.ofReal_pow]
  try ring_nf
  try simp [s2_sq, uu_quartic, ← Complex.ofReal_pow]
  try ring_nf

lemma d4_overlap_22 : 5 * Complex.normSq (wh_inner 4 v (D_ah 4 2 2 0 v)) = (N:ℝ)^2 := by
  rw [d4_inner_22]
  rw [Complex.normSq_apply]
  simp [← Complex.ofReal_pow]
  unfold N
  ring_nf
  simp [s2_sq, uu_quartic]
  ring_nf

lemma d4_inner_23 : wh_inner 4 v (D_ah 4 2 3 0 v) = ((2*s2 - 2 : ℝ) : ℂ) - ((2*s2*uu - 2*uu : ℝ) : ℂ) * Complex.I := by
  simp [v, D_ah, X_d, Z_d, omega4, wh_inner, Fin.sum_univ_four]
  ring_nf
  simp [I2,I3,I4,I5,I6,I7,I8,I9,I10,I11,I12,I13,I14,I15,I16, ← Complex.ofReal_pow, map_ofNat]
  norm_num
  try ring_nf
  try simp [s2_sq, uu_quartic, ← Complex.ofReal_pow]
  try ring_nf
  try simp [s2_sq, uu_quartic, ← Complex.ofReal_pow]
  try ring_nf

lemma d4_overlap_23 : 5 * Complex.normSq (wh_inner 4 v (D_ah 4 2 3 0 v)) = (N:ℝ)^2 := by
  rw [d4_inner_23]
  rw [Complex.normSq_apply]
  simp [← Complex.ofReal_pow]
  unfold N
  ring_nf
  simp [s2_sq, uu_quartic]
  ring_nf

lemma d4_inner_30 : wh_inner 4 v (D_ah 4 3 0 0 v) = ((2*s2 - 2 : ℝ) : ℂ) - ((-2*s2*uu + 2*uu : ℝ) : ℂ) * Complex.I := by
  simp [v, D_ah, X_d, Z_d, omega4, wh_inner, Fin.sum_univ_four]
  ring_nf
  simp [I2,I3,I4,I5,I6,I7,I8,I9,I10,I11,I12,I13,I14,I15,I16, ← Complex.ofReal_pow, map_ofNat]
  norm_num
  try ring_nf
  try simp [s2_sq, uu_quartic, ← Complex.ofReal_pow]
  try ring_nf
  try simp [s2_sq, uu_quartic, ← Complex.ofReal_pow]
  try ring_nf

lemma d4_overlap_30 : 5 * Complex.normSq (wh_inner 4 v (D_ah 4 3 0 0 v)) = (N:ℝ)^2 := by
  rw [d4_inner_30]
  rw [Complex.normSq_apply]
  simp [← Complex.ofReal_pow]
  unfold N
  ring_nf
  simp [s2_sq, uu_quartic]
  ring_nf

lemma d4_inner_31 : wh_inner 4 v (D_ah 4 3 1 0 v) = ((-s2*uu + s2 + 2*uu - 2 : ℝ) : ℂ) - ((-s2*uu - s2 + 2*uu + 2 : ℝ) : ℂ) * Complex.I := by
  simp [v, D_ah, X_d, Z_d, omega4, wh_inner, Fin.sum_univ_four]
  ring_nf
  simp [I2,I3,I4,I5,I6,I7,I8,I9,I10,I11,I12,I13,I14,I15,I16, ← Complex.ofReal_pow, map_ofNat]
  norm_num
  try ring_nf
  try simp [s2_sq, uu_quartic, ← Complex.ofReal_pow]
  try ring_nf
  try simp [s2_sq, uu_quartic, ← Complex.ofReal_pow]
  try ring_nf

lemma d4_overlap_31 : 5 * Complex.normSq (wh_inner 4 v (D_ah 4 3 1 0 v)) = (N:ℝ)^2 := by
  rw [d4_inner_31]
  rw [Complex.normSq_apply]
  simp [← Complex.ofReal_pow]
  unfold N
  ring_nf
  simp [s2_sq, uu_quartic]
  ring_nf

lemma d4_inner_32 : wh_inner 4 v (D_ah 4 3 2 0 v) = ((-2*s2*uu + 2*uu : ℝ) : ℂ) - ((2*s2 - 2 : ℝ) : ℂ) * Complex.I := by
  simp [v, D_ah, X_d, Z_d, omega4, wh_inner, Fin.sum_univ_four]
  ring_nf
  simp [I2,I3,I4,I5,I6,I7,I8,I9,I10,I11,I12,I13,I14,I15,I16, ← Complex.ofReal_pow, map_ofNat]
  norm_num
  try ring_nf
  try simp [s2_sq, uu_quartic, ← Complex.ofReal_pow]
  try ring_nf
  try simp [s2_sq, uu_quartic, ← Complex.ofReal_pow]
  try ring_nf

lemma d4_overlap_32 : 5 * Complex.normSq (wh_inner 4 v (D_ah 4 3 2 0 v)) = (N:ℝ)^2 := by
  rw [d4_inner_32]
  rw [Complex.normSq_apply]
  simp [← Complex.ofReal_pow]
  unfold N
  ring_nf
  simp [s2_sq, uu_quartic]
  ring_nf

lemma d4_inner_33 : wh_inner 4 v (D_ah 4 3 3 0 v) = ((s2*uu + s2 - 2*uu - 2 : ℝ) : ℂ) - ((-s2*uu + s2 + 2*uu - 2 : ℝ) : ℂ) * Complex.I := by
  simp [v, D_ah, X_d, Z_d, omega4, wh_inner, Fin.sum_univ_four]
  ring_nf
  simp [I2,I3,I4,I5,I6,I7,I8,I9,I10,I11,I12,I13,I14,I15,I16, ← Complex.ofReal_pow, map_ofNat]
  norm_num
  try ring_nf
  try simp [s2_sq, uu_quartic, ← Complex.ofReal_pow]
  try ring_nf
  try simp [s2_sq, uu_quartic, ← Complex.ofReal_pow]
  try ring_nf


lemma d4_overlap_33 : 5 * Complex.normSq (wh_inner 4 v (D_ah 4 3 3 0 v)) = (N:ℝ)^2 := by
  rw [d4_inner_33]
  rw [Complex.normSq_apply]
  simp [← Complex.ofReal_pow]
  unfold N
  ring_nf
  simp [s2_sq, uu_quartic]
  ring_nf

lemma v_norm : wh_inner 4 v v = (N : ℂ) := by
  simp [v, wh_inner, Fin.sum_univ_four]
  ring_nf
  simp [I2,I3,I4,I5,I6,I7,I8,I9,I10,I11,I12,I13,I14,I15,I16, ← Complex.ofReal_pow, map_ofNat]
  norm_num
  try ring_nf
  unfold N
  simp [s2_sq, uu_quartic, ← Complex.ofReal_pow]
  ring_nf

lemma N_pos : 0 < N := by
  unfold N s2 uu s5
  have hs2sq : (Real.sqrt 2)^2 = 2 := by rw [Real.sq_sqrt] <;> norm_num
  have hs5sq : (Real.sqrt 5)^2 = 5 := by rw [Real.sq_sqrt] <;> norm_num
  have huusq : (Real.sqrt (2+Real.sqrt 5))^2 = 2+Real.sqrt 5 := by
    rw [Real.sq_sqrt]; positivity
  have hs2nn : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have hs5nn : 0 ≤ Real.sqrt 5 := Real.sqrt_nonneg 5
  have hnn : 0 ≤ Real.sqrt (2+Real.sqrt 5) := Real.sqrt_nonneg _
  nlinarith [hs2sq, hs5sq, huusq, hs2nn, hs5nn, hnn]

lemma X_smul_point (c : ℂ) (w : Fin 4 → ℂ) :
    X_d 4 (fun k => c * w k) = fun k => c * (X_d 4 w k) := by
  funext k
  simp [X_d]

lemma Z_smul_point (c : ℂ) (w : Fin 4 → ℂ) :
    Z_d 4 (fun k => c * w k) = fun k => c * (Z_d 4 w k) := by
  funext k
  simp [Z_d, mul_assoc, mul_left_comm, mul_comm]

lemma X_smul (c : ℂ) (n : ℕ) (w : Fin 4 → ℂ) :
    (Nat.iterate (X_d 4) n) (fun k => c * w k) =
      fun k => c * ((Nat.iterate (X_d 4) n) w k) := by
  induction n generalizing w with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply, X_smul_point, ih]
      rw [← Function.iterate_succ_apply]

lemma Z_smul (c : ℂ) (n : ℕ) (w : Fin 4 → ℂ) :
    (Nat.iterate (Z_d 4) n) (fun k => c * w k) =
      fun k => c * ((Nat.iterate (Z_d 4) n) w k) := by
  induction n generalizing w with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply, Z_smul_point, ih]
      rw [← Function.iterate_succ_apply]

lemma D_ah_smul (c : ℂ) (a b t : Fin 4) (w : Fin 4 → ℂ) :
    D_ah 4 a b t (fun k => c * w k) = fun k => c * D_ah 4 a b t w k := by
  funext k
  simp [D_ah, X_smul, Z_smul, mul_assoc, mul_left_comm, mul_comm]

lemma wh_inner_smul_real (c : ℝ) (w z : Fin 4 → ℂ) :
    wh_inner 4 (fun k => (c : ℂ) * w k) (fun k => (c : ℂ) * z k) =
      ((c*c : ℝ) : ℂ) * wh_inner 4 w z := by
  simp [wh_inner, Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm]

def psi : Fin 4 → ℂ := fun k => v k / (Real.sqrt N : ℂ)

lemma psi_inner_scale (a b : Fin 4) :
    wh_inner 4 psi (D_ah 4 a b 0 psi) =
      ((1/N : ℝ) : ℂ) * wh_inner 4 v (D_ah 4 a b 0 v) := by
  let c : ℝ := 1 / Real.sqrt N
  have hpsi : psi = fun k => (c : ℂ) * v k := by
    funext k
    simp [psi, c, div_eq_mul_inv]
    ring
  rw [hpsi]
  rw [D_ah_smul, wh_inner_smul_real]
  have hc : c*c = 1/N := by
    unfold c
    have hs : Real.sqrt N ≠ 0 := (Real.sqrt_pos.2 N_pos).ne'
    field_simp [hs, ne_of_gt N_pos]
    rw [Real.sq_sqrt (le_of_lt N_pos)]
  rw [hc]


lemma inv_sqrt_sq : (1 / Real.sqrt N) * (1 / Real.sqrt N) = 1/N := by
  have hs : Real.sqrt N ≠ 0 := (Real.sqrt_pos.2 N_pos).ne'
  field_simp [hs, ne_of_gt N_pos]
  rw [Real.sq_sqrt (le_of_lt N_pos)]

lemma psi_eq_smul : psi = fun k => ((1 / Real.sqrt N : ℝ) : ℂ) * v k := by
  funext k
  simp [psi, div_eq_mul_inv]
  ring

lemma psi_norm : wh_normSq 4 psi = 1 := by
  rw [psi_eq_smul]
  rw [wh_normSq, wh_inner_smul_real, v_norm, inv_sqrt_sq]
  norm_num [ne_of_gt N_pos]

lemma psi_equi (a b : Fin 4) (hab : (a,b) ≠ (0,0)) :
    ((4 : ℝ) + 1) * ‖wh_inner 4 psi (D_ah 4 a b 0 psi)‖ ^ 2 = 1 := by
  rw [show ((4:ℝ)+1) = 5 by norm_num]
  rw [← Complex.normSq_eq_norm_sq]
  rw [psi_inner_scale, Complex.normSq_mul, Complex.normSq_ofReal]
  have hNne : N ≠ 0 := ne_of_gt N_pos
  fin_cases a <;> fin_cases b
  · exfalso; exact hab rfl
  all_goals
    field_simp [hNne]
    first
    | simpa using d4_overlap_01
    | simpa using d4_overlap_02
    | simpa using d4_overlap_03
    | simpa using d4_overlap_10
    | simpa using d4_overlap_11
    | simpa using d4_overlap_12
    | simpa using d4_overlap_13
    | simpa using d4_overlap_20
    | simpa using d4_overlap_21
    | simpa using d4_overlap_22
    | simpa using d4_overlap_23
    | simpa using d4_overlap_30
    | simpa using d4_overlap_31
    | simpa using d4_overlap_32
    | simpa using d4_overlap_33

lemma d4_sic : IsSICPOVM 4 psi where
  norm_eq := psi_norm
  equiangular := psi_equi

theorem sicpovm_exists_4 : Millennium.SIC_POVM_Stark.SICPOVM_Exists 4 := ⟨psi, d4_sic⟩

