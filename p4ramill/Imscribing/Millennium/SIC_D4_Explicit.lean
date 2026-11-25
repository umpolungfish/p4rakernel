import Mathlib
import Imscribing.Millennium.SIC_POVM_Stark
set_option maxRecDepth 10000000
set_option maxHeartbeats 20000000
namespace SIC.D4.Explicit
open Millennium.SIC_POVM_Stark
noncomputable section

def s2 : ℝ := Real.sqrt 2
def s5 : ℝ := Real.sqrt 5
def uu : ℝ := Real.sqrt (2+s5)
def tt : ℝ := s2*uu*(5-s5)/2
def A1 : ℝ := (10 + 5*s2 - 2*s5 - s2*s5)/40
def A3 : ℝ := (10 - 5*s2 - 2*s5 + s2*s5)/40
def B2 : ℝ := (5+s5-tt)/20
def B4 : ℝ := (5+s5+tt)/20
def r1re : ℝ := (-10 - 10*uu + 5*tt + s5*tt - 5*uu*tt + 3*s5*uu*tt)/20
def r1im : ℝ := (uu-1)/2
def r3re : ℝ := (10 - 10*uu + 5*tt + s5*tt + 5*uu*tt - 3*s5*uu*tt)/20
def r3im : ℝ := (uu+1)/2

lemma s2_sq : s2^2 = 2 := by rw [s2, Real.sq_sqrt] <;> norm_num
lemma s5_sq : s5^2 = 5 := by rw [s5, Real.sq_sqrt] <;> norm_num
lemma uu_sq : uu^2 = 2+s5 := by rw [uu, Real.sq_sqrt]; rw [s5]; positivity

lemma s2_p2 : s2^2 = 2 := s2_sq
lemma s5_p2 : s5^2 = 5 := s5_sq
lemma s2_p3 : s2^3 = 2*s2 := by
  calc s2^3 = (s2^2)^1 * s2 := by ring
       _ = 2*s2 := by rw [s2_sq]; try ring_nf
lemma s5_p3 : s5^3 = 5*s5 := by
  calc s5^3 = (s5^2)^1 * s5 := by ring
       _ = 5*s5 := by rw [s5_sq]; try ring_nf
lemma s2_p4 : s2^4 = 4 := by
  calc s2^4 = (s2^2)^2 := by ring
       _ = 4 := by rw [s2_sq]; try ring_nf
lemma s5_p4 : s5^4 = 25 := by
  calc s5^4 = (s5^2)^2 := by ring
       _ = 25 := by rw [s5_sq]; try ring_nf
lemma s2_p5 : s2^5 = 4*s2 := by
  calc s2^5 = (s2^2)^2 * s2 := by ring
       _ = 4*s2 := by rw [s2_sq]; try ring_nf
lemma s5_p5 : s5^5 = 25*s5 := by
  calc s5^5 = (s5^2)^2 * s5 := by ring
       _ = 25*s5 := by rw [s5_sq]; try ring_nf
lemma s2_p6 : s2^6 = 8 := by
  calc s2^6 = (s2^2)^3 := by ring
       _ = 8 := by rw [s2_sq]; try ring_nf
lemma s5_p6 : s5^6 = 125 := by
  calc s5^6 = (s5^2)^3 := by ring
       _ = 125 := by rw [s5_sq]; try ring_nf
lemma s2_p7 : s2^7 = 8*s2 := by
  calc s2^7 = (s2^2)^3 * s2 := by ring
       _ = 8*s2 := by rw [s2_sq]; try ring_nf
lemma s5_p7 : s5^7 = 125*s5 := by
  calc s5^7 = (s5^2)^3 * s5 := by ring
       _ = 125*s5 := by rw [s5_sq]; try ring_nf
lemma s2_p8 : s2^8 = 16 := by
  calc s2^8 = (s2^2)^4 := by ring
       _ = 16 := by rw [s2_sq]; try ring_nf
lemma s5_p8 : s5^8 = 625 := by
  calc s5^8 = (s5^2)^4 := by ring
       _ = 625 := by rw [s5_sq]; try ring_nf
lemma s2_p9 : s2^9 = 16*s2 := by
  calc s2^9 = (s2^2)^4 * s2 := by ring
       _ = 16*s2 := by rw [s2_sq]; try ring_nf
lemma s5_p9 : s5^9 = 625*s5 := by
  calc s5^9 = (s5^2)^4 * s5 := by ring
       _ = 625*s5 := by rw [s5_sq]; try ring_nf
lemma s2_p10 : s2^10 = 32 := by
  calc s2^10 = (s2^2)^5 := by ring
       _ = 32 := by rw [s2_sq]; try ring_nf
lemma s5_p10 : s5^10 = 3125 := by
  calc s5^10 = (s5^2)^5 := by ring
       _ = 3125 := by rw [s5_sq]; try ring_nf
lemma s2_p11 : s2^11 = 32*s2 := by
  calc s2^11 = (s2^2)^5 * s2 := by ring
       _ = 32*s2 := by rw [s2_sq]; try ring_nf
lemma s5_p11 : s5^11 = 3125*s5 := by
  calc s5^11 = (s5^2)^5 * s5 := by ring
       _ = 3125*s5 := by rw [s5_sq]; try ring_nf
lemma s2_p12 : s2^12 = 64 := by
  calc s2^12 = (s2^2)^6 := by ring
       _ = 64 := by rw [s2_sq]; try ring_nf
lemma s5_p12 : s5^12 = 15625 := by
  calc s5^12 = (s5^2)^6 := by ring
       _ = 15625 := by rw [s5_sq]; try ring_nf
lemma uu_p2 : uu^2 = 2+s5 := uu_sq
lemma uu_p3 : uu^3 = (uu*(s5 + 2)) := by
  calc uu^3 = (uu^2)^1 * uu := by ring
       _ = (uu*(s5 + 2)) := by rw [uu_sq]; try ring_nf; try simp [s5_p2,s5_p3,s5_p4,s5_p5,s5_p6,s5_p7,s5_p8,s5_p9,s5_p10,s5_p11,s5_p12]; try ring_nf
lemma uu_p4 : uu^4 = 4*s5 + 9 := by
  calc uu^4 = (uu^2)^2 := by ring
       _ = 4*s5 + 9 := by rw [uu_sq]; try ring_nf; try simp [s5_p2,s5_p3,s5_p4,s5_p5,s5_p6,s5_p7,s5_p8,s5_p9,s5_p10,s5_p11,s5_p12]; try ring_nf
lemma uu_p5 : uu^5 = (uu*(4*s5 + 9)) := by
  calc uu^5 = (uu^2)^2 * uu := by ring
       _ = (uu*(4*s5 + 9)) := by rw [uu_sq]; try ring_nf; try simp [s5_p2,s5_p3,s5_p4,s5_p5,s5_p6,s5_p7,s5_p8,s5_p9,s5_p10,s5_p11,s5_p12]; try ring_nf
lemma uu_p6 : uu^6 = 17*s5 + 38 := by
  calc uu^6 = (uu^2)^3 := by ring
       _ = 17*s5 + 38 := by rw [uu_sq]; try ring_nf; try simp [s5_p2,s5_p3,s5_p4,s5_p5,s5_p6,s5_p7,s5_p8,s5_p9,s5_p10,s5_p11,s5_p12]; try ring_nf
lemma uu_p7 : uu^7 = (uu*(17*s5 + 38)) := by
  calc uu^7 = (uu^2)^3 * uu := by ring
       _ = (uu*(17*s5 + 38)) := by rw [uu_sq]; try ring_nf; try simp [s5_p2,s5_p3,s5_p4,s5_p5,s5_p6,s5_p7,s5_p8,s5_p9,s5_p10,s5_p11,s5_p12]; try ring_nf
lemma uu_p8 : uu^8 = 72*s5 + 161 := by
  calc uu^8 = (uu^2)^4 := by ring
       _ = 72*s5 + 161 := by rw [uu_sq]; try ring_nf; try simp [s5_p2,s5_p3,s5_p4,s5_p5,s5_p6,s5_p7,s5_p8,s5_p9,s5_p10,s5_p11,s5_p12]; try ring_nf
lemma uu_p9 : uu^9 = (uu*(72*s5 + 161)) := by
  calc uu^9 = (uu^2)^4 * uu := by ring
       _ = (uu*(72*s5 + 161)) := by rw [uu_sq]; try ring_nf; try simp [s5_p2,s5_p3,s5_p4,s5_p5,s5_p6,s5_p7,s5_p8,s5_p9,s5_p10,s5_p11,s5_p12]; try ring_nf
lemma uu_p10 : uu^10 = 305*s5 + 682 := by
  calc uu^10 = (uu^2)^5 := by ring
       _ = 305*s5 + 682 := by rw [uu_sq]; try ring_nf; try simp [s5_p2,s5_p3,s5_p4,s5_p5,s5_p6,s5_p7,s5_p8,s5_p9,s5_p10,s5_p11,s5_p12]; try ring_nf
lemma uu_p11 : uu^11 = (uu*(305*s5 + 682)) := by
  calc uu^11 = (uu^2)^5 * uu := by ring
       _ = (uu*(305*s5 + 682)) := by rw [uu_sq]; try ring_nf; try simp [s5_p2,s5_p3,s5_p4,s5_p5,s5_p6,s5_p7,s5_p8,s5_p9,s5_p10,s5_p11,s5_p12]; try ring_nf
lemma uu_p12 : uu^12 = 1292*s5 + 2889 := by
  calc uu^12 = (uu^2)^6 := by ring
       _ = 1292*s5 + 2889 := by rw [uu_sq]; try ring_nf; try simp [s5_p2,s5_p3,s5_p4,s5_p5,s5_p6,s5_p7,s5_p8,s5_p9,s5_p10,s5_p11,s5_p12]; try ring_nf

example : (s5^2 : ℝ) = 5 := by simp [s5_p2]

lemma A1_r1 : A1 * (r1re^2 + r1im^2) = B2 := by
  unfold r1re r1im A1 B2 tt
  try ring_nf
  rw [s5_p2]
  try simp only [s2_p2, s5_p2, s2_p3, s5_p3, s2_p4, s5_p4, s2_p5, s5_p5, s2_p6, s5_p6, s2_p7, s5_p7, s2_p8, s5_p8, s2_p9, s5_p9, s2_p10, s5_p10, s2_p11, s5_p11, s2_p12, s5_p12, uu_p2, uu_p3, uu_p4, uu_p5, uu_p6, uu_p7, uu_p8, uu_p9, uu_p10, uu_p11, uu_p12]
  try ring_nf
  try simp only [s2_p2, s5_p2, s2_p3, s5_p3, s2_p4, s5_p4, s2_p5, s5_p5, s2_p6, s5_p6, s2_p7, s5_p7, s2_p8, s5_p8, s2_p9, s5_p9, s2_p10, s5_p10, s2_p11, s5_p11, s2_p12, s5_p12, uu_p2, uu_p3, uu_p4, uu_p5, uu_p6, uu_p7, uu_p8, uu_p9, uu_p10, uu_p11, uu_p12]
  try ring_nf
  try simp only [s2_p2, s5_p2, s2_p3, s5_p3, s2_p4, s5_p4, s2_p5, s5_p5, s2_p6, s5_p6, s2_p7, s5_p7, s2_p8, s5_p8, s2_p9, s5_p9, s2_p10, s5_p10, s2_p11, s5_p11, s2_p12, s5_p12, uu_p2, uu_p3, uu_p4, uu_p5, uu_p6, uu_p7, uu_p8, uu_p9, uu_p10, uu_p11, uu_p12]
  try ring_nf

lemma A1_r3 : A1 * (r3re^2 + r3im^2) = B4 := by
  unfold r3re r3im A1 B4 tt
  try ring_nf
  try simp only [s2_p2, s5_p2, s2_p3, s5_p3, s2_p4, s5_p4, s2_p5, s5_p5, s2_p6, s5_p6, s2_p7, s5_p7, s2_p8, s5_p8, s2_p9, s5_p9, s2_p10, s5_p10, s2_p11, s5_p11, s2_p12, s5_p12, uu_p2, uu_p3, uu_p4, uu_p5, uu_p6, uu_p7, uu_p8, uu_p9, uu_p10, uu_p11, uu_p12]
  try ring_nf
  try simp only [s2_p2, s5_p2, s2_p3, s5_p3, s2_p4, s5_p4, s2_p5, s5_p5, s2_p6, s5_p6, s2_p7, s5_p7, s2_p8, s5_p8, s2_p9, s5_p9, s2_p10, s5_p10, s2_p11, s5_p11, s2_p12, s5_p12, uu_p2, uu_p3, uu_p4, uu_p5, uu_p6, uu_p7, uu_p8, uu_p9, uu_p10, uu_p11, uu_p12]
  try ring_nf
  try simp only [s2_p2, s5_p2, s2_p3, s5_p3, s2_p4, s5_p4, s2_p5, s5_p5, s2_p6, s5_p6, s2_p7, s5_p7, s2_p8, s5_p8, s2_p9, s5_p9, s2_p10, s5_p10, s2_p11, s5_p11, s2_p12, s5_p12, uu_p2, uu_p3, uu_p4, uu_p5, uu_p6, uu_p7, uu_p8, uu_p9, uu_p10, uu_p11, uu_p12]
  try ring_nf

lemma A1_shift : A1 * (s2-1)^2 = A3 := by
  unfold A1 A3
  try ring_nf
  try simp only [s2_p2, s5_p2, s2_p3, s5_p3, s2_p4, s5_p4, s2_p5, s5_p5, s2_p6, s5_p6, s2_p7, s5_p7, s2_p8, s5_p8, s2_p9, s5_p9, s2_p10, s5_p10, s2_p11, s5_p11, s2_p12, s5_p12, uu_p2, uu_p3, uu_p4, uu_p5, uu_p6, uu_p7, uu_p8, uu_p9, uu_p10, uu_p11, uu_p12]
  try ring_nf
  try simp only [s2_p2, s5_p2, s2_p3, s5_p3, s2_p4, s5_p4, s2_p5, s5_p5, s2_p6, s5_p6, s2_p7, s5_p7, s2_p8, s5_p8, s2_p9, s5_p9, s2_p10, s5_p10, s2_p11, s5_p11, s2_p12, s5_p12, uu_p2, uu_p3, uu_p4, uu_p5, uu_p6, uu_p7, uu_p8, uu_p9, uu_p10, uu_p11, uu_p12]
  try ring_nf
  try simp only [s2_p2, s5_p2, s2_p3, s5_p3, s2_p4, s5_p4, s2_p5, s5_p5, s2_p6, s5_p6, s2_p7, s5_p7, s2_p8, s5_p8, s2_p9, s5_p9, s2_p10, s5_p10, s2_p11, s5_p11, s2_p12, s5_p12, uu_p2, uu_p3, uu_p4, uu_p5, uu_p6, uu_p7, uu_p8, uu_p9, uu_p10, uu_p11, uu_p12]
  try ring_nf

lemma A1_sum : A1 + A3 + B2 + B4 = 1 := by
  unfold A1 A3 B2 B4 tt
  try ring_nf
  try simp only [s2_p2, s5_p2, s2_p3, s5_p3, s2_p4, s5_p4, s2_p5, s5_p5, s2_p6, s5_p6, s2_p7, s5_p7, s2_p8, s5_p8, s2_p9, s5_p9, s2_p10, s5_p10, s2_p11, s5_p11, s2_p12, s5_p12, uu_p2, uu_p3, uu_p4, uu_p5, uu_p6, uu_p7, uu_p8, uu_p9, uu_p10, uu_p11, uu_p12]
  try ring_nf
  try simp only [s2_p2, s5_p2, s2_p3, s5_p3, s2_p4, s5_p4, s2_p5, s5_p5, s2_p6, s5_p6, s2_p7, s5_p7, s2_p8, s5_p8, s2_p9, s5_p9, s2_p10, s5_p10, s2_p11, s5_p11, s2_p12, s5_p12, uu_p2, uu_p3, uu_p4, uu_p5, uu_p6, uu_p7, uu_p8, uu_p9, uu_p10, uu_p11, uu_p12]
  try ring_nf
  try simp only [s2_p2, s5_p2, s2_p3, s5_p3, s2_p4, s5_p4, s2_p5, s5_p5, s2_p6, s5_p6, s2_p7, s5_p7, s2_p8, s5_p8, s2_p9, s5_p9, s2_p10, s5_p10, s2_p11, s5_p11, s2_p12, s5_p12, uu_p2, uu_p3, uu_p4, uu_p5, uu_p6, uu_p7, uu_p8, uu_p9, uu_p10, uu_p11, uu_p12]
  try ring_nf


def v : Fin 4 → ℂ := ![1, r1re + r1im * Complex.I, (s2-1) * Complex.I, r3re + r3im * Complex.I]

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
lemma omega4 : Millennium.SIC_POVM_Stark.omega_d 4 = Complex.I := by
  rw [Millennium.SIC_POVM_Stark.omega_d]; norm_num
  rw [show (2 * Real.pi * Complex.I / (4:ℂ)) = (Real.pi / 2 : ℂ) * Complex.I by ring]
  apply Complex.ext
  · simp [Complex.exp_ofReal_mul_I_re, Real.cos_pi_div_two]
  · simp [Complex.exp_ofReal_mul_I_im, Real.sin_pi_div_two]


lemma A1_nonneg : 0 ≤ A1 := by
  unfold A1 s2 s5
  have hs2sq : (Real.sqrt 2)^2 = 2 := by rw [Real.sq_sqrt] <;> norm_num
  have hs5sq : (Real.sqrt 5)^2 = 5 := by rw [Real.sq_sqrt] <;> norm_num
  have hs10sq : (Real.sqrt 2 * Real.sqrt 5)^2 = 10 := by
    rw [mul_pow, hs2sq, hs5sq]; norm_num
  have hs2nn : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have hs5nn : 0 ≤ Real.sqrt 5 := Real.sqrt_nonneg 5
  have hs10nn : 0 ≤ Real.sqrt 2 * Real.sqrt 5 := mul_nonneg hs2nn hs5nn
  nlinarith [hs2sq, hs5sq, hs10sq, hs2nn, hs5nn, hs10nn]
lemma d4_overlap_0_1 : 5 * Complex.normSq (Millennium.SIC_POVM_Stark.wh_inner 4 v
    (Millennium.SIC_POVM_Stark.D_ah 4 0 1 0 v)) * A1^2 = 1 := by
  simp [v, Millennium.SIC_POVM_Stark.D_ah, Millennium.SIC_POVM_Stark.X_d,
    Millennium.SIC_POVM_Stark.Z_d, omega4, Millennium.SIC_POVM_Stark.wh_inner,
    Fin.sum_univ_four]
  rw [Complex.normSq_apply]
  ring_nf
  simp [I2,I3,I4,I5, ← Complex.ofReal_pow]
  ring_nf
  unfold r1re r1im r3re r3im A1 tt
  ring_nf
  simp only [s2_p2, s5_p2, s2_p3, s5_p3, s2_p4, s5_p4, s2_p5, s5_p5, s2_p6, s5_p6, s2_p7, s5_p7, s2_p8, s5_p8, s2_p9, s5_p9, s2_p10, s5_p10, s2_p11, s5_p11, s2_p12, s5_p12, uu_p2, uu_p3, uu_p4, uu_p5, uu_p6, uu_p7, uu_p8, uu_p9, uu_p10, uu_p11, uu_p12]
  ring_nf
  try simp only [s2_p2, s5_p2, s2_p3, s5_p3, s2_p4, s5_p4, s2_p5, s5_p5, s2_p6, s5_p6, s2_p7, s5_p7, s2_p8, s5_p8, s2_p9, s5_p9, s2_p10, s5_p10, s2_p11, s5_p11, s2_p12, s5_p12, uu_p2, uu_p3, uu_p4, uu_p5, uu_p6, uu_p7, uu_p8, uu_p9, uu_p10, uu_p11, uu_p12]
  try ring_nf
  try simp only [s2_p2, s5_p2, s2_p3, s5_p3, s2_p4, s5_p4, s2_p5, s5_p5, s2_p6, s5_p6, s2_p7, s5_p7, s2_p8, s5_p8, s2_p9, s5_p9, s2_p10, s5_p10, s2_p11, s5_p11, s2_p12, s5_p12, uu_p2, uu_p3, uu_p4, uu_p5, uu_p6, uu_p7, uu_p8, uu_p9, uu_p10, uu_p11, uu_p12]
  try ring_nf

lemma d4_overlap_0_2 : 5 * Complex.normSq (Millennium.SIC_POVM_Stark.wh_inner 4 v
    (Millennium.SIC_POVM_Stark.D_ah 4 0 2 0 v)) * A1^2 = 1 := by
  simp [v, Millennium.SIC_POVM_Stark.D_ah, Millennium.SIC_POVM_Stark.X_d,
    Millennium.SIC_POVM_Stark.Z_d, omega4, Millennium.SIC_POVM_Stark.wh_inner,
    Fin.sum_univ_four]
  rw [Complex.normSq_apply]
  ring_nf
  simp [I2,I3,I4,I5, ← Complex.ofReal_pow]
  ring_nf
  unfold r1re r1im r3re r3im A1 tt
  ring_nf
  simp only [s2_p2, s5_p2, s2_p3, s5_p3, s2_p4, s5_p4, s2_p5, s5_p5, s2_p6, s5_p6, s2_p7, s5_p7, s2_p8, s5_p8, s2_p9, s5_p9, s2_p10, s5_p10, s2_p11, s5_p11, s2_p12, s5_p12, uu_p2, uu_p3, uu_p4, uu_p5, uu_p6, uu_p7, uu_p8, uu_p9, uu_p10, uu_p11, uu_p12]
  ring_nf
  try simp only [s2_p2, s5_p2, s2_p3, s5_p3, s2_p4, s5_p4, s2_p5, s5_p5, s2_p6, s5_p6, s2_p7, s5_p7, s2_p8, s5_p8, s2_p9, s5_p9, s2_p10, s5_p10, s2_p11, s5_p11, s2_p12, s5_p12, uu_p2, uu_p3, uu_p4, uu_p5, uu_p6, uu_p7, uu_p8, uu_p9, uu_p10, uu_p11, uu_p12]
  try ring_nf
  try simp only [s2_p2, s5_p2, s2_p3, s5_p3, s2_p4, s5_p4, s2_p5, s5_p5, s2_p6, s5_p6, s2_p7, s5_p7, s2_p8, s5_p8, s2_p9, s5_p9, s2_p10, s5_p10, s2_p11, s5_p11, s2_p12, s5_p12, uu_p2, uu_p3, uu_p4, uu_p5, uu_p6, uu_p7, uu_p8, uu_p9, uu_p10, uu_p11, uu_p12]
  try ring_nf

lemma d4_overlap_0_3 : 5 * Complex.normSq (Millennium.SIC_POVM_Stark.wh_inner 4 v
    (Millennium.SIC_POVM_Stark.D_ah 4 0 3 0 v)) * A1^2 = 1 := by
  simp [v, Millennium.SIC_POVM_Stark.D_ah, Millennium.SIC_POVM_Stark.X_d,
    Millennium.SIC_POVM_Stark.Z_d, omega4, Millennium.SIC_POVM_Stark.wh_inner,
    Fin.sum_univ_four]
  rw [Complex.normSq_apply]
  ring_nf
  simp [I2,I3,I4,I5, ← Complex.ofReal_pow]
  ring_nf
  unfold r1re r1im r3re r3im A1 tt
  ring_nf
  simp only [s2_p2, s5_p2, s2_p3, s5_p3, s2_p4, s5_p4, s2_p5, s5_p5, s2_p6, s5_p6, s2_p7, s5_p7, s2_p8, s5_p8, s2_p9, s5_p9, s2_p10, s5_p10, s2_p11, s5_p11, s2_p12, s5_p12, uu_p2, uu_p3, uu_p4, uu_p5, uu_p6, uu_p7, uu_p8, uu_p9, uu_p10, uu_p11, uu_p12]
  ring_nf
  try simp only [s2_p2, s5_p2, s2_p3, s5_p3, s2_p4, s5_p4, s2_p5, s5_p5, s2_p6, s5_p6, s2_p7, s5_p7, s2_p8, s5_p8, s2_p9, s5_p9, s2_p10, s5_p10, s2_p11, s5_p11, s2_p12, s5_p12, uu_p2, uu_p3, uu_p4, uu_p5, uu_p6, uu_p7, uu_p8, uu_p9, uu_p10, uu_p11, uu_p12]
  try ring_nf
  try simp only [s2_p2, s5_p2, s2_p3, s5_p3, s2_p4, s5_p4, s2_p5, s5_p5, s2_p6, s5_p6, s2_p7, s5_p7, s2_p8, s5_p8, s2_p9, s5_p9, s2_p10, s5_p10, s2_p11, s5_p11, s2_p12, s5_p12, uu_p2, uu_p3, uu_p4, uu_p5, uu_p6, uu_p7, uu_p8, uu_p9, uu_p10, uu_p11, uu_p12]
  try ring_nf

lemma d4_overlap_1_0 : 5 * Complex.normSq (Millennium.SIC_POVM_Stark.wh_inner 4 v
    (Millennium.SIC_POVM_Stark.D_ah 4 1 0 0 v)) * A1^2 = 1 := by
  simp [v, Millennium.SIC_POVM_Stark.D_ah, Millennium.SIC_POVM_Stark.X_d,
    Millennium.SIC_POVM_Stark.Z_d, omega4, Millennium.SIC_POVM_Stark.wh_inner,
    Fin.sum_univ_four]
  rw [Complex.normSq_apply]
  ring_nf
  simp [I2,I3,I4,I5, ← Complex.ofReal_pow]
  ring_nf
  unfold r1re r1im r3re r3im A1 tt
  ring_nf
  simp only [s2_p2, s5_p2, s2_p3, s5_p3, s2_p4, s5_p4, s2_p5, s5_p5, s2_p6, s5_p6, s2_p7, s5_p7, s2_p8, s5_p8, s2_p9, s5_p9, s2_p10, s5_p10, s2_p11, s5_p11, s2_p12, s5_p12, uu_p2, uu_p3, uu_p4, uu_p5, uu_p6, uu_p7, uu_p8, uu_p9, uu_p10, uu_p11, uu_p12]
  ring_nf
  try simp only [s2_p2, s5_p2, s2_p3, s5_p3, s2_p4, s5_p4, s2_p5, s5_p5, s2_p6, s5_p6, s2_p7, s5_p7, s2_p8, s5_p8, s2_p9, s5_p9, s2_p10, s5_p10, s2_p11, s5_p11, s2_p12, s5_p12, uu_p2, uu_p3, uu_p4, uu_p5, uu_p6, uu_p7, uu_p8, uu_p9, uu_p10, uu_p11, uu_p12]
  try ring_nf
  try simp only [s2_p2, s5_p2, s2_p3, s5_p3, s2_p4, s5_p4, s2_p5, s5_p5, s2_p6, s5_p6, s2_p7, s5_p7, s2_p8, s5_p8, s2_p9, s5_p9, s2_p10, s5_p10, s2_p11, s5_p11, s2_p12, s5_p12, uu_p2, uu_p3, uu_p4, uu_p5, uu_p6, uu_p7, uu_p8, uu_p9, uu_p10, uu_p11, uu_p12]
  try ring_nf

lemma d4_overlap_1_1 : 5 * Complex.normSq (Millennium.SIC_POVM_Stark.wh_inner 4 v
    (Millennium.SIC_POVM_Stark.D_ah 4 1 1 0 v)) * A1^2 = 1 := by
  simp [v, Millennium.SIC_POVM_Stark.D_ah, Millennium.SIC_POVM_Stark.X_d,
    Millennium.SIC_POVM_Stark.Z_d, omega4, Millennium.SIC_POVM_Stark.wh_inner,
    Fin.sum_univ_four]
  rw [Complex.normSq_apply]
  ring_nf
  simp [I2,I3,I4,I5, ← Complex.ofReal_pow]
  ring_nf
  unfold r1re r1im r3re r3im A1 tt
  ring_nf
  simp only [s2_p2, s5_p2, s2_p3, s5_p3, s2_p4, s5_p4, s2_p5, s5_p5, s2_p6, s5_p6, s2_p7, s5_p7, s2_p8, s5_p8, s2_p9, s5_p9, s2_p10, s5_p10, s2_p11, s5_p11, s2_p12, s5_p12, uu_p2, uu_p3, uu_p4, uu_p5, uu_p6, uu_p7, uu_p8, uu_p9, uu_p10, uu_p11, uu_p12]
  ring_nf
  try simp only [s2_p2, s5_p2, s2_p3, s5_p3, s2_p4, s5_p4, s2_p5, s5_p5, s2_p6, s5_p6, s2_p7, s5_p7, s2_p8, s5_p8, s2_p9, s5_p9, s2_p10, s5_p10, s2_p11, s5_p11, s2_p12, s5_p12, uu_p2, uu_p3, uu_p4, uu_p5, uu_p6, uu_p7, uu_p8, uu_p9, uu_p10, uu_p11, uu_p12]
  try ring_nf
  try simp only [s2_p2, s5_p2, s2_p3, s5_p3, s2_p4, s5_p4, s2_p5, s5_p5, s2_p6, s5_p6, s2_p7, s5_p7, s2_p8, s5_p8, s2_p9, s5_p9, s2_p10, s5_p10, s2_p11, s5_p11, s2_p12, s5_p12, uu_p2, uu_p3, uu_p4, uu_p5, uu_p6, uu_p7, uu_p8, uu_p9, uu_p10, uu_p11, uu_p12]
  try ring_nf

lemma d4_overlap_1_2 : 5 * Complex.normSq (Millennium.SIC_POVM_Stark.wh_inner 4 v
    (Millennium.SIC_POVM_Stark.D_ah 4 1 2 0 v)) * A1^2 = 1 := by
  simp [v, Millennium.SIC_POVM_Stark.D_ah, Millennium.SIC_POVM_Stark.X_d,
    Millennium.SIC_POVM_Stark.Z_d, omega4, Millennium.SIC_POVM_Stark.wh_inner,
    Fin.sum_univ_four]
  rw [Complex.normSq_apply]
  ring_nf
  simp [I2,I3,I4,I5, ← Complex.ofReal_pow]
  ring_nf
  unfold r1re r1im r3re r3im A1 tt
  ring_nf
  simp only [s2_p2, s5_p2, s2_p3, s5_p3, s2_p4, s5_p4, s2_p5, s5_p5, s2_p6, s5_p6, s2_p7, s5_p7, s2_p8, s5_p8, s2_p9, s5_p9, s2_p10, s5_p10, s2_p11, s5_p11, s2_p12, s5_p12, uu_p2, uu_p3, uu_p4, uu_p5, uu_p6, uu_p7, uu_p8, uu_p9, uu_p10, uu_p11, uu_p12]
  ring_nf
  try simp only [s2_p2, s5_p2, s2_p3, s5_p3, s2_p4, s5_p4, s2_p5, s5_p5, s2_p6, s5_p6, s2_p7, s5_p7, s2_p8, s5_p8, s2_p9, s5_p9, s2_p10, s5_p10, s2_p11, s5_p11, s2_p12, s5_p12, uu_p2, uu_p3, uu_p4, uu_p5, uu_p6, uu_p7, uu_p8, uu_p9, uu_p10, uu_p11, uu_p12]
  try ring_nf
  try simp only [s2_p2, s5_p2, s2_p3, s5_p3, s2_p4, s5_p4, s2_p5, s5_p5, s2_p6, s5_p6, s2_p7, s5_p7, s2_p8, s5_p8, s2_p9, s5_p9, s2_p10, s5_p10, s2_p11, s5_p11, s2_p12, s5_p12, uu_p2, uu_p3, uu_p4, uu_p5, uu_p6, uu_p7, uu_p8, uu_p9, uu_p10, uu_p11, uu_p12]
  try ring_nf

lemma d4_overlap_1_3 : 5 * Complex.normSq (Millennium.SIC_POVM_Stark.wh_inner 4 v
    (Millennium.SIC_POVM_Stark.D_ah 4 1 3 0 v)) * A1^2 = 1 := by
  simp [v, Millennium.SIC_POVM_Stark.D_ah, Millennium.SIC_POVM_Stark.X_d,
    Millennium.SIC_POVM_Stark.Z_d, omega4, Millennium.SIC_POVM_Stark.wh_inner,
    Fin.sum_univ_four]
  rw [Complex.normSq_apply]
  ring_nf
  simp [I2,I3,I4,I5, ← Complex.ofReal_pow]
  ring_nf
  unfold r1re r1im r3re r3im A1 tt
  ring_nf
  simp only [s2_p2, s5_p2, s2_p3, s5_p3, s2_p4, s5_p4, s2_p5, s5_p5, s2_p6, s5_p6, s2_p7, s5_p7, s2_p8, s5_p8, s2_p9, s5_p9, s2_p10, s5_p10, s2_p11, s5_p11, s2_p12, s5_p12, uu_p2, uu_p3, uu_p4, uu_p5, uu_p6, uu_p7, uu_p8, uu_p9, uu_p10, uu_p11, uu_p12]
  ring_nf
  try simp only [s2_p2, s5_p2, s2_p3, s5_p3, s2_p4, s5_p4, s2_p5, s5_p5, s2_p6, s5_p6, s2_p7, s5_p7, s2_p8, s5_p8, s2_p9, s5_p9, s2_p10, s5_p10, s2_p11, s5_p11, s2_p12, s5_p12, uu_p2, uu_p3, uu_p4, uu_p5, uu_p6, uu_p7, uu_p8, uu_p9, uu_p10, uu_p11, uu_p12]
  try ring_nf
  try simp only [s2_p2, s5_p2, s2_p3, s5_p3, s2_p4, s5_p4, s2_p5, s5_p5, s2_p6, s5_p6, s2_p7, s5_p7, s2_p8, s5_p8, s2_p9, s5_p9, s2_p10, s5_p10, s2_p11, s5_p11, s2_p12, s5_p12, uu_p2, uu_p3, uu_p4, uu_p5, uu_p6, uu_p7, uu_p8, uu_p9, uu_p10, uu_p11, uu_p12]
  try ring_nf

lemma d4_overlap_2_0 : 5 * Complex.normSq (Millennium.SIC_POVM_Stark.wh_inner 4 v
    (Millennium.SIC_POVM_Stark.D_ah 4 2 0 0 v)) * A1^2 = 1 := by
  simp [v, Millennium.SIC_POVM_Stark.D_ah, Millennium.SIC_POVM_Stark.X_d,
    Millennium.SIC_POVM_Stark.Z_d, omega4, Millennium.SIC_POVM_Stark.wh_inner,
    Fin.sum_univ_four]
  rw [Complex.normSq_apply]
  ring_nf
  simp [I2,I3,I4,I5, ← Complex.ofReal_pow]
  ring_nf
  unfold r1re r1im r3re r3im A1 tt
  ring_nf
  simp only [s2_p2, s5_p2, s2_p3, s5_p3, s2_p4, s5_p4, s2_p5, s5_p5, s2_p6, s5_p6, s2_p7, s5_p7, s2_p8, s5_p8, s2_p9, s5_p9, s2_p10, s5_p10, s2_p11, s5_p11, s2_p12, s5_p12, uu_p2, uu_p3, uu_p4, uu_p5, uu_p6, uu_p7, uu_p8, uu_p9, uu_p10, uu_p11, uu_p12]
  ring_nf
  try simp only [s2_p2, s5_p2, s2_p3, s5_p3, s2_p4, s5_p4, s2_p5, s5_p5, s2_p6, s5_p6, s2_p7, s5_p7, s2_p8, s5_p8, s2_p9, s5_p9, s2_p10, s5_p10, s2_p11, s5_p11, s2_p12, s5_p12, uu_p2, uu_p3, uu_p4, uu_p5, uu_p6, uu_p7, uu_p8, uu_p9, uu_p10, uu_p11, uu_p12]
  try ring_nf
  try simp only [s2_p2, s5_p2, s2_p3, s5_p3, s2_p4, s5_p4, s2_p5, s5_p5, s2_p6, s5_p6, s2_p7, s5_p7, s2_p8, s5_p8, s2_p9, s5_p9, s2_p10, s5_p10, s2_p11, s5_p11, s2_p12, s5_p12, uu_p2, uu_p3, uu_p4, uu_p5, uu_p6, uu_p7, uu_p8, uu_p9, uu_p10, uu_p11, uu_p12]
  try ring_nf

lemma d4_overlap_2_1 : 5 * Complex.normSq (Millennium.SIC_POVM_Stark.wh_inner 4 v
    (Millennium.SIC_POVM_Stark.D_ah 4 2 1 0 v)) * A1^2 = 1 := by
  simp [v, Millennium.SIC_POVM_Stark.D_ah, Millennium.SIC_POVM_Stark.X_d,
    Millennium.SIC_POVM_Stark.Z_d, omega4, Millennium.SIC_POVM_Stark.wh_inner,
    Fin.sum_univ_four]
  rw [Complex.normSq_apply]
  ring_nf
  simp [I2,I3,I4,I5, ← Complex.ofReal_pow]
  ring_nf
  unfold r1re r1im r3re r3im A1 tt
  ring_nf
  simp only [s2_p2, s5_p2, s2_p3, s5_p3, s2_p4, s5_p4, s2_p5, s5_p5, s2_p6, s5_p6, s2_p7, s5_p7, s2_p8, s5_p8, s2_p9, s5_p9, s2_p10, s5_p10, s2_p11, s5_p11, s2_p12, s5_p12, uu_p2, uu_p3, uu_p4, uu_p5, uu_p6, uu_p7, uu_p8, uu_p9, uu_p10, uu_p11, uu_p12]
  ring_nf
  try simp only [s2_p2, s5_p2, s2_p3, s5_p3, s2_p4, s5_p4, s2_p5, s5_p5, s2_p6, s5_p6, s2_p7, s5_p7, s2_p8, s5_p8, s2_p9, s5_p9, s2_p10, s5_p10, s2_p11, s5_p11, s2_p12, s5_p12, uu_p2, uu_p3, uu_p4, uu_p5, uu_p6, uu_p7, uu_p8, uu_p9, uu_p10, uu_p11, uu_p12]
  try ring_nf
  try simp only [s2_p2, s5_p2, s2_p3, s5_p3, s2_p4, s5_p4, s2_p5, s5_p5, s2_p6, s5_p6, s2_p7, s5_p7, s2_p8, s5_p8, s2_p9, s5_p9, s2_p10, s5_p10, s2_p11, s5_p11, s2_p12, s5_p12, uu_p2, uu_p3, uu_p4, uu_p5, uu_p6, uu_p7, uu_p8, uu_p9, uu_p10, uu_p11, uu_p12]
  try ring_nf

lemma d4_overlap_2_2 : 5 * Complex.normSq (Millennium.SIC_POVM_Stark.wh_inner 4 v
    (Millennium.SIC_POVM_Stark.D_ah 4 2 2 0 v)) * A1^2 = 1 := by
  simp [v, Millennium.SIC_POVM_Stark.D_ah, Millennium.SIC_POVM_Stark.X_d,
    Millennium.SIC_POVM_Stark.Z_d, omega4, Millennium.SIC_POVM_Stark.wh_inner,
    Fin.sum_univ_four]
  rw [Complex.normSq_apply]
  ring_nf
  simp [I2,I3,I4,I5, ← Complex.ofReal_pow]
  ring_nf
  unfold r1re r1im r3re r3im A1 tt
  ring_nf
  simp only [s2_p2, s5_p2, s2_p3, s5_p3, s2_p4, s5_p4, s2_p5, s5_p5, s2_p6, s5_p6, s2_p7, s5_p7, s2_p8, s5_p8, s2_p9, s5_p9, s2_p10, s5_p10, s2_p11, s5_p11, s2_p12, s5_p12, uu_p2, uu_p3, uu_p4, uu_p5, uu_p6, uu_p7, uu_p8, uu_p9, uu_p10, uu_p11, uu_p12]
  ring_nf
  try simp only [s2_p2, s5_p2, s2_p3, s5_p3, s2_p4, s5_p4, s2_p5, s5_p5, s2_p6, s5_p6, s2_p7, s5_p7, s2_p8, s5_p8, s2_p9, s5_p9, s2_p10, s5_p10, s2_p11, s5_p11, s2_p12, s5_p12, uu_p2, uu_p3, uu_p4, uu_p5, uu_p6, uu_p7, uu_p8, uu_p9, uu_p10, uu_p11, uu_p12]
  try ring_nf
  try simp only [s2_p2, s5_p2, s2_p3, s5_p3, s2_p4, s5_p4, s2_p5, s5_p5, s2_p6, s5_p6, s2_p7, s5_p7, s2_p8, s5_p8, s2_p9, s5_p9, s2_p10, s5_p10, s2_p11, s5_p11, s2_p12, s5_p12, uu_p2, uu_p3, uu_p4, uu_p5, uu_p6, uu_p7, uu_p8, uu_p9, uu_p10, uu_p11, uu_p12]
  try ring_nf

lemma d4_overlap_2_3 : 5 * Complex.normSq (Millennium.SIC_POVM_Stark.wh_inner 4 v
    (Millennium.SIC_POVM_Stark.D_ah 4 2 3 0 v)) * A1^2 = 1 := by
  simp [v, Millennium.SIC_POVM_Stark.D_ah, Millennium.SIC_POVM_Stark.X_d,
    Millennium.SIC_POVM_Stark.Z_d, omega4, Millennium.SIC_POVM_Stark.wh_inner,
    Fin.sum_univ_four]
  rw [Complex.normSq_apply]
  ring_nf
  simp [I2,I3,I4,I5, ← Complex.ofReal_pow]
  ring_nf
  unfold r1re r1im r3re r3im A1 tt
  ring_nf
  simp only [s2_p2, s5_p2, s2_p3, s5_p3, s2_p4, s5_p4, s2_p5, s5_p5, s2_p6, s5_p6, s2_p7, s5_p7, s2_p8, s5_p8, s2_p9, s5_p9, s2_p10, s5_p10, s2_p11, s5_p11, s2_p12, s5_p12, uu_p2, uu_p3, uu_p4, uu_p5, uu_p6, uu_p7, uu_p8, uu_p9, uu_p10, uu_p11, uu_p12]
  ring_nf
  try simp only [s2_p2, s5_p2, s2_p3, s5_p3, s2_p4, s5_p4, s2_p5, s5_p5, s2_p6, s5_p6, s2_p7, s5_p7, s2_p8, s5_p8, s2_p9, s5_p9, s2_p10, s5_p10, s2_p11, s5_p11, s2_p12, s5_p12, uu_p2, uu_p3, uu_p4, uu_p5, uu_p6, uu_p7, uu_p8, uu_p9, uu_p10, uu_p11, uu_p12]
  try ring_nf
  try simp only [s2_p2, s5_p2, s2_p3, s5_p3, s2_p4, s5_p4, s2_p5, s5_p5, s2_p6, s5_p6, s2_p7, s5_p7, s2_p8, s5_p8, s2_p9, s5_p9, s2_p10, s5_p10, s2_p11, s5_p11, s2_p12, s5_p12, uu_p2, uu_p3, uu_p4, uu_p5, uu_p6, uu_p7, uu_p8, uu_p9, uu_p10, uu_p11, uu_p12]
  try ring_nf

lemma d4_overlap_3_0 : 5 * Complex.normSq (Millennium.SIC_POVM_Stark.wh_inner 4 v
    (Millennium.SIC_POVM_Stark.D_ah 4 3 0 0 v)) * A1^2 = 1 := by
  simp [v, Millennium.SIC_POVM_Stark.D_ah, Millennium.SIC_POVM_Stark.X_d,
    Millennium.SIC_POVM_Stark.Z_d, omega4, Millennium.SIC_POVM_Stark.wh_inner,
    Fin.sum_univ_four]
  rw [Complex.normSq_apply]
  ring_nf
  simp [I2,I3,I4,I5, ← Complex.ofReal_pow]
  ring_nf
  unfold r1re r1im r3re r3im A1 tt
  ring_nf
  simp only [s2_p2, s5_p2, s2_p3, s5_p3, s2_p4, s5_p4, s2_p5, s5_p5, s2_p6, s5_p6, s2_p7, s5_p7, s2_p8, s5_p8, s2_p9, s5_p9, s2_p10, s5_p10, s2_p11, s5_p11, s2_p12, s5_p12, uu_p2, uu_p3, uu_p4, uu_p5, uu_p6, uu_p7, uu_p8, uu_p9, uu_p10, uu_p11, uu_p12]
  ring_nf
  try simp only [s2_p2, s5_p2, s2_p3, s5_p3, s2_p4, s5_p4, s2_p5, s5_p5, s2_p6, s5_p6, s2_p7, s5_p7, s2_p8, s5_p8, s2_p9, s5_p9, s2_p10, s5_p10, s2_p11, s5_p11, s2_p12, s5_p12, uu_p2, uu_p3, uu_p4, uu_p5, uu_p6, uu_p7, uu_p8, uu_p9, uu_p10, uu_p11, uu_p12]
  try ring_nf
  try simp only [s2_p2, s5_p2, s2_p3, s5_p3, s2_p4, s5_p4, s2_p5, s5_p5, s2_p6, s5_p6, s2_p7, s5_p7, s2_p8, s5_p8, s2_p9, s5_p9, s2_p10, s5_p10, s2_p11, s5_p11, s2_p12, s5_p12, uu_p2, uu_p3, uu_p4, uu_p5, uu_p6, uu_p7, uu_p8, uu_p9, uu_p10, uu_p11, uu_p12]
  try ring_nf

lemma d4_overlap_3_1 : 5 * Complex.normSq (Millennium.SIC_POVM_Stark.wh_inner 4 v
    (Millennium.SIC_POVM_Stark.D_ah 4 3 1 0 v)) * A1^2 = 1 := by
  simp [v, Millennium.SIC_POVM_Stark.D_ah, Millennium.SIC_POVM_Stark.X_d,
    Millennium.SIC_POVM_Stark.Z_d, omega4, Millennium.SIC_POVM_Stark.wh_inner,
    Fin.sum_univ_four]
  rw [Complex.normSq_apply]
  ring_nf
  simp [I2,I3,I4,I5, ← Complex.ofReal_pow]
  ring_nf
  unfold r1re r1im r3re r3im A1 tt
  ring_nf
  simp only [s2_p2, s5_p2, s2_p3, s5_p3, s2_p4, s5_p4, s2_p5, s5_p5, s2_p6, s5_p6, s2_p7, s5_p7, s2_p8, s5_p8, s2_p9, s5_p9, s2_p10, s5_p10, s2_p11, s5_p11, s2_p12, s5_p12, uu_p2, uu_p3, uu_p4, uu_p5, uu_p6, uu_p7, uu_p8, uu_p9, uu_p10, uu_p11, uu_p12]
  ring_nf
  try simp only [s2_p2, s5_p2, s2_p3, s5_p3, s2_p4, s5_p4, s2_p5, s5_p5, s2_p6, s5_p6, s2_p7, s5_p7, s2_p8, s5_p8, s2_p9, s5_p9, s2_p10, s5_p10, s2_p11, s5_p11, s2_p12, s5_p12, uu_p2, uu_p3, uu_p4, uu_p5, uu_p6, uu_p7, uu_p8, uu_p9, uu_p10, uu_p11, uu_p12]
  try ring_nf
  try simp only [s2_p2, s5_p2, s2_p3, s5_p3, s2_p4, s5_p4, s2_p5, s5_p5, s2_p6, s5_p6, s2_p7, s5_p7, s2_p8, s5_p8, s2_p9, s5_p9, s2_p10, s5_p10, s2_p11, s5_p11, s2_p12, s5_p12, uu_p2, uu_p3, uu_p4, uu_p5, uu_p6, uu_p7, uu_p8, uu_p9, uu_p10, uu_p11, uu_p12]
  try ring_nf

lemma d4_overlap_3_2 : 5 * Complex.normSq (Millennium.SIC_POVM_Stark.wh_inner 4 v
    (Millennium.SIC_POVM_Stark.D_ah 4 3 2 0 v)) * A1^2 = 1 := by
  simp [v, Millennium.SIC_POVM_Stark.D_ah, Millennium.SIC_POVM_Stark.X_d,
    Millennium.SIC_POVM_Stark.Z_d, omega4, Millennium.SIC_POVM_Stark.wh_inner,
    Fin.sum_univ_four]
  rw [Complex.normSq_apply]
  ring_nf
  simp [I2,I3,I4,I5, ← Complex.ofReal_pow]
  ring_nf
  unfold r1re r1im r3re r3im A1 tt
  ring_nf
  simp only [s2_p2, s5_p2, s2_p3, s5_p3, s2_p4, s5_p4, s2_p5, s5_p5, s2_p6, s5_p6, s2_p7, s5_p7, s2_p8, s5_p8, s2_p9, s5_p9, s2_p10, s5_p10, s2_p11, s5_p11, s2_p12, s5_p12, uu_p2, uu_p3, uu_p4, uu_p5, uu_p6, uu_p7, uu_p8, uu_p9, uu_p10, uu_p11, uu_p12]
  ring_nf
  try simp only [s2_p2, s5_p2, s2_p3, s5_p3, s2_p4, s5_p4, s2_p5, s5_p5, s2_p6, s5_p6, s2_p7, s5_p7, s2_p8, s5_p8, s2_p9, s5_p9, s2_p10, s5_p10, s2_p11, s5_p11, s2_p12, s5_p12, uu_p2, uu_p3, uu_p4, uu_p5, uu_p6, uu_p7, uu_p8, uu_p9, uu_p10, uu_p11, uu_p12]
  try ring_nf
  try simp only [s2_p2, s5_p2, s2_p3, s5_p3, s2_p4, s5_p4, s2_p5, s5_p5, s2_p6, s5_p6, s2_p7, s5_p7, s2_p8, s5_p8, s2_p9, s5_p9, s2_p10, s5_p10, s2_p11, s5_p11, s2_p12, s5_p12, uu_p2, uu_p3, uu_p4, uu_p5, uu_p6, uu_p7, uu_p8, uu_p9, uu_p10, uu_p11, uu_p12]
  try ring_nf

lemma d4_overlap_3_3 : 5 * Complex.normSq (Millennium.SIC_POVM_Stark.wh_inner 4 v
    (Millennium.SIC_POVM_Stark.D_ah 4 3 3 0 v)) * A1^2 = 1 := by
  simp [v, Millennium.SIC_POVM_Stark.D_ah, Millennium.SIC_POVM_Stark.X_d,
    Millennium.SIC_POVM_Stark.Z_d, omega4, Millennium.SIC_POVM_Stark.wh_inner,
    Fin.sum_univ_four]
  rw [Complex.normSq_apply]
  ring_nf
  simp [I2,I3,I4,I5, ← Complex.ofReal_pow]
  ring_nf
  unfold r1re r1im r3re r3im A1 tt
  ring_nf
  simp only [s2_p2, s5_p2, s2_p3, s5_p3, s2_p4, s5_p4, s2_p5, s5_p5, s2_p6, s5_p6, s2_p7, s5_p7, s2_p8, s5_p8, s2_p9, s5_p9, s2_p10, s5_p10, s2_p11, s5_p11, s2_p12, s5_p12, uu_p2, uu_p3, uu_p4, uu_p5, uu_p6, uu_p7, uu_p8, uu_p9, uu_p10, uu_p11, uu_p12]
  ring_nf
  try simp only [s2_p2, s5_p2, s2_p3, s5_p3, s2_p4, s5_p4, s2_p5, s5_p5, s2_p6, s5_p6, s2_p7, s5_p7, s2_p8, s5_p8, s2_p9, s5_p9, s2_p10, s5_p10, s2_p11, s5_p11, s2_p12, s5_p12, uu_p2, uu_p3, uu_p4, uu_p5, uu_p6, uu_p7, uu_p8, uu_p9, uu_p10, uu_p11, uu_p12]
  try ring_nf


def psi : Fin 4 → ℂ := fun k => (Real.sqrt A1 : ℂ) * v k

lemma psi_inner_scale (a b : Fin 4) :
    Millennium.SIC_POVM_Stark.wh_inner 4 psi
        (Millennium.SIC_POVM_Stark.D_ah 4 a b 0 psi) =
      (A1 : ℂ) * Millennium.SIC_POVM_Stark.wh_inner 4 v
        (Millennium.SIC_POVM_Stark.D_ah 4 a b 0 v) := by
  simp [psi, Millennium.SIC_POVM_Stark.wh_inner, Millennium.SIC_POVM_Stark.D_ah,
    Millennium.SIC_POVM_Stark.X_d, Millennium.SIC_POVM_Stark.Z_d, omega4,
    Fin.sum_univ_four]
  ring_nf
  rw [Real.sq_sqrt A1_nonneg]

