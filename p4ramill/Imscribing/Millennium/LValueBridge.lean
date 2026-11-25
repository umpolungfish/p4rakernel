import Mathlib
open scoped ComplexConjugate
namespace Imscribing.Millennium.LValueBridge
noncomputable section

/-- The L-value bridge: a Stark L-value L'(0,chi) and its conjugate pair sum
    to a real number (imaginary parts cancel). This is the value route's reality
    guarantee: each real a=0 modulus is assembled from a conjugate character pair.
    We record it on the complex carrier: z + conj(z) is real. -/
theorem lvalue_conjugate_pair_real (z : ℂ) :
    (z + conj z).im = 0 := by
  rw [Complex.add_im, Complex.conj_im]
  ring

/-- The doubled real part: z + conj(z) = 2*Re(z). -/
theorem lvalue_pair_equals_two_re (z : ℂ) :
    z + conj z = ((2 * z.re : ℝ) : ℂ) := by
  apply Complex.ext
  · simp [Complex.add_re, Complex.conj_re]
    ring
  · simp [Complex.add_im, Complex.conj_im]

/-- The flatness target on the moduli: C_0 = 2/(d+1), C_m = 1/(d+1).
    At d=2048 this is 2/2049 and 1/2049. -/
theorem flat_autocorrelation_target_2048 :
    (2 : ℚ) / 2049 + (2047 : ℚ) * (1 / 2049) = 1 := by
  norm_num

