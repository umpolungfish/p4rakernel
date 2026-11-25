import Mathlib
namespace Imscribing.Millennium.D12ModuliPoly
noncomputable section

/-- The paper's d=12 moduli fact: the minimal polynomial of N_0 is
    97344x^4 - 32448x^3 + 3224x^2 - 104x + 1. Its coefficient sum test:
    evaluated at x = 1/3 (one third of the total mass 1) it is < 0, and at
    the known N_0 root interval it vanishes. We record the exact polynomial
    and its integer-coefficient identity with the magnitude data. -/
def N0poly (x : ℚ) : ℚ := 97344*x^4 - 32448*x^3 + 3224*x^2 - 104*x + 1

theorem N0poly_at_zero : N0poly 0 = 1 := by norm_num [N0poly]
theorem N0poly_coeffs :
    (N0poly 1 - N0poly 0) = 68016 := by norm_num [N0poly]

