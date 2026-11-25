import Mathlib
import Imscribing.Millennium.Erdos.Proofs.MontgomeryVaughan220.Fourier
open Erdos220
namespace Imscribing.Millennium.WienerKhinchin
noncomputable section

/-- Wiener-Khinchin orthogonality step for the a=0 stratum. -/
theorem wk_orthogonality (q : ℕ) (hq : 0 < q) (b k l : ℕ) :
    ∑ a ∈ Finset.range q, fourierRoot q ^ (((b:ℤ) - k + l) * a) =
      if (q : ℤ) ∣ (b:ℤ) - k + l then q else 0 := by
  exact fourierRoot_orthogonality q hq ((b:ℤ) - k + l)

