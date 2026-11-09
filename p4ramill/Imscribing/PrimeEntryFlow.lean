import Mathlib
import Imscribing.PrimeEntryMatching

open scoped BigOperators

namespace Imscribing

/--
A normalized prime-entry flow satisfies the abstract fractional-matching
hypotheses whenever the raw rows are uniformly close to one and the raw
columns are uniformly bounded below the available capacity.

The analytic number theory is isolated in `hZ_lower` and `hr_col`:
`Z i` is the raw row sum, `deltaR` controls its deficit, and
`eta + deltaC` controls every raw column.
-/
theorem primeEntryRawFlow_matching
    (m n q upper : ℕ)
    (r : PrimeLowSource m → PrimeEntryDestination n q upper → ℝ)
    (Z : PrimeLowSource m → ℝ)
    (deltaR eta deltaC : ℝ)
    (hr_nonneg : ∀ i x, 0 ≤ r i x)
    (hr_supported : ∀ i x,
      ¬ PrimeEntryAdj m n q upper i x → r i x = 0)
    (hZ_eq : ∀ i, Z i = ∑ x : PrimeEntryDestination n q upper, r i x)
    (hZ_lower : ∀ i, 1 - deltaR ≤ Z i)
    (hr_col : ∀ x,
      (∑ i : PrimeLowSource m, r i x) ≤ eta + deltaC)
    (hdeltaR : 0 ≤ deltaR)
    (hdeltaC : 0 ≤ deltaC)
    (heta : 0 ≤ eta)
    (heta_lt : eta < 1)
    (hmargin : deltaR + deltaC < 1 - eta) :
    ∃ f : PrimeLowSource m → PrimeEntryDestination n q upper,
      Function.Injective f ∧
      ∀ i, ∃ p : ℕ, Nat.Prime p ∧ (f i).val.val = i.val.val * p := by
  classical
  let w : PrimeLowSource m → PrimeEntryDestination n q upper → ℝ :=
    fun i x => r i x / Z i

  have hden : 0 < 1 - deltaR := by
    linarith
  have hnum : eta + deltaC ≤ 1 - deltaR := by
    linarith
  have hZpos (i : PrimeLowSource m) : 0 < Z i := by
    have h := hZ_lower i
    linarith

  have hw_nonneg : ∀ i x, 0 ≤ w i x := by
    intro i x
    dsimp [w]
    exact div_nonneg (hr_nonneg i x) (le_of_lt (hZpos i))

  have hw_supported : ∀ i x,
      ¬ PrimeEntryAdj m n q upper i x → w i x = 0 := by
    intro i x hnot
    dsimp [w]
    rw [hr_supported i x hnot]
    simp

  have hw_row : ∀ i,
      (∑ x : PrimeEntryDestination n q upper, w i x) = 1 := by
    intro i
    dsimp [w]
    have hsum_pos :
        0 < (∑ x : PrimeEntryDestination n q upper, r i x) := by
      simpa [hZ_eq i] using hZpos i
    calc
      (∑ x : PrimeEntryDestination n q upper, r i x / Z i)
          = (∑ x : PrimeEntryDestination n q upper, r i x) / Z i := by
              rw [Finset.sum_div]
      _ = 1 := by
            rw [hZ_eq i]
            exact div_self (ne_of_gt hsum_pos)

  have hw_col : ∀ x,
      (∑ i : PrimeLowSource m, w i x) ≤ 1 := by
    intro x
    calc
      (∑ i : PrimeLowSource m, w i x)
          ≤ ∑ i : PrimeLowSource m, r i x / (1 - deltaR) := by
              apply Finset.sum_le_sum
              intro i hi
              dsimp [w]
              exact div_le_div_of_nonneg_left
                (hr_nonneg i x) hden (hZ_lower i)
      _ = (∑ i : PrimeLowSource m, r i x) / (1 - deltaR) := by
            rw [Finset.sum_div]
      _ ≤ (eta + deltaC) / (1 - deltaR) := by
            exact div_le_div_of_nonneg_right (hr_col x) hden.le
      _ ≤ 1 := by
            rw [div_le_iff₀ hden]
            nlinarith [hnum]

  exact primeEntryFlow_matching m n q upper w
    hw_nonneg hw_supported hw_row hw_col

end Imscribing
