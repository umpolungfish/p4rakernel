import Mathlib
import Imscribing.PrimeEntryFlow

open scoped BigOperators

namespace Imscribing

/-- All left-hand integers `1, ..., n`, represented by `Fin n` via `i ↦ i+1`. -/
abbrev PrimeFullSource (n : ℕ) := Fin n

/-- Right-hand integers in `(n, upper]`. -/
abbrev PrimeFullDestination (n upper : ℕ) :=
  {x : Fin (upper + 1) // n < x.val}

/-- Convert a zero-based source index below `m` to the existing low-source type. -/
def lowSourceOfFin (m n : ℕ) (i : Fin n) (hi : i.val < m) :
    PrimeLowSource m :=
  ⟨⟨i.val + 1, by omega⟩, by exact Nat.succ_ne_zero _⟩

/-- Embed a low prime-entry destination into the full right-hand interval. -/
def embedLowPrimeDestination
    (n q upper : ℕ) (hnq : n ≤ n * q)
    (x : PrimeEntryDestination n q upper) :
    PrimeFullDestination n upper := by
  refine ⟨⟨x.val.val, ?_⟩, ?_⟩
  · have hx := (primeEntryDestination_bounds n q upper x).2
    omega
  · exact lt_of_le_of_lt hnq x.property

/-- The direct high-index assignment `i ↦ q*(i+1)`. -/
def highPrimeDestination
    (n m q upper : ℕ)
    (hlower : n < q * (m + 1))
    (hupper : q * n ≤ upper)
    (i : Fin n) (hi : m ≤ i.val) :
    PrimeFullDestination n upper := by
  have hiUpper : i.val + 1 ≤ n := Nat.succ_le_of_lt i.isLt
  have hmulUpper : q * (i.val + 1) ≤ q * n :=
    Nat.mul_le_mul_left q hiUpper
  have hmulLower : q * (m + 1) ≤ q * (i.val + 1) :=
    Nat.mul_le_mul_left q (Nat.succ_le_succ hi)
  refine ⟨⟨q * (i.val + 1), Nat.lt_succ_of_le (le_trans hmulUpper hupper)⟩, ?_⟩
  exact lt_of_lt_of_le hlower hmulLower

/--
Combine a low-index prime-entry matching with the direct high-index assignment.

The hypotheses `n < q*(m+1)` and `q*n ≤ upper` ensure that high-index
outputs lie in `(n, n*q] ⊆ (n, upper]`; low-index prime-entry outputs lie
in `(n*q, upper]`. Hence the two ranges are disjoint.
-/
theorem extendPrimeEntryMatching
    (m n q upper : ℕ)
    (hnq : n ≤ n * q)
    (hqpos : 0 < q)
    (hlower : n < q * (m + 1))
    (hupper : q * n ≤ upper)
    (hLow :
      ∃ f : PrimeLowSource m → PrimeEntryDestination n q upper,
        Function.Injective f ∧
        ∀ i, ∃ p : ℕ, Nat.Prime p ∧
          (f i).val.val = i.val.val * p) :
    ∃ F : PrimeFullSource n → PrimeFullDestination n upper,
      Function.Injective F ∧
      ∀ i, ∃ d : ℕ, 0 < d ∧
        (F i).val.val = (i.val + 1) * d := by
  classical
  obtain ⟨f, hf_inj, hf_prime⟩ := hLow
  let F : PrimeFullSource n → PrimeFullDestination n upper := fun i =>
    if hi : i.val < m then
      embedLowPrimeDestination n q upper hnq (f (lowSourceOfFin m n i hi))
    else
      highPrimeDestination n m q upper hlower hupper i (Nat.le_of_not_gt hi)
  refine ⟨F, ?_, ?_⟩
  · intro i j hij
    have hval : (F i).val.val = (F j).val.val :=
      congrArg (fun z : PrimeFullDestination n upper => z.val.val) hij
    by_cases hi : i.val < m
    · by_cases hj : j.val < m
      · have hfeq :
            f (lowSourceOfFin m n i hi) =
              f (lowSourceOfFin m n j hj) := by
          apply Subtype.ext
          apply Fin.ext
          simpa [F, hi, hj, embedLowPrimeDestination] using hval
        have hloweq := hf_inj hfeq
        have hidx : i.val + 1 = j.val + 1 := by
          simpa [lowSourceOfFin] using
            congrArg (fun z : PrimeLowSource m => z.val.val) hloweq
        apply Fin.ext
        omega
      · have hjHigh : m ≤ j.val := Nat.le_of_not_gt hj
        have hLowBound :
            n * q < (f (lowSourceOfFin m n i hi)).val.val :=
          (f (lowSourceOfFin m n i hi)).property
        have hjUpper : q * (j.val + 1) ≤ n * q := by
          calc
            q * (j.val + 1) ≤ q * n :=
              Nat.mul_le_mul_left q (Nat.succ_le_of_lt j.isLt)
            _ = n * q := Nat.mul_comm q n
        have hEq := hval
        simp [F, hi, hj, embedLowPrimeDestination,
          highPrimeDestination] at hEq
        omega
    · have hiHigh : m ≤ i.val := Nat.le_of_not_gt hi
      by_cases hj : j.val < m
      · have hiUpper : q * (i.val + 1) ≤ n * q := by
          calc
            q * (i.val + 1) ≤ q * n :=
              Nat.mul_le_mul_left q (Nat.succ_le_of_lt i.isLt)
            _ = n * q := Nat.mul_comm q n
        have hLowBound :
            n * q < (f (lowSourceOfFin m n j hj)).val.val :=
          (f (lowSourceOfFin m n j hj)).property
        have hEq := hval
        simp [F, hi, hj, embedLowPrimeDestination,
          highPrimeDestination] at hEq
        omega
      · have hjHigh : m ≤ j.val := Nat.le_of_not_gt hj
        have hEq : q * (i.val + 1) = q * (j.val + 1) := by
          simpa [F, hi, hj, highPrimeDestination] using hval
        have hsucc : i.val + 1 = j.val + 1 :=
          Nat.eq_of_mul_eq_mul_left hqpos hEq
        have hidx : i.val = j.val := by omega
        exact Fin.ext hidx
  · intro i
    by_cases hi : i.val < m
    · obtain ⟨p, hp, hmul⟩ := hf_prime (lowSourceOfFin m n i hi)
      refine ⟨p, hp.pos, ?_⟩
      simpa [F, hi, embedLowPrimeDestination, lowSourceOfFin] using hmul
    · have hiHigh : m ≤ i.val := Nat.le_of_not_gt hi
      refine ⟨q, hqpos, ?_⟩
      simp [F, hi, highPrimeDestination]
      exact Nat.mul_comm q (i.val + 1)

/--
The full divisibility-matching theorem obtained directly from a raw
prime-entry flow on the low indices and the deterministic high-index map.
-/
theorem primeEntryRawFlow_fullMatching
    (m n q upper : ℕ)
    (r : PrimeLowSource m → PrimeEntryDestination n q upper → ℝ)
    (Z : PrimeLowSource m → ℝ)
    (deltaR eta deltaC : ℝ)
    (hnq : n ≤ n * q)
    (hqpos : 0 < q)
    (hlower : n < q * (m + 1))
    (hupper : q * n ≤ upper)
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
    ∃ F : PrimeFullSource n → PrimeFullDestination n upper,
      Function.Injective F ∧
      ∀ i, ∃ d : ℕ, 0 < d ∧
        (F i).val.val = (i.val + 1) * d := by
  have hLow := primeEntryRawFlow_matching
    m n q upper r Z deltaR eta deltaC
    hr_nonneg hr_supported hZ_eq hZ_lower hr_col
    hdeltaR hdeltaC heta heta_lt hmargin
  exact extendPrimeEntryMatching m n q upper
    hnq hqpos hlower hupper hLow

end Imscribing
