/-
Imscribing/NumberTheory/ErdosStrausProof.lean

Erdős–Straus: what is proved, and what is open.

The conjecture is that `4/n = 1/x + 1/y + 1/z` has a positive integer solution
for every `n ≥ 2`. It is OPEN. What is settled is every congruence class except
one: the residues `n ≡ 1 (mod 4)` with `3 ∤ n` are the standing gap, and every
other `n` is handled by an explicit parametric family.

This file previously claimed the whole conjecture, in 1175 lines, and three
things were wrong with it.

**The statement was empty.** `structure Solution` carried the equation
`4*x*y*z = n*(y*z + x*z + x*y)` with `n` appearing nowhere in its parameters,
and the main theorem read `theorem erdos_straus (n : ℕ) (hn : n ≥ 2) :
∃ (sol : Solution)`. The conclusion does not mention `n`. Whatever `n` the
structure's equation referred to, it was not the `n` the theorem quantified
over, so the theorem said only that some solution of some instance exists.
`Solution` now takes `n` as a parameter and the theorem concludes about that
`n`.

**One family was arithmetically false.** `solve_mod12_9` set `x = 3k+3` and
`y = z = (12k+9)(k+1)`. At `k = 0` that is `1/3 + 1/9 + 1/9 = 5/9`, against
`4/9`. The two tails are each half of what they should be: `4/n − 1/(3k+3)`
is `1/(n(k+1))`, and splitting it in two gives `y = z = 2n(k+1)`. Corrected
below and proved.

**It constructed a solution for the open case.** `solve_mod4_1_not3` claimed to
build a solution for `n ≡ 1 (mod 4)` with `3 ∤ n` out of a CRT search for a
`d` with `d ≡ 3 (mod 4)`, `d ≡ 0 (mod 3)`, `d ≡ −n (mod 5)`. That case is the
conjecture. It is stated here as a Prop and not constructed.

The file also never compiled — it imported `Mathlib.NumberTheory.Primes`, which
does not exist in this toolchain — and it was absent from the lakefile, so
nothing ever checked any of the above.

Author: Lando⊗⊙perator
-/
import Mathlib.Tactic

namespace ErdosStraus

/-- A solution to `4/n = 1/x + 1/y + 1/z`, cleared of denominators. `n` is a
parameter: without it the equation refers to a variable the statement does not
quantify over. -/
structure Solution (n : ℕ) where
  x : ℕ
  y : ℕ
  z : ℕ
  hx : 0 < x
  hy : 0 < y
  hz : 0 < z
  hmain : 4 * x * y * z = n * (y * z + x * z + x * y)

-- ============================================================
-- §1  The parametric families
-- ============================================================

/-- `n` even, `n = 2m`: `4/(2m) = 1/m + 1/(m+1) + 1/(m(m+1))`. -/
def solve_even (m : ℕ) (hm : 1 ≤ m) : Solution (2 * m) where
  x := m
  y := m + 1
  z := m * (m + 1)
  hx := hm
  hy := Nat.succ_pos m
  hz := Nat.mul_pos hm (Nat.succ_pos m)
  hmain := by ring

/-- `n ≡ 3 (mod 4)`, `n = 4k+3`. Since `4/n − 1/(k+1) = 1/(n(k+1))`, and
`1/M = 1/(M+1) + 1/(M(M+1))` splits the tail. -/
def solve_mod4_3 (k : ℕ) : Solution (4 * k + 3) where
  x := k + 1
  y := (4 * k + 3) * (k + 1) + 1
  z := ((4 * k + 3) * (k + 1)) * ((4 * k + 3) * (k + 1) + 1)
  hx := Nat.succ_pos k
  hy := Nat.succ_pos _
  hz := Nat.mul_pos (by positivity) (Nat.succ_pos _)
  hmain := by ring

/-- `n ≡ 2 (mod 4)`, `n = 4k+2`: `4/n = 1/(k+1) + 2/((2k+1)(2k+2))`. -/
def solve_mod4_2 (k : ℕ) : Solution (4 * k + 2) where
  x := k + 1
  y := (2 * k + 1) * (2 * k + 2)
  z := (2 * k + 1) * (2 * k + 2)
  hx := Nat.succ_pos k
  hy := by positivity
  hz := by positivity
  hmain := by ring

/-- `n ≡ 9 (mod 12)`, `n = 12k+9` — the corrected family. `4/n − 1/(3k+3) =
1/(n(k+1))`, so the two equal tails are `2n(k+1)` each, not `n(k+1)`. -/
def solve_mod12_9 (k : ℕ) : Solution (12 * k + 9) where
  x := 3 * k + 3
  y := 2 * (12 * k + 9) * (k + 1)
  z := 2 * (12 * k + 9) * (k + 1)
  hx := by positivity
  hy := by positivity
  hz := by positivity
  hmain := by ring

/-- The value the old family produced, against the value it needed: at `k = 0`
the old tails give `5/9` where `4/9` was wanted. Cleared of denominators,
`4·3·9·9 = 972` while `9·(81 + 27 + 27) = 1215`. -/
theorem old_mod12_9_fails : 4 * 3 * 9 * 9 ≠ 9 * (9 * 9 + 3 * 9 + 3 * 9) := by decide

/-- And the corrected one closes at the same point: `x = 3`, `y = z = 18`. -/
theorem new_mod12_9_holds : 4 * 3 * 18 * 18 = 9 * (18 * 18 + 3 * 18 + 3 * 18) := by decide

-- ============================================================
-- §2  What the families settle
-- ============================================================

/-- The one open case: `n ≡ 1 (mod 4)` with `3 ∤ n`. Stated, not constructed. -/
def ErdosStrausOpenCase : Prop :=
  ∀ n : ℕ, 2 ≤ n → n % 4 = 1 → n % 3 ≠ 0 → Nonempty (Solution n)

/-- The full conjecture. -/
def ErdosStrausConjecture : Prop :=
  ∀ n : ℕ, 2 ≤ n → Nonempty (Solution n)

/-- **Every `n ≥ 2` outside the open case has a solution**, by the four
families. This is the real content, and it is proved. -/
theorem erdos_straus_off_open_case (n : ℕ) (hn : 2 ≤ n)
    (hoff : ¬ (n % 4 = 1 ∧ n % 3 ≠ 0)) : Nonempty (Solution n) := by
  rcases Nat.lt_or_ge (n % 4) 4 with _ | h; swap
  · omega
  have h4 : n % 4 = 0 ∨ n % 4 = 1 ∨ n % 4 = 2 ∨ n % 4 = 3 := by omega
  rcases h4 with h4 | h4 | h4 | h4
  · -- n ≡ 0 (mod 4): even
    obtain ⟨m, rfl⟩ : ∃ m, n = 2 * m := ⟨n / 2, by omega⟩
    exact ⟨solve_even m (by omega)⟩
  · -- n ≡ 1 (mod 4): the hypothesis forces 3 ∣ n, so n ≡ 9 (mod 12)
    have h3 : n % 3 = 0 := by
      by_contra hc
      exact hoff ⟨h4, hc⟩
    obtain ⟨k, rfl⟩ : ∃ k, n = 12 * k + 9 := ⟨(n - 9) / 12, by omega⟩
    exact ⟨solve_mod12_9 k⟩
  · -- n ≡ 2 (mod 4)
    obtain ⟨k, rfl⟩ : ∃ k, n = 4 * k + 2 := ⟨(n - 2) / 4, by omega⟩
    exact ⟨solve_mod4_2 k⟩
  · -- n ≡ 3 (mod 4)
    obtain ⟨k, rfl⟩ : ∃ k, n = 4 * k + 3 := ⟨(n - 3) / 4, by omega⟩
    exact ⟨solve_mod4_3 k⟩

/-- **And the conjecture is exactly the open case away.** Given the residues
`n ≡ 1 (mod 4)` with `3 ∤ n`, the rest follows. -/
theorem conjecture_iff_open_case : ErdosStrausOpenCase → ErdosStrausConjecture := by
  intro hopen n hn
  by_cases h : n % 4 = 1 ∧ n % 3 ≠ 0
  · exact hopen n hn h.1 h.2
  · exact erdos_straus_off_open_case n hn h

/-- The converse direction is immediate, so the gap is precisely that class. -/
theorem open_case_of_conjecture : ErdosStrausConjecture → ErdosStrausOpenCase :=
  fun h n hn _ _ => h n hn

-- ============================================================
-- §3  Small values, checked
-- ============================================================

/-- The families at small arguments, cleared of denominators: `n = 2` even,
`n = 3` at `k = 0`, `n = 6` at `k = 1`, `n = 9` at `k = 0`. -/
theorem small_values :
    (4 * 1 * 2 * 2 = 2 * (2 * 2 + 1 * 2 + 1 * 2)) ∧
    (4 * 1 * 4 * 12 = 3 * (4 * 12 + 1 * 12 + 1 * 4)) ∧
    (4 * 2 * 12 * 12 = 6 * (12 * 12 + 2 * 12 + 2 * 12)) ∧
    (4 * 3 * 18 * 18 = 9 * (18 * 18 + 3 * 18 + 3 * 18)) := by decide

#print axioms erdos_straus_off_open_case
#print axioms conjecture_iff_open_case
#print axioms old_mod12_9_fails

end ErdosStraus
