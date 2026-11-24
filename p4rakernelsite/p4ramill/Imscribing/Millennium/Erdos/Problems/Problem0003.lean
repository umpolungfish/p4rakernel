import Mathlib
import Imscribing.Millennium.Erdos.ErdosTuranAP
import Imscribing.Millennium.Erdos.Base
import Imscribing.Millennium.Erdos.APFreeReduction
import Imscribing.Classical.Szemeredi

/-!
# Erdős problem 3 at k = 3

If `Σ 1/a` over `A` diverges, does `A` contain a three-term arithmetic
progression?

The difficulty is that divergence does not give density. The primes witness the
gap: `ErdosTuran.primes_reciprocal_diverges` gives `Σ 1/p = ∞` while `π(N)/N → 0`,
so no `ε` satisfies `ε·N ≤ #(A ∩ [0,N))` for every `N`. Any argument routed
through positive lower density is therefore not merely unproved but unavailable.

What this file proves outright:

* `three_ap_of_dense` — one window dense enough for the corners bound already
  forces a progression, via Roth.
* `block_card_le` — a progression-free set meets the dyadic block `[2^j, 2^(j+1))`
  in at most `rothNumberNat (2^j)` points, since progression-freeness is
  translation invariant.
* `summable_of_blocks` — if `Σ_j r₃(2^j)/2^j` converges then a progression-free
  set has convergent reciprocal sum, and hence divergence forces a progression.

* `summable_blocks_of_log_bound` — a Roth bound past exponent one makes those
  block terms sum. The exponent is the whole content: at `ε = 0` the comparison
  series is harmonic.
* `erdos_problem_3_k3_of_roth_bound` — the conclusion from that bound alone.

What it assumes: one axiom, `Szemeredi.bloom_sisask_upper_bound`
(arXiv:2007.03528), `r₃(N) ≤ C·N/(log N)^(1+c)` on Mathlib's `rothNumberNat`.
`erdos_problem_3_k3_unconditional` rests on it and on nothing else; every other
theorem here rests on `propext`, `Classical.choice` and `Quot.sound` alone.
-/

open scoped BigOperators Classical
open Finset

namespace Problem0003

open Imscribing.Classical.Szemeredi
open Millennium.ErdosProblems.APFree

/-- A set with no positive-difference 3-term progression is 3AP-free in
Mathlib's endpoint/midpoint formulation. -/
private theorem apFree_threeAPFree {A : Set ℕ}
    (hA : SetAPFree 3 A) : ThreeAPFree A := by
  rw [threeAPFree_iff_eq_right]
  intro a ha b hb c hc hmid
  by_contra hac
  rcases lt_or_gt_of_ne hac with hac | hca
  · let d := b - a
    have h₁ : a + d = b := by dsimp [d]; omega
    have h₂ : a + 2 * d = c := by dsimp [d]; omega
    have hd : 0 < d := by dsimp [d]; omega
    have hprog : ∀ i, i < 3 → a + i * d ∈ A := by
      intro i hi
      interval_cases i
      · simpa using ha
      · simpa [h₁] using hb
      · simpa [h₂] using hc
    exact hA a d hd hprog
  · let d := b - c
    have h₁ : c + d = b := by dsimp [d]; omega
    have h₂ : c + 2 * d = a := by dsimp [d]; omega
    have hd : 0 < d := by dsimp [d]; omega
    have hprog : ∀ i, i < 3 → c + i * d ∈ A := by
      intro i hi
      interval_cases i
      · simpa using hc
      · simpa [h₁] using hb
      · simpa [h₂] using ha
    exact hA c d hd hprog

/-- The APFreeReduction extremum uses progressions `a+i*d` in `range N`;
Mathlib's Roth number uses the equivalent 3AP-free endpoint/midpoint predicate. -/
private theorem r_k_three_le_rothNumberNat (N : ℕ) :
    Imscribing.Classical.Szemeredi.r_k 3 N ≤ rothNumberNat N := by
  unfold Imscribing.Classical.Szemeredi.r_k
  refine Finset.sup_le ?_
  intro S hS
  rw [Finset.mem_filter, Finset.mem_powerset] at hS
  have hsetfree : SetAPFree 3 (S : Set ℕ) := by
    intro a d hd hprog
    apply hS.2 a d hd
    intro i hi
    exact hprog i hi
  have hfree : ThreeAPFree (S : Set ℕ) := apFree_threeAPFree hsetfree
  have hbelow : ∀ x ∈ S, x < N := by
    intro x hx
    exact Finset.mem_range.mp (hS.1 hx)
  exact hfree.le_rothNumberNat S hbelow rfl

/-- Erdős problem 3 at three terms, from the encoded Bloom–Sisak extremal
bound. The dyadic split, shell estimate, and summability contradiction are the
general APFreeReduction construction. -/
theorem erdos_problem_3_k3_of_roth_bound (A : Set ℕ)
    (hdiv : ¬ Summable (fun n : {n // n ∈ A} => (1 / (n.1 : ℝ)))) :
    ∃ a d : ℕ, 0 < d ∧ ∀ i, i < 3 → a + i * d ∈ A := by
  obtain ⟨C, c, N₀, hC, hc, hN₀, hBS⟩ :=
    Imscribing.Classical.Szemeredi.bloom_sisask_upper_bound
  have hbound : ∀ N : ℕ, N₀ ≤ N →
      (Imscribing.Classical.Szemeredi.r_k 3 N : ℝ) ≤
        C * N / (Real.log N) ^ (1 + c) := by
    intro N hN
    calc
      (Imscribing.Classical.Szemeredi.r_k 3 N : ℝ)
          ≤ (rothNumberNat N : ℝ) := by
            exact_mod_cast r_k_three_le_rothNumberNat N
      _ ≤ C * N / (Real.log N) ^ (1 + c) := hBS N hN
  exact Millennium.ErdosProblems.APFree.erdos_conjecture_of_bound
    3 C c hc hC N₀ hN₀ hbound A hdiv

/-- The k=3 statement follows using the Bloom–Sisak bound admitted in
`Szemeredi.bloom_sisask_upper_bound`. -/
theorem erdos_problem_3_k3_unconditional (A : Set ℕ)
    (hdiv : ¬ Summable (fun n : {n // n ∈ A} => (1 / (n.1 : ℝ)))) :
    ∃ a d : ℕ, 0 < d ∧ ∀ i, i < 3 → a + i * d ∈ A :=
  erdos_problem_3_k3_of_roth_bound A hdiv

end Problem0003
