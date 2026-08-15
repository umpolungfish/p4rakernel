import Mathlib
import Imscribing.Millennium.Erdos.ErdosTuranAP
import Imscribing.Millennium.Erdos.Base

/-!
# Erdős problem 3, k = 3

If the reciprocals of `A` diverge, does `A` contain a three-term progression?

The file used to answer yes from an axiom asserting that divergent reciprocals
give positive lower density:

    ∃ ε > 0, ∀ N, ε * N ≤ #(A ∩ [0,N))

That axiom is FALSE, and the counterexample is proved two files away: the primes.
`ErdosTuran.primes_reciprocal_diverges` says Σ 1/p diverges, and π(N)/N → 0, so no
ε survives every N. Everything downstream of it proved nothing.

It is also exactly the hard part. Erdős' question is interesting BECAUSE divergence
does not give density — that gap is why the primes needed Green–Tao. Assuming it
away assumes away the problem.

What is separated here:

* `three_ap_of_dense` — density gives a progression. Proved, from Roth via
  `ErdosTuran.dense_has_3ap`, resting on nothing but Mathlib's foundation.
* `bloom_sisask_reciprocal_three_ap` — divergence gives a progression. A real
  theorem (Bloom–Sisask 2020), not in Mathlib, so it is stated as an axiom and
  named for the paper that proved it rather than dressed as a density claim.

The lift reads the difference: the first verdicts closed, the second opens a fork
that nothing rejoins, which is what resting on an uncited-in-Mathlib theorem is.
-/

open scoped BigOperators Classical
open Finset

namespace Millennium.ErdosProblems

def reciprocalDiverges (A : Set ℕ) : Prop :=
  ¬ Summable (fun n : {n // n ∈ A} => (1 / (n.1 : ℝ)))

/-- Mathlib's `ThreeAPFree` negated, unpacked into a progression with a positive
common difference. -/
theorem three_ap_of_not_threeAPFree {S : Set ℕ} (h : ¬ ThreeAPFree S) :
    ∃ a d : ℕ, 1 ≤ d ∧ a ∈ S ∧ a + d ∈ S ∧ a + 2 * d ∈ S := by
  unfold ThreeAPFree at h
  push_neg at h
  obtain ⟨a, ha, b, hb, c, hc, habc, hab⟩ := h
  rcases lt_or_gt_of_ne hab with hlt | hgt
  · refine ⟨a, b - a, by omega, ha, ?_, ?_⟩
    · have : a + (b - a) = b := by omega
      rwa [this]
    · have : a + 2 * (b - a) = c := by omega
      rwa [this]
  · have hcb : c < b := by omega
    refine ⟨c, b - c, by omega, hc, ?_, ?_⟩
    · have : c + (b - c) = b := by omega
      rwa [this]
    · have : c + 2 * (b - c) = a := by omega
      rwa [this]

/-- **Density gives a progression.** Proved, at no assumed cost.

This is the half Roth settles. `A` need only be dense in ONE window wide enough
for the corners bound; no uniform lower density over every `N` is required, which
is what made the old axiom both false and unnecessary. -/
theorem three_ap_of_dense
    {ε : ℝ} (hε : 0 < ε) (A : Set ℕ)
    (h : ∃ n : ℕ, cornersTheoremBound (ε / 3) ≤ n ∧
        ε * n ≤ #((Finset.range n).filter (· ∈ A))) :
    ∃ a d : ℕ, 1 ≤ d ∧ a ∈ A ∧ a + d ∈ A ∧ a + 2 * d ∈ A := by
  obtain ⟨n, hn, hcard⟩ := h
  set S : Finset ℕ := (Finset.range n).filter (· ∈ A) with hS
  have hsub : S ⊆ Finset.range n := Finset.filter_subset _ _
  have hne : ¬ ThreeAPFree (S : Set ℕ) := ErdosTuran.dense_has_3ap hε hn S hsub hcard
  obtain ⟨a, d, hd, h1, h2, h3⟩ := three_ap_of_not_threeAPFree hne
  have mem : ∀ {x : ℕ}, x ∈ (S : Set ℕ) → x ∈ A := by
    intro x hx
    simp only [hS, Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_range] at hx
    exact hx.2
  exact ⟨a, d, hd, mem h1, mem h2, mem h3⟩

/-- **Divergence gives a progression.** Bloom–Sisask, *Breaking the logarithmic
barrier in Roth's theorem on arithmetic progressions* (2020).

Assumed, because it is not in Mathlib. It is stated as itself — the theorem whose
proof this corpus does not carry — and not as a density claim that would be false.
Every theorem below inherits the open fork this leaves, and the lift says so. -/
axiom bloom_sisask_reciprocal_three_ap (A : Set ℕ) (h : reciprocalDiverges A) :
    ∃ a d : ℕ, 1 ≤ d ∧ a ∈ A ∧ a + d ∈ A ∧ a + 2 * d ∈ A

/-- Erdős problem 3 at k = 3. -/
theorem erdos_problem_3_k3 (A : Set ℕ) (h_sum_div : reciprocalDiverges A) :
    ∃ a d : ℕ, 1 ≤ d ∧ a ∈ A ∧ a + d ∈ A ∧ a + 2 * d ∈ A :=
  bloom_sisask_reciprocal_three_ap A h_sum_div

theorem erdos_problem_3_k3' {S : Set ℕ} (h : ¬ ThreeAPFree S) :
    ∃ a d : ℕ, 1 ≤ d ∧ a ∈ S ∧ a + d ∈ S ∧ a + 2 * d ∈ S :=
  three_ap_of_not_threeAPFree h

theorem erdos_k3_certified (A : Set ℕ) (h_sum_div : reciprocalDiverges A) :
    ∃ a d : ℕ, 1 ≤ d ∧ a ∈ A ∧ a + d ∈ A ∧ a + 2 * d ∈ A :=
  erdos_problem_3_k3 A h_sum_div

theorem erdos_problem_3_full (A : Set ℕ) (h_sum_div : reciprocalDiverges A) :
    ∃ a d : ℕ, 1 ≤ d ∧ a ∈ A ∧ a + d ∈ A ∧ a + 2 * d ∈ A :=
  erdos_problem_3_k3 A h_sum_div

-- k ≥ 4 from divergence is open. Szemerédi gives it from positive density, and
-- Szemerédi is not in Mathlib either; the k = 3 rung is the one Bloom–Sisask
-- reaches, and it is the highest rung anyone has.

#print axioms three_ap_of_dense
#print axioms three_ap_of_not_threeAPFree
#print axioms erdos_problem_3_k3

end Millennium.ErdosProblems
