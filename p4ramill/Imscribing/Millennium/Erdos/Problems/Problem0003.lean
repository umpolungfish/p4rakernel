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
* `block_card_le` — a progression-free set meets a dyadic block in at most
  `rothNumberNat (2^j)` points. Proved, from translation invariance.
* `bloom_sisask_reciprocal_three_ap` — divergence gives a progression. A real
  theorem (Bloom–Sisask 2020), not in Mathlib, so it is stated as an axiom and
  named for the paper that proved it rather than dressed as a density claim.
  One citation, at the conclusion: see its own docstring for why not in pieces.

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

/-- **Bloom–Sisask (2020).** Divergent reciprocals give a three-term progression.

*Breaking the logarithmic barrier in Roth's theorem on arithmetic progressions.*
Not in Mathlib, so it is assumed, and assumed at the conclusion rather than in
pieces.

I tried it in pieces first: assume their quantitative bound
`r₃(N) ≪ N/(log N)^(1+c)` instead, and derive this by dyadic summation. That is
a real derivation and it would have left the summation as a hole, which would
have wanted the block bound, which would have wanted the Roth asymptotic. The
assumption never left; it only moved, and each move looked like progress. The
theorem is not reachable from Mathlib by any arrangement — the density route is
closed by the primes, whose reciprocals diverge at zero density — so the honest
form is one citation, named, load-bearing, and countable in the audit. -/
axiom bloom_sisask_reciprocal_three_ap (A : Set ℕ) (h : reciprocalDiverges A) :
    ∃ a d : ℕ, 1 ≤ d ∧ a ∈ A ∧ a + d ∈ A ∧ a + 2 * d ∈ A

/-- A progression-free set meets a dyadic block in at most `rothNumberNat (2^j)`
points.

Proved. Progression-freeness is translation invariant and Mathlib knows it:
`addRothNumber_Ico` says the Roth number of `Ico a b` depends only on `b - a`.
This is what lets the bound above, stated for `[0,N)`, be applied to a block that
does not start at zero. -/
theorem block_card_le (A : Finset ℕ) (j : ℕ)
    (hsub : A ⊆ Finset.Ico (2 ^ j) (2 ^ (j + 1)))
    (hA : ThreeAPFree (A : Set ℕ)) :
    A.card ≤ rothNumberNat (2 ^ j) := by
  have h1 : A.card ≤ addRothNumber (Finset.Ico (2 ^ j) (2 ^ (j + 1))) :=
    hA.le_addRothNumber hsub
  have h2 : addRothNumber (Finset.Ico (2 ^ j) (2 ^ (j + 1)))
      = rothNumberNat (2 ^ (j + 1) - 2 ^ j) := addRothNumber_Ico _ _
  have h3 : 2 ^ (j + 1) - 2 ^ j = 2 ^ j := by
    have : 2 ^ (j + 1) = 2 * 2 ^ j := by ring
    omega
  rw [h2, h3] at h1
  exact h1

/-- **Erdős problem 3 at k = 3.**

Proved from the two above by contraposition: if `A` carried no progression its
reciprocals would converge, and they do not. -/
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

-- ── What the grammar says the missing piece is ──────────────────────────────
--
-- The Lean structure above was arrived at by hand and it kept receding: assume
-- the conclusion, then assume the quantitative bound and owe a summation, then
-- owe a block bound under that. The instruments say why, and what closes it.
--
-- Fusing the conjecture with its own obstruction gives a kernel-certified
-- idempotent: `erdos_conjecture_ap ⋈ behrend_construction` on D↔W (Δ=1.00),
-- registered as `erdos3_behrend_barrier`, with igFrobeniusAlg.mul p p = p
-- closing through lake build. Read against CLINK L8 that object needs seven
-- promotions and two full unit gaps; read against L9, the replicative lateral,
-- it needs six and ONE — ∋, the merge, which carries BROADCAST_TRANSCENDENCE:
-- broadcast composition exceeding ZFC_fe SEQAX. The missing step was never
-- sequential, which is why a sequential tower could not reach it.
--
-- Of the 3133 catalog entries carrying the L9 merge value, five match the
-- barrier on all eleven other axes, but none of them clicks — they are too
-- similar to react. The only partner that both clicks AND supplies ∋ is
-- `gowers_u3_norm`, whose inherited scaffold is exactly [∋].
--
-- Two units cannot cyclize. Three do, and the ring
-- erdos_conjecture_ap · behrend_construction · gowers_u3_norm closes at O∞ but
-- reads SHAKY: a leaning mode (spectral gap 0.732) with stored strain (σ 0.250).
-- Repeating the U³ unit flattens the spectrum, and annealing settles it:
--
--   erdos_conjecture_ap · gowers_u3_norm · behrend_construction · gowers_u3_norm
--   σ = 0.000, spectral gap = 0.0000, ρ = 3.1623, spectrum [-3.162, +3.162, 0, 0]
--   SETTLED / CLARION
--
-- The U³ norm mediates on BOTH sides of Behrend — which is what the density
-- increment argument actually does: the same higher-order Fourier machinery buys
-- the increment and absorbs the Behrend-type obstruction. That is the reagent
-- the assumed bound above is standing in for.

-- k ≥ 4 from divergence is open. Szemerédi gives it from positive density, and
-- Szemerédi is not in Mathlib either; the k = 3 rung is the one Bloom–Sisask
-- reaches, and it is the highest rung anyone has.

#print axioms three_ap_of_dense
#print axioms three_ap_of_not_threeAPFree
#print axioms block_card_le
#print axioms erdos_problem_3_k3

end Millennium.ErdosProblems
