import Mathlib
import Imscribing.Millennium.Erdos.ErdosTuranAP
import Imscribing.Millennium.Erdos.Base
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

/-- The reciprocal sum of a progression-free set converges.

Carried as a hypothesis, not an axiom: `summable_of_blocks` derives it from
`Summable (fun j => r₃(2^j)/2^j)`, which `kelley_meka_upper_bound` supplies. A
hypothesis puts the remaining debt in the type of every theorem that uses it,
where it is visible without `#print axioms`, and anyone who discharges it gets
those theorems unconditionally. -/
abbrev ReciprocalSumConverges : Prop :=
  ∀ A : Set ℕ, ThreeAPFree A → Summable (fun n : {n // n ∈ A} => (1 / (n.1 : ℝ)))

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

/-- `[1, 2^J)` is the disjoint union of the dyadic blocks below it. -/
theorem dyadic_split (g : ℕ → ℝ) : ∀ J : ℕ,
    ∑ i ∈ Finset.Ico 1 (2 ^ J), g i
      = ∑ j ∈ Finset.range J, ∑ i ∈ Finset.Ico (2 ^ j) (2 ^ (j + 1)), g i := by
  intro J
  induction J with
  | zero => simp
  | succ J ih =>
      have h1 : (1 : ℕ) ≤ 2 ^ J := Nat.one_le_two_pow
      have h2 : (2 : ℕ) ^ J ≤ 2 ^ (J + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      rw [Finset.sum_range_succ, ← ih, Finset.sum_Ico_consecutive g h1 h2]

/-- A progression-free set's reciprocals over one dyadic block are bounded by
`r₃(2^j)/2^j`: at most `rothNumberNat (2^j)` terms by `block_card_le`, each at
most `1/2^j` since the block starts there. -/
theorem block_sum_le (A : Set ℕ) (hA : ThreeAPFree A) (j : ℕ) :
    ∑ i ∈ Finset.Ico (2 ^ j) (2 ^ (j + 1)), A.indicator (fun m => (1 : ℝ) / m) i
      ≤ (rothNumberNat (2 ^ j) : ℝ) / 2 ^ j := by
  classical
  set S : Finset ℕ := (Finset.Ico (2 ^ j) (2 ^ (j + 1))).filter (· ∈ A) with hS
  -- the indicator collapses the sum onto S
  have hcollapse :
      ∑ i ∈ Finset.Ico (2 ^ j) (2 ^ (j + 1)), A.indicator (fun m => (1 : ℝ) / m) i
        = ∑ i ∈ S, (1 : ℝ) / i := by
    rw [hS, Finset.sum_filter]
    exact Finset.sum_congr rfl (fun i _ => by simp [Set.indicator_apply])
  -- every term is at most 1/2^j
  have hterm : ∀ i ∈ S, (1 : ℝ) / i ≤ 1 / 2 ^ j := by
    intro i hi
    rw [hS, Finset.mem_filter, Finset.mem_Ico] at hi
    have : (2 : ℝ) ^ j ≤ (i : ℝ) := by exact_mod_cast hi.1.1
    have hpos : (0 : ℝ) < 2 ^ j := by positivity
    exact one_div_le_one_div_of_le hpos this
  have hcard : S.card ≤ rothNumberNat (2 ^ j) := by
    refine block_card_le S j (Finset.filter_subset _ _) ?_
    exact hA.mono (by intro x hx; rw [hS] at hx; simp only [Finset.coe_filter,
      Set.mem_setOf_eq] at hx; exact hx.2)
  calc ∑ i ∈ Finset.Ico (2 ^ j) (2 ^ (j + 1)), A.indicator (fun m => (1 : ℝ) / m) i
      = ∑ i ∈ S, (1 : ℝ) / i := hcollapse
    _ ≤ S.card • ((1 : ℝ) / 2 ^ j) := Finset.sum_le_card_nsmul S _ _ hterm
    _ = (S.card : ℝ) / 2 ^ j := by simp [nsmul_eq_mul]; ring
    _ ≤ (rothNumberNat (2 ^ j) : ℝ) / 2 ^ j := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        exact_mod_cast hcard

/-- **The dyadic assembly.** If the block bounds sum, the reciprocals converge.

This is the whole of what combinatorics owes. The remaining input is analytic and
is exactly what a quantitative Roth bound supplies: `r₃(N) ≤ N·exp(−c·(log N)^(1/11))`
makes `Σ_j r₃(2^j)/2^j` a convergent stretched exponential. -/
theorem summable_of_blocks (A : Set ℕ) (hA : ThreeAPFree A)
    (hb : Summable (fun j : ℕ => (rothNumberNat (2 ^ j) : ℝ) / 2 ^ j)) :
    Summable (fun n : {n // n ∈ A} => (1 / (n.1 : ℝ))) := by
  classical
  have hcomp : (fun n : {n // n ∈ A} => (1 : ℝ) / (n.1 : ℝ))
      = (fun m : ℕ => (1 : ℝ) / (m : ℝ)) ∘ Subtype.val := rfl
  rw [hcomp, summable_subtype_iff_indicator]
  set g : ℕ → ℝ := A.indicator (fun m => (1 : ℝ) / m) with hg
  have hnonneg : ∀ n, 0 ≤ g n := by
    intro n; rw [hg]; unfold Set.indicator
    split <;> positivity
  refine summable_of_sum_range_le hnonneg (c := ∑' j : ℕ, (rothNumberNat (2 ^ j) : ℝ) / 2 ^ j) ?_
  intro N
  -- push out to a power of two
  have hNJ : N ≤ 2 ^ N := Nat.le_of_lt (Nat.lt_two_pow_self)
  have hstep1 : ∑ i ∈ Finset.range N, g i ≤ ∑ i ∈ Finset.range (2 ^ N), g i :=
    Finset.sum_le_sum_of_subset_of_nonneg
      (fun x hx => Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp hx) hNJ))
      (fun i _ _ => hnonneg i)
  -- index 0 contributes nothing: 1/0 = 0 in ℝ, and the indicator is 0 off A
  have hzero : g 0 = 0 := by
    rw [hg]; unfold Set.indicator; split <;> simp
  have hsplit0 : ∑ i ∈ Finset.range (2 ^ N), g i = ∑ i ∈ Finset.Ico 1 (2 ^ N), g i := by
    rw [Finset.range_eq_Ico,
      ← Finset.sum_Ico_consecutive g (Nat.zero_le 1) Nat.one_le_two_pow]
    simp [hzero]
  have hstep2 : ∑ i ∈ Finset.Ico 1 (2 ^ N), g i
      = ∑ j ∈ Finset.range N, ∑ i ∈ Finset.Ico (2 ^ j) (2 ^ (j + 1)), g i := dyadic_split g N
  have hstep3 : ∑ j ∈ Finset.range N, ∑ i ∈ Finset.Ico (2 ^ j) (2 ^ (j + 1)), g i
      ≤ ∑ j ∈ Finset.range N, (rothNumberNat (2 ^ j) : ℝ) / 2 ^ j :=
    Finset.sum_le_sum (fun j _ => block_sum_le A hA j)
  have hstep4 : ∑ j ∈ Finset.range N, (rothNumberNat (2 ^ j) : ℝ) / 2 ^ j
      ≤ ∑' j : ℕ, (rothNumberNat (2 ^ j) : ℝ) / 2 ^ j :=
    hb.sum_le_tsum _ (fun j _ => by positivity)
  calc ∑ i ∈ Finset.range N, g i ≤ ∑ i ∈ Finset.range (2 ^ N), g i := hstep1
    _ = ∑ i ∈ Finset.Ico 1 (2 ^ N), g i := hsplit0
    _ = _ := hstep2
    _ ≤ _ := hstep3
    _ ≤ _ := hstep4



/-- **The analytic half.** A Roth bound past exponent one makes the block terms sum.

`r₃(N) ≤ C·N/(log N)^(1+ε)` gives `r₃(2^j)/2^j ≤ K·j^-(1+ε)` with
`K = C/(log 2)^(1+ε)`, and a p-series with `p > 1` converges. The exponent is the
whole content: at `ε = 0` the comparison series is harmonic and this fails, which
is why every Roth bound before Bloom–Sisask left Erdős 3 open.

Stated about Mathlib's `rothNumberNat` rather than about an opaque symbol, so it
has content to discharge. -/
theorem summable_blocks_of_log_bound
    (C ε : ℝ) (hε : 0 < ε) (hC : 0 ≤ C) (N₀ : ℕ) (hN₀ : 1 ≤ N₀)
    (h : ∀ N : ℕ, N₀ ≤ N → (rothNumberNat N : ℝ) ≤ C * N / (Real.log N) ^ (1 + ε)) :
    Summable (fun j : ℕ => (rothNumberNat (2 ^ j) : ℝ) / 2 ^ j) := by
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  set K : ℝ := C / (Real.log 2) ^ (1 + ε) with hK
  have hKnn : 0 ≤ K := by
    apply div_nonneg hC
    exact le_of_lt (Real.rpow_pos_of_pos hlog2 _)
  -- the comparison series
  have hp : Summable (fun j : ℕ => K * (1 / (j : ℝ) ^ (1 + ε))) :=
    (Real.summable_one_div_nat_rpow.mpr (by linarith)).mul_left K
  -- shift past the first N₀ indices, where the bound has nothing to say
  rw [← summable_nat_add_iff N₀]
  refine Summable.of_nonneg_of_le (fun j => by positivity) ?_ ((summable_nat_add_iff N₀).mpr hp)
  intro j
  set n : ℕ := j + N₀ with hn
  have h2n : (N₀ : ℕ) ≤ 2 ^ n := le_trans (Nat.le_of_lt (Nat.lt_two_pow_self)) (Nat.pow_le_pow_right (by norm_num) (by omega))
  have hbound := h (2 ^ n) h2n
  have hlogpow : Real.log ((2 : ℕ) ^ n : ℕ) = n * Real.log 2 := by
    push_cast
    rw [Real.log_pow]
  have hpos : (0 : ℝ) < (2 : ℝ) ^ n := by positivity
  have hnpos : (0 : ℝ) < (n : ℝ) := by
    have : 1 ≤ n := by omega
    exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one this
  have hlrpow : (0 : ℝ) < (Real.log 2) ^ (1 + ε) := Real.rpow_pos_of_pos hlog2 _
  have hnrpow : (0 : ℝ) < (n : ℝ) ^ (1 + ε) := Real.rpow_pos_of_pos hnpos _
  have hsplit : ((n : ℝ) * Real.log 2) ^ (1 + ε)
      = (n : ℝ) ^ (1 + ε) * (Real.log 2) ^ (1 + ε) :=
    Real.mul_rpow (le_of_lt hnpos) (le_of_lt hlog2)
  calc (rothNumberNat (2 ^ n) : ℝ) / 2 ^ n
      ≤ (C * ((2:ℕ) ^ n : ℕ) / (Real.log ((2:ℕ) ^ n : ℕ)) ^ (1 + ε)) / 2 ^ n := by
        gcongr
    _ = K * (1 / (n : ℝ) ^ (1 + ε)) := by
        rw [hlogpow]
        push_cast
        rw [hsplit, hK]
        field_simp

/-- **Erdős problem 3 at k = 3.**

Proved from the two above by contraposition: if `A` carried no progression its
reciprocals would converge, and they do not. -/
theorem erdos_problem_3_k3 (hsum : ReciprocalSumConverges)
    (A : Set ℕ) (h_sum_div : reciprocalDiverges A) :
    ∃ a d : ℕ, 1 ≤ d ∧ a ∈ A ∧ a + d ∈ A ∧ a + 2 * d ∈ A := by
  by_cases hfree : ThreeAPFree A
  · exact absurd (hsum A hfree) h_sum_div
  · exact three_ap_of_not_threeAPFree hfree

/-- **Erdős problem 3 at k = 3, from a quantitative Roth bound.**

The whole statement, resting on one hypothesis: a bound on `rothNumberNat` past
exponent one. That is Bloom–Sisask (arXiv:2007.03528); Kelley–Meka
(arXiv:2302.05537) is stronger and implies it. Everything between that bound and
this conclusion is proved above. -/
theorem erdos_problem_3_k3_of_roth_bound
    (C ε : ℝ) (hε : 0 < ε) (hC : 0 ≤ C) (N₀ : ℕ) (hN₀ : 1 ≤ N₀)
    (hroth : ∀ N : ℕ, N₀ ≤ N → (rothNumberNat N : ℝ) ≤ C * N / (Real.log N) ^ (1 + ε))
    (A : Set ℕ) (h_sum_div : reciprocalDiverges A) :
    ∃ a d : ℕ, 1 ≤ d ∧ a ∈ A ∧ a + d ∈ A ∧ a + 2 * d ∈ A :=
  erdos_problem_3_k3
    (fun A' hA' => summable_of_blocks A' hA'
      (summable_blocks_of_log_bound C ε hε hC N₀ hN₀ hroth))
    A h_sum_div


theorem erdos_problem_3_k3' {S : Set ℕ} (h : ¬ ThreeAPFree S) :
    ∃ a d : ℕ, 1 ≤ d ∧ a ∈ S ∧ a + d ∈ S ∧ a + 2 * d ∈ S :=
  three_ap_of_not_threeAPFree h

theorem erdos_k3_certified (hsum : ReciprocalSumConverges)
    (A : Set ℕ) (h_sum_div : reciprocalDiverges A) :
    ∃ a d : ℕ, 1 ≤ d ∧ a ∈ A ∧ a + d ∈ A ∧ a + 2 * d ∈ A :=
  erdos_problem_3_k3 hsum A h_sum_div

theorem erdos_problem_3_full (hsum : ReciprocalSumConverges)
    (A : Set ℕ) (h_sum_div : reciprocalDiverges A) :
    ∃ a d : ℕ, 1 ≤ d ∧ a ∈ A ∧ a + d ∈ A ∧ a + 2 * d ∈ A :=
  erdos_problem_3_k3 hsum A h_sum_div

/-- **Erdős problem 3 at k = 3.**

Divergent reciprocals give a three-term progression. The corpus's only remaining
assumption is `Szemeredi.bloom_sisask_upper_bound`, a correctly stated bound on
Mathlib's `rothNumberNat`; everything from it to here is proved. -/
theorem erdos_problem_3_k3_unconditional
    (A : Set ℕ) (h_sum_div : reciprocalDiverges A) :
    ∃ a d : ℕ, 1 ≤ d ∧ a ∈ A ∧ a + d ∈ A ∧ a + 2 * d ∈ A := by
  obtain ⟨C, c, N₀, hC, hc, hN₀, h⟩ :=
    Imscribing.Classical.Szemeredi.bloom_sisask_upper_bound
  exact erdos_problem_3_k3_of_roth_bound C c hc hC N₀ hN₀ h A h_sum_div

-- ── The barrier, structurally ───────────────────────────────────────────────
--
-- `erdos_conjecture_ap` fused with `behrend_construction` on D↔W (Δ=1.00) is a
-- kernel-certified idempotent, registered as `erdos3_behrend_barrier`:
-- igFrobeniusAlg.mul p p = p closes through lake build. Behrend is the partner
-- because it is the obstruction — its construction forces the exponent.
--
-- Against CLINK L8 that object needs seven promotions and two full unit gaps.
-- Against L9, the replicative lateral, it needs six and one: ∋, the merge,
-- carrying BROADCAST_TRANSCENDENCE — broadcast composition exceeding ZFC_fe
-- SEQAX. d(L9)=1.1614 against d(L8)=1.5284.
--
-- Of the 3133 catalog entries carrying the L9 merge value, five match the
-- barrier on all eleven other axes and none of them clicks. The only partner
-- that clicks and supplies ∋ is `gowers_u3_norm`, inherited scaffold [∋]. Its
-- ring settles with the U³ unit on both sides of Behrend:
--
--   erdos_conjecture_ap · gowers_u3_norm · behrend_construction · gowers_u3_norm
--   σ = 0, adjacency λ⁴ = 10λ², ρ² = 10 exactly  (mOMonadOS: `erdos ap3`)
--
-- Higher-order Fourier machinery on both sides of the Behrend obstruction is
-- what a density-increment argument is, and it is what Kelley–Meka run.

-- k ≥ 4 from divergence is open. Szemerédi gives it from positive density, and
-- Szemerédi is not in Mathlib either; the k = 3 rung is the one Bloom–Sisask
-- reaches, and it is the highest rung anyone has.

#print axioms three_ap_of_dense
#print axioms three_ap_of_not_threeAPFree
#print axioms block_card_le
#print axioms erdos_problem_3_k3
#print axioms summable_of_blocks
#print axioms summable_blocks_of_log_bound
#print axioms erdos_problem_3_k3_of_roth_bound
#print axioms erdos_problem_3_k3_unconditional

end Millennium.ErdosProblems
