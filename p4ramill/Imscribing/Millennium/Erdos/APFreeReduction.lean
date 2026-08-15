import Mathlib
import Imscribing.Classical.Szemeredi

/-!
# Erdős's conjecture on arithmetic progressions, at every `k`

If `Σ 1/a` over `A` diverges, `A` contains a `k`-term arithmetic progression —
reduced, for every `k`, to a counting bound past exponent one.

The `k = 3` development proves this through Mathlib's `ThreeAPFree` and
`rothNumberNat`, and leans on `addRothNumber_Ico` for translation invariance.
Neither of those exists for `k ≥ 4`. What is 3-specific is exactly that one
lemma, so it is proved here directly: `card_le_r_k` shifts a progression-free
subset of any interval down to `range N` and observes that a progression in the
image lifts back by adding the offset.

Everything after it is indifferent to `k`. The dyadic decomposition, the block
estimate, the transport from a subtype to an indicator and the comparison with a
`p`-series never mention the length of a progression; they mention only the
counting function that bounds it.

The conclusion is therefore uniform in `k`: given

    r_k(N) ≤ C·N/(log N)^(1+ε)    for some ε > 0 and all large N,

divergent reciprocals force a `k`-term progression. At `k = 3` such a bound is
known (Bloom–Sisask; Kelley–Meka is stronger). For `k ≥ 4` none is known, and
this file states precisely which inequality would close the case.
-/

open Finset
open scoped Classical BigOperators

namespace Millennium.ErdosProblems.APFree

open Imscribing.Classical.Szemeredi

/-- `A` carries no `k`-term progression with positive common difference. The set
form of `Szemeredi.APFree`. -/
def SetAPFree (k : ℕ) (A : Set ℕ) : Prop :=
  ∀ a d : ℕ, 0 < d → ¬ (∀ i, i < k → a + i * d ∈ A)

/-- Progression-freeness passes to any finite subset. -/
theorem apFree_of_subset {k : ℕ} {A : Set ℕ} (hA : SetAPFree k A)
    (S : Finset ℕ) (hS : ∀ x ∈ S, x ∈ A) : APFree k S := by
  intro a d hd hcontra
  exact hA a d hd (fun i hi => hS _ (hcontra i hi))

/-- **Translation invariance at every `k`.**

A `k`-progression-free subset of an interval of length `N` is no larger than
`r_k k N`. Mathlib supplies this for `k = 3` as `addRothNumber_Ico`; for general
`k` it is proved here, by shifting to `range N` and lifting any progression in
the image back by the offset. -/
theorem card_le_r_k (k N m : ℕ) (A : Finset ℕ)
    (hsub : A ⊆ Finset.Ico m (m + N)) (hA : APFree k A) :
    A.card ≤ r_k k N := by
  set B : Finset ℕ := A.image (fun x => x - m) with hB
  have hmem : ∀ x ∈ A, m ≤ x ∧ x < m + N := by
    intro x hx
    have := hsub hx
    rw [Finset.mem_Ico] at this
    exact this
  have hinj : Set.InjOn (fun x => x - m) A := by
    intro x hx y hy hxy
    have hx' := hmem x hx
    have hy' := hmem y hy
    simp only at hxy
    omega
  have hcard : B.card = A.card := by rw [hB, Finset.card_image_of_injOn hinj]
  have hBsub : B ⊆ Finset.range N := by
    intro b hb
    rw [hB, Finset.mem_image] at hb
    obtain ⟨x, hx, rfl⟩ := hb
    have := hmem x hx
    rw [Finset.mem_range]
    omega
  have hBfree : APFree k B := by
    intro a d hd hcontra
    refine hA (a + m) d hd ?_
    intro i hi
    have hbi : a + i * d ∈ B := hcontra i hi
    rw [hB, Finset.mem_image] at hbi
    obtain ⟨x, hx, hxeq⟩ := hbi
    have hx2 := hmem x hx
    have hxv : x = a + i * d + m := by omega
    subst hxv
    have hcomm : a + m + i * d = a + i * d + m := by ring
    rw [hcomm]
    exact hx
  rw [← hcard]
  unfold r_k
  refine Finset.le_sup (f := fun A : Finset ℕ => A.card) ?_
  rw [Finset.mem_filter, Finset.mem_powerset]
  exact ⟨hBsub, hBfree⟩

/-- The dyadic block `[2^j, 2^(j+1))` has length `2^j`. -/
theorem block_card_le (k : ℕ) (A : Finset ℕ) (j : ℕ)
    (hsub : A ⊆ Finset.Ico (2 ^ j) (2 ^ (j + 1)))
    (hA : APFree k A) :
    A.card ≤ r_k k (2 ^ j) := by
  refine card_le_r_k k (2 ^ j) (2 ^ j) A ?_ hA
  have : (2 : ℕ) ^ j + 2 ^ j = 2 ^ (j + 1) := by ring
  rwa [this]

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

/-- Over one block the reciprocals are bounded by `r_k(2^j)/2^j`. -/
theorem block_sum_le (k : ℕ) (A : Set ℕ) (hA : SetAPFree k A) (j : ℕ) :
    ∑ i ∈ Finset.Ico (2 ^ j) (2 ^ (j + 1)), A.indicator (fun m => (1 : ℝ) / m) i
      ≤ (r_k k (2 ^ j) : ℝ) / 2 ^ j := by
  set S : Finset ℕ := (Finset.Ico (2 ^ j) (2 ^ (j + 1))).filter (· ∈ A) with hS
  have hcollapse :
      ∑ i ∈ Finset.Ico (2 ^ j) (2 ^ (j + 1)), A.indicator (fun m => (1 : ℝ) / m) i
        = ∑ i ∈ S, (1 : ℝ) / i := by
    rw [hS, Finset.sum_filter]
    exact Finset.sum_congr rfl (fun i _ => by simp [Set.indicator_apply])
  have hterm : ∀ i ∈ S, (1 : ℝ) / i ≤ 1 / 2 ^ j := by
    intro i hi
    rw [hS, Finset.mem_filter, Finset.mem_Ico] at hi
    have : (2 : ℝ) ^ j ≤ (i : ℝ) := by exact_mod_cast hi.1.1
    exact one_div_le_one_div_of_le (by positivity) this
  have hcard : S.card ≤ r_k k (2 ^ j) := by
    refine block_card_le k S j (Finset.filter_subset _ _) ?_
    refine apFree_of_subset hA S ?_
    intro x hx
    rw [hS, Finset.mem_filter] at hx
    exact hx.2
  calc ∑ i ∈ Finset.Ico (2 ^ j) (2 ^ (j + 1)), A.indicator (fun m => (1 : ℝ) / m) i
      = ∑ i ∈ S, (1 : ℝ) / i := hcollapse
    _ ≤ S.card • ((1 : ℝ) / 2 ^ j) := Finset.sum_le_card_nsmul S _ _ hterm
    _ = (S.card : ℝ) / 2 ^ j := by simp [nsmul_eq_mul]; ring
    _ ≤ (r_k k (2 ^ j) : ℝ) / 2 ^ j := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        exact_mod_cast hcard

/-- If the block bounds sum, a progression-free set has convergent reciprocals. -/
theorem summable_of_blocks (k : ℕ) (A : Set ℕ) (hA : SetAPFree k A)
    (hb : Summable (fun j : ℕ => (r_k k (2 ^ j) : ℝ) / 2 ^ j)) :
    Summable (fun n : {n // n ∈ A} => (1 / (n.1 : ℝ))) := by
  have hcomp : (fun n : {n // n ∈ A} => (1 : ℝ) / (n.1 : ℝ))
      = (fun m : ℕ => (1 : ℝ) / (m : ℝ)) ∘ Subtype.val := rfl
  rw [hcomp, summable_subtype_iff_indicator]
  set g : ℕ → ℝ := A.indicator (fun m => (1 : ℝ) / m) with hg
  have hnonneg : ∀ n, 0 ≤ g n := by
    intro n; rw [hg]; unfold Set.indicator; split <;> positivity
  refine summable_of_sum_range_le hnonneg (c := ∑' j : ℕ, (r_k k (2 ^ j) : ℝ) / 2 ^ j) ?_
  intro N
  have hNJ : N ≤ 2 ^ N := Nat.le_of_lt (Nat.lt_two_pow_self)
  have hstep1 : ∑ i ∈ Finset.range N, g i ≤ ∑ i ∈ Finset.range (2 ^ N), g i :=
    Finset.sum_le_sum_of_subset_of_nonneg
      (fun x hx => Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp hx) hNJ))
      (fun i _ _ => hnonneg i)
  have hzero : g 0 = 0 := by rw [hg]; unfold Set.indicator; split <;> simp
  have hsplit0 : ∑ i ∈ Finset.range (2 ^ N), g i = ∑ i ∈ Finset.Ico 1 (2 ^ N), g i := by
    rw [Finset.range_eq_Ico,
      ← Finset.sum_Ico_consecutive g (Nat.zero_le 1) Nat.one_le_two_pow]
    simp [hzero]
  calc ∑ i ∈ Finset.range N, g i ≤ ∑ i ∈ Finset.range (2 ^ N), g i := hstep1
    _ = ∑ i ∈ Finset.Ico 1 (2 ^ N), g i := hsplit0
    _ = ∑ j ∈ Finset.range N, ∑ i ∈ Finset.Ico (2 ^ j) (2 ^ (j + 1)), g i := dyadic_split g N
    _ ≤ ∑ j ∈ Finset.range N, (r_k k (2 ^ j) : ℝ) / 2 ^ j :=
        Finset.sum_le_sum (fun j _ => block_sum_le k A hA j)
    _ ≤ _ := hb.sum_le_tsum _ (fun j _ => by positivity)

/-- A counting bound past exponent one makes the block terms sum. -/
theorem summable_blocks_of_log_bound (k : ℕ)
    (C ε : ℝ) (hε : 0 < ε) (hC : 0 ≤ C) (N₀ : ℕ) (hN₀ : 1 ≤ N₀)
    (h : ∀ N : ℕ, N₀ ≤ N → (r_k k N : ℝ) ≤ C * N / (Real.log N) ^ (1 + ε)) :
    Summable (fun j : ℕ => (r_k k (2 ^ j) : ℝ) / 2 ^ j) := by
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  set K : ℝ := C / (Real.log 2) ^ (1 + ε) with hK
  have hKnn : 0 ≤ K := div_nonneg hC (le_of_lt (Real.rpow_pos_of_pos hlog2 _))
  have hp : Summable (fun j : ℕ => K * (1 / (j : ℝ) ^ (1 + ε))) :=
    (Real.summable_one_div_nat_rpow.mpr (by linarith)).mul_left K
  rw [← summable_nat_add_iff N₀]
  refine Summable.of_nonneg_of_le (fun j => by positivity) ?_ ((summable_nat_add_iff N₀).mpr hp)
  intro j
  set n : ℕ := j + N₀ with hn
  have h2n : (N₀ : ℕ) ≤ 2 ^ n :=
    le_trans (Nat.le_of_lt (Nat.lt_two_pow_self)) (Nat.pow_le_pow_right (by norm_num) (by omega))
  have hbound := h (2 ^ n) h2n
  have hlogpow : Real.log ((2 : ℕ) ^ n : ℕ) = n * Real.log 2 := by push_cast; rw [Real.log_pow]
  have hpos : (0 : ℝ) < (2 : ℝ) ^ n := by positivity
  have hnpos : (0 : ℝ) < (n : ℝ) := by
    have : 1 ≤ n := by omega
    exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one this
  have hsplit : ((n : ℝ) * Real.log 2) ^ (1 + ε)
      = (n : ℝ) ^ (1 + ε) * (Real.log 2) ^ (1 + ε) :=
    Real.mul_rpow (le_of_lt hnpos) (le_of_lt hlog2)
  calc (r_k k (2 ^ n) : ℝ) / 2 ^ n
      ≤ (C * ((2:ℕ) ^ n : ℕ) / (Real.log ((2:ℕ) ^ n : ℕ)) ^ (1 + ε)) / 2 ^ n := by gcongr
    _ = K * (1 / (n : ℝ) ^ (1 + ε)) := by
        rw [hlogpow]; push_cast; rw [hsplit, hK]; field_simp


/-! ## What is not enough

The reduction needs the dyadic series `Σ_j r_k(2^j)/2^j` to converge. Two shapes
of bound that are actually known for `k ≥ 4` fail it, and fail it provably rather
than merely failing to be strong enough for a proof anyone has written.
-/

/-- For every `c > 0`, the series `Σ 1/(log j)^c` diverges. -/
theorem not_summable_one_div_log_rpow (c : ℝ) (hc : 0 < c) :
    ¬ Summable (fun j : ℕ => 1 / (Real.log j) ^ c) := by
  intro hsum
  -- log j ≤ c · j^(1/c), so (log j)^c ≤ c^c · j
  have key : ∀ j : ℕ, 3 ≤ j → (Real.log j) ^ c ≤ c ^ c * j := by
    intro j hj
    have hj0 : (0 : ℝ) ≤ (j : ℝ) := by positivity
    have hlog : Real.log j ≤ (j : ℝ) ^ (1/c) / (1/c) :=
      Real.log_le_rpow_div hj0 (by positivity)
    have hlognn : 0 ≤ Real.log j := Real.log_nonneg (by exact_mod_cast Nat.one_le_of_lt hj)
    have h1 : (Real.log j) ^ c ≤ ((j : ℝ) ^ (1/c) / (1/c)) ^ c :=
      Real.rpow_le_rpow hlognn hlog (le_of_lt hc)
    have h2 : ((j : ℝ) ^ (1/c) / (1/c)) ^ c = c ^ c * (j : ℝ) := by
      rw [div_eq_mul_inv, one_div, inv_inv, mul_comm,
        Real.mul_rpow (le_of_lt hc) (by positivity),
        ← Real.rpow_mul hj0, inv_mul_cancel₀ (ne_of_gt hc), Real.rpow_one]
    rw [h2] at h1
    exact h1
  -- hence 1/(c^c · j) ≤ 1/(log j)^c, and the harmonic series would be summable
  have hcc : (0 : ℝ) < c ^ c := Real.rpow_pos_of_pos hc c
  have hshift := (summable_nat_add_iff 3).mpr hsum
  have hcomp : Summable (fun j : ℕ => 1 / (c ^ c * ((j + 3 : ℕ) : ℝ))) := by
    refine Summable.of_nonneg_of_le (fun j => by positivity) ?_ hshift
    intro j
    have hj3 : 3 ≤ j + 3 := by omega
    have hk := key (j + 3) hj3
    have hlogpos : 0 < Real.log ((j : ℕ) + 3 : ℕ) := by
      apply Real.log_pos
      have : (3 : ℝ) ≤ ((j + 3 : ℕ) : ℝ) := by exact_mod_cast hj3
      linarith
    have hlrpow : 0 < (Real.log ((j + 3 : ℕ) : ℝ)) ^ c := Real.rpow_pos_of_pos hlogpos c
    exact one_div_le_one_div_of_le hlrpow hk
  -- strip the constant and the shift: the harmonic series is not summable
  have : Summable (fun j : ℕ => 1 / ((j + 3 : ℕ) : ℝ)) := by
    have := hcomp.mul_left (c ^ c)
    refine this.congr (fun j => ?_)
    field_simp
  exact Real.not_summable_one_div_natCast ((summable_nat_add_iff 3).mp this)

/-- **Exponent one is not enough.** A bound `r_k(N) ≤ C·N/log N` gives dyadic
terms `C/(j·log 2)`, and the harmonic series diverges.

This is the knife-edge. Roth's own bound for `k = 3` has exactly this shape, and
every bound at exponent one, however small the constant, leaves the dyadic sum
divergent. Only `1 + ε` closes it. -/
theorem not_summable_at_exponent_one (C : ℝ) (hC : 0 < C) :
    ¬ Summable (fun j : ℕ => C / ((j : ℝ) * Real.log 2)) := by
  intro hsum
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have : Summable (fun j : ℕ => 1 / (j : ℝ)) := by
    have h := hsum.mul_left (Real.log 2 / C)
    refine h.congr (fun j => ?_)
    field_simp
  exact Real.not_summable_one_div_natCast this

/-- **A `log log` bound is not enough, at any exponent.**

Gowers' bound for general `k`, and the Leng--Sah--Sawhney improvement, have the
shape `r_k(N) ≤ C·N/(log log N)^c` or weaker. At `N = 2^j` that leaves terms of
order `1/(log j)^c`, which diverge for every `c > 0` by
`not_summable_one_div_log_rpow`. No improvement of the constant, and no increase
of the exponent `c`, changes this: the shape itself is insufficient. What the
reduction requires is a bound polylogarithmic in `N`, past exponent one --- known
at `k = 3`, and at `k = 4` known only with an exponent far below one. -/
theorem loglog_shape_insufficient (c : ℝ) (hc : 0 < c) :
    ¬ Summable (fun j : ℕ => 1 / (Real.log j) ^ c) :=
  not_summable_one_div_log_rpow c hc

/-- **Erdős's conjecture at `k`, from a counting bound past exponent one.**

Divergent reciprocals force a `k`-term arithmetic progression, given

    r_k(N) ≤ C·N/(log N)^(1+ε).

Uniform in `k`: the reduction never uses the length of a progression, only the
counting function bounding it. At `k = 3` the hypothesis is a theorem
(Bloom–Sisask). For `k ≥ 4` it is open, and it is the whole of what is open. -/
theorem erdos_conjecture_of_bound (k : ℕ)
    (C ε : ℝ) (hε : 0 < ε) (hC : 0 ≤ C) (N₀ : ℕ) (hN₀ : 1 ≤ N₀)
    (hbound : ∀ N : ℕ, N₀ ≤ N → (r_k k N : ℝ) ≤ C * N / (Real.log N) ^ (1 + ε))
    (A : Set ℕ)
    (hdiv : ¬ Summable (fun n : {n // n ∈ A} => (1 / (n.1 : ℝ)))) :
    ∃ a d : ℕ, 0 < d ∧ ∀ i, i < k → a + i * d ∈ A := by
  by_contra hcon
  push_neg at hcon
  have hfree : SetAPFree k A := by
    intro a d hd hall
    obtain ⟨i, hi, hnot⟩ := hcon a d hd
    exact hnot (hall i hi)
  exact hdiv (summable_of_blocks k A hfree
    (summable_blocks_of_log_bound k C ε hε hC N₀ hN₀ hbound))

#print axioms card_le_r_k
#print axioms block_sum_le
#print axioms summable_of_blocks
#print axioms summable_blocks_of_log_bound
#print axioms erdos_conjecture_of_bound
#print axioms not_summable_one_div_log_rpow
#print axioms not_summable_at_exponent_one

end Millennium.ErdosProblems.APFree
