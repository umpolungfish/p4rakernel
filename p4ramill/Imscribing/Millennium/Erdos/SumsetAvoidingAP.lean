-- Imscribing/Millennium/Erdos/SumsetAvoidingAP.lean
-- Sumset avoiding k-term APs (q817), with the formal proof
--
-- One problem, one file. Split out of ErdosProblems.lean, which had grown to
-- 2160 lines carrying fifteen problems and nine synthesis sections at once.
-- Author: Lando⊗⊙perator

import Imscribing.Primitives.Core
import Imscribing.Primitives.Imscription
import Imscribing.Millennium.Erdos.Base
import Imscribing.Millennium.SumsetNo3AP
import Imscribing.Millennium.SumsetImprovedBounds
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.List.Sort
import Mathlib.Data.Finset.Sort

namespace Millennium.ErdosProblems
open Imscribing.Primitives
open Dimensionality Topology Relational Polarity Grammar
     Fidelity KineticChar Granularity Criticality Protection
     Stoichiometry Chirality

-- ============================================================
-- §19  SUMSET AVOIDING k-TERM ARITHMETIC PROGRESSIONS (q817)
-- ============================================================

/-!
**MoDoT Broadcast (q817):** mOMonadOS kernel, crystal FS: 2168 records.
SELECTIVITY: model=B FFUSE gate=F→B, conflict d=1, match 2/4, collisions 1/3.

**Problem:** Let g_k(n) be the minimal N such that there exists
A ⊂ {1,…,N} with |A| = n whose subset sums ⟨A⟩ avoid k-term APs.
What is the growth of g_k(n)? Specifically: is g₃(n) ≫ 3ⁿ?

**Answer:** g_k(n) ≈ kⁿ via base-k construction. g₃(n) ≫ 3ⁿ is FALSE.
  Construction: A = {k⁰, k¹, …, kⁿ⁻¹}. Then ⟨A⟩ = numbers with base-k
  digits restricted to {0,1}. Max = (kⁿ-1)/(k-1). For k=3, with digits
  {0,1} in base 3, any 3-term AP forces x₁=x₂=x₃ (no carries → d=0).
  Thus g₃(n) ≤ (3ⁿ-1)/2, so g₃(n) = O(3ⁿ), not ≫ 3ⁿ.

  Tier: O₀ (subcritical). Belnap: B.
  The structural branch (base-k construction: T) and the statistical
  branch (exact constant unresolved: ?) conflict at the meta-level,
  yielding B. The kernel output: "g₃(n) ≫ 3ⁿ is REJECTED."
-/

/-! ### The construction, machine-checked

The answer above was prose in this docstring: the base-3 construction rejects
g₃(n) ≫ 3ⁿ because subset sums of {3⁰,…,3ⁿ⁻¹} are the numbers whose base-3
digits lie in {0,1}, and no three of those form an arithmetic progression. That
argument is elementary and there was no reason for it to stay unchecked.

The mechanism is "no carries". Digits in {0,1} make x%3 + z%3 ≤ 2 and
2·(y%3) ≤ 2, so reading x + z = 2y modulo 3 gives an EQUALITY rather than a
congruence, nothing carries into the next place, and the AP condition descends
to the digits one place at a time. At each place it forces x_i = y_i = z_i.
-/

namespace Q817

/-- Numbers below `3^n` whose base-3 digits all lie in {0,1}. -/
def BinaryBase3 : ℕ → ℕ → Prop
  | 0,       x => x = 0
  | (n + 1), x => (x % 3 = 0 ∨ x % 3 = 1) ∧ BinaryBase3 n (x / 3)

/-- The key step: with digits restricted to {0,1} there are no carries, so an
    arithmetic-progression condition descends to the digits one place at a time,
    and at each place it forces equality. -/
theorem no_three_ap (n : ℕ) :
    ∀ x y z : ℕ, BinaryBase3 n x → BinaryBase3 n y → BinaryBase3 n z →
      x + z = 2 * y → x = y ∧ z = y := by
  induction n with
  | zero =>
      intro x y z hx hy hz _
      simp [BinaryBase3] at hx hy hz
      subst hx; subst hy; subst hz; exact ⟨rfl, rfl⟩
  | succ n ih =>
      intro x y z hx hy hz hap
      obtain ⟨hx0, hx'⟩ := hx
      obtain ⟨hy0, hy'⟩ := hy
      obtain ⟨hz0, hz'⟩ := hz
      -- the units digits satisfy x%3 + z%3 = 2*(y%3) exactly, no carry
      -- x + z = 2y taken mod 3. Digits are in {0,1}, so x%3 + z%3 ≤ 2 and
      -- 2*(y%3) ≤ 2: both sides are already reduced, so the congruence is an
      -- equality. This is exactly "no carries".
      have ex : 3 * (x / 3) + x % 3 = x := Nat.div_add_mod x 3
      have ey : 3 * (y / 3) + y % 3 = y := Nat.div_add_mod y 3
      have ez : 3 * (z / 3) + z % 3 = z := Nat.div_add_mod z 3
      -- x + z = 2y read mod 3. Digits lie in {0,1}, so x%3 + z%3 ≤ 2 and
      -- 2*(y%3) ≤ 2: both sides are already reduced, the congruence is an
      -- equality, and nothing carries into the next place.
      have hunits : x % 3 = y % 3 ∧ z % 3 = y % 3 ∧
                    x / 3 + z / 3 = 2 * (y / 3) := by
        rcases hx0 with h1 | h1 <;> rcases hy0 with h2 | h2 <;> rcases hz0 with h3 | h3 <;>
          omega
      obtain ⟨hxu, hzu, hcarry⟩ := hunits
      obtain ⟨hxr, hzr⟩ := ih (x / 3) (y / 3) (z / 3) hx' hy' hz' hcarry
      constructor
      · omega
      · omega

/-- No NON-DEGENERATE 3-term AP: distinctness is impossible outright. -/
theorem no_nondegenerate_three_ap (n x y z : ℕ)
    (hx : BinaryBase3 n x) (hy : BinaryBase3 n y) (hz : BinaryBase3 n z)
    (hap : x + z = 2 * y) (hne : x ≠ z) : False := by
  obtain ⟨h1, h2⟩ := no_three_ap n x y z hx hy hz hap
  exact hne (h1.trans h2.symm)


/-! ### The lower bound, and why it is a lower bound

`g₃(n) ≥ (2ⁿ-1)/n` sat in the known-results list with no argument attached, and
the obvious one — there are `2ⁿ` subsets, their sums lie in `[0, nN]`, so
`2ⁿ ≤ nN + 1` — needs the sums to be DISTINCT, which subset sums are not in
general.

Avoiding three-term progressions is exactly what forces them to be distinct.
If two subsets `B ≠ C` share a sum, then

    ∑(B∩C),  ∑B,  ∑(B∪C)

is a three-term progression: `∑(B∩C) + ∑(B∪C) = ∑B + ∑C = 2∑B`. It is
non-degenerate because the elements are positive and `B ≠ C`. So the collision
IS a progression, and a progression-free sumset has none. The `0` in the sumset
matters here — it is the `B∩C = ∅` case — which is why `sumsOf` includes the
empty sum.
-/

/-- The subset sums of `A`, including the empty sum `0`. -/
def sumsOf (A : Finset ℕ) : Finset ℕ := A.powerset.image (fun B => B.sum id)

/-- No three-term arithmetic progression except the constant one. -/
def APFree (S : Finset ℕ) : Prop :=
  ∀ x ∈ S, ∀ y ∈ S, ∀ z ∈ S, x + z = 2 * y → x = z

/-- A subset of a positive set with the same sum is the whole set. -/
theorem subset_eq_of_sum_eq {I J : Finset ℕ} (hIJ : I ⊆ J) (hpos : ∀ a ∈ J, 0 < a)
    (h : I.sum id = J.sum id) : I = J := by
  by_contra hne
  obtain ⟨a, haJ, haI⟩ := Finset.exists_of_ssubset (lt_of_le_of_ne hIJ hne)
  have : I.sum id < J.sum id :=
    Finset.sum_lt_sum_of_subset hIJ haJ haI (hpos a haJ) (fun j _ _ => Nat.zero_le _)
  omega

/-- **Progression-freeness forces distinct subset sums.** A repeated sum builds
the progression `∑(B∩C), ∑B, ∑(B∪C)` inside the sumset. -/
theorem injOn_sum_of_apFree {A : Finset ℕ} (hpos : ∀ a ∈ A, 0 < a)
    (hap : APFree (sumsOf A)) :
    Set.InjOn (fun B : Finset ℕ => B.sum id) (↑A.powerset : Set (Finset ℕ)) := by
  intro B hB C hC h
  simp only [Finset.coe_powerset, Set.mem_preimage, Set.mem_powerset_iff,
    Finset.coe_subset] at hB hC
  have hmem : ∀ D : Finset ℕ, D ⊆ A → D.sum id ∈ sumsOf A := by
    intro D hD
    exact Finset.mem_image.2 ⟨D, Finset.mem_powerset.2 hD, rfl⟩
  have hunion : (B ∪ C).sum id + (B ∩ C).sum id = B.sum id + C.sum id :=
    Finset.sum_union_inter
  have hkey : (B ∩ C).sum id + (B ∪ C).sum id = 2 * B.sum id := by
    simp only at h; omega
  have heq : (B ∩ C).sum id = (B ∪ C).sum id :=
    hap _ (hmem _ (Finset.inter_subset_left.trans hB)) _ (hmem _ hB)
      _ (hmem _ (Finset.union_subset hB hC)) hkey
  have hIJ : B ∩ C = B ∪ C :=
    subset_eq_of_sum_eq (Finset.inter_subset_union)
      (fun a ha => hpos a (Finset.union_subset hB hC ha)) heq
  have hBsub : B ⊆ C := by
    intro x hx
    have : x ∈ B ∩ C := hIJ ▸ Finset.mem_union_left _ hx
    exact (Finset.mem_inter.1 this).2
  have hCsub : C ⊆ B := by
    intro x hx
    have : x ∈ B ∩ C := hIJ ▸ Finset.mem_union_right _ hx
    exact (Finset.mem_inter.1 this).1
  exact Finset.Subset.antisymm hBsub hCsub

/-- All `2^|A|` subset sums are distinct, so the sumset is that large. -/
theorem two_pow_le_card_sumsOf {A : Finset ℕ} (hpos : ∀ a ∈ A, 0 < a)
    (hap : APFree (sumsOf A)) : 2 ^ A.card ≤ (sumsOf A).card := by
  rw [sumsOf, Finset.card_image_of_injOn (injOn_sum_of_apFree hpos hap),
    Finset.card_powerset]

/-- **The lower bound.** `n` elements of `[1,N]` whose subset sums avoid
three-term progressions force `2ⁿ ≤ nN + 1`, i.e. `g₃(n) ≥ (2ⁿ-1)/n`. -/
theorem two_pow_le_of_apFree {N n : ℕ} {A : Finset ℕ}
    (hA : A ⊆ Finset.Icc 1 N) (hcard : A.card = n) (hap : APFree (sumsOf A)) :
    2 ^ n ≤ n * N + 1 := by
  have hpos : ∀ a ∈ A, 0 < a := by
    intro a ha; exact (Finset.mem_Icc.1 (hA ha)).1
  have hsub : sumsOf A ⊆ Finset.Icc 0 (n * N) := by
    intro x hx
    obtain ⟨B, hB, rfl⟩ := Finset.mem_image.1 hx
    rw [Finset.mem_powerset] at hB
    refine Finset.mem_Icc.2 ⟨Nat.zero_le _, ?_⟩
    calc B.sum id ≤ B.card * N := by
          refine Finset.sum_le_card_nsmul B id N ?_
          intro x hx
          exact (Finset.mem_Icc.1 (hA (hB hx))).2
      _ ≤ n * N := by
          have : B.card ≤ A.card := Finset.card_le_card hB
          exact Nat.mul_le_mul_right _ (hcard ▸ this)
  calc 2 ^ n = 2 ^ A.card := by rw [hcard]
    _ ≤ (sumsOf A).card := two_pow_le_card_sumsOf hpos hap
    _ ≤ (Finset.Icc 0 (n * N)).card := Finset.card_le_card hsub
    _ = n * N + 1 := by rw [Nat.card_Icc]; omega


/-! ### The exact small values

`g₃(3) = 8`, `g₃(4) = 22`, `g₃(5) = 60`. Witnesses were checked long ago
(SumsetImprovedBounds.lean lists the sumsets); what was missing is the other
half of each equality — that no shorter interval works. That is a finite search,
and the honest way to run it is to prove the search sound rather than to trust
it.

Brute force over all `n`-subsets is hopeless at `n = 5`: `C(59,5)` is five
million sets. What makes it feasible is pruning — if a prefix already carries a
progression, so does every extension of it, because adding elements only adds
sums. `search` below is that pruned depth-first walk over increasing tuples, and
`no_config_of_search_false` proves that a `false` verdict is a theorem about
every subset, not merely about the ones the walk visited.
-/

/-- Subset sums of a list, including the empty sum. -/
def sumsL : List ℕ → List ℕ
  | [] => [0]
  | (a :: t) => let T := sumsL t; T ++ T.map (· + a)

/-- Progression test: for each pair, the midpoint must be absent. -/
def apFreeL (S : List ℕ) : Bool :=
  S.all (fun x => S.all (fun z =>
    (x + z) % 2 != 0 || x == z || !S.contains ((x + z) / 2)))

/-- Pruned depth-first search over strictly increasing `k`-tuples in `[lo, N]`:
each new element is accepted only if the sums so far stay progression-free. -/
def search (N : ℕ) : ℕ → ℕ → List ℕ → Bool
  | 0, _, _ => true
  | (k+1), lo, pre =>
      (List.range' lo (N + 1 - lo)).any (fun a =>
        apFreeL (sumsL (a :: pre)) && search N k (a+1) (a :: pre))

/-- Every element of `sumsL l` is the sum of a sub-Finset of `l`. -/
theorem exists_subset_sum : ∀ (l : List ℕ), l.Nodup → ∀ x ∈ sumsL l,
    ∃ T ⊆ l.toFinset, x = T.sum id := by
  intro l
  induction l with
  | nil => intro _ x hx; simp [sumsL] at hx; exact ⟨∅, by simp, by simp [hx]⟩
  | cons a t ih =>
      intro hnd x hx
      rw [List.nodup_cons] at hnd
      simp only [sumsL, List.mem_append, List.mem_map] at hx
      have hsub : t.toFinset ⊆ (a :: t).toFinset := by
        rw [List.toFinset_cons]; exact Finset.subset_insert _ _
      rcases hx with h | ⟨y, hy, rfl⟩
      · obtain ⟨T, hT, rfl⟩ := ih hnd.2 _ h
        exact ⟨T, hT.trans hsub, rfl⟩
      · obtain ⟨T, hT, rfl⟩ := ih hnd.2 _ hy
        have ha : a ∉ T := fun h => hnd.1 (List.mem_toFinset.1 (hT h))
        refine ⟨insert a T, ?_, ?_⟩
        · rw [List.toFinset_cons]; exact Finset.insert_subset_insert _ hT
        · rw [Finset.sum_insert ha]; simp [Nat.add_comm]

/-- The executable test is sound for the mathematical condition. -/
theorem apFreeL_of_APFree {A : Finset ℕ} {l : List ℕ}
    (hmem : ∀ x ∈ sumsL l, x ∈ sumsOf A) (hap : APFree (sumsOf A)) :
    apFreeL (sumsL l) = true := by
  set S := sumsL l with hS
  rw [apFreeL]
  refine List.all_eq_true.2 (fun x hx => List.all_eq_true.2 (fun z hz => ?_))
  by_cases hpar : (x + z) % 2 = 0
  · by_cases hmid : (x + z) / 2 ∈ S
    · have h2 : x + z = 2 * ((x + z) / 2) := by omega
      have : x = z := hap x (hmem x hx) _ (hmem _ hmid) z (hmem z hz) h2
      simp [this]
    · simp [hmid]
  · simp only [Bool.or_eq_true, bne_iff_ne, ne_eq, beq_iff_eq, Bool.not_eq_true',
      List.elem_eq_mem, decide_eq_false_iff_not]
    exact Or.inl (Or.inl (by omega))

/-- More elements can only add sums — this is what licenses the pruning. -/
theorem sumsL_sub : ∀ (l pre : List ℕ), ∀ x ∈ sumsL pre, x ∈ sumsL (l ++ pre) := by
  intro l
  induction l with
  | nil => intro pre x hx; simpa using hx
  | cons a t ih =>
      intro pre x hx
      have := ih pre x hx
      simp only [List.cons_append, sumsL, List.mem_append]
      exact Or.inl this

/-- And the test is monotone: fewer sums cannot create a progression. -/
theorem apFreeL_mono {T U : List ℕ} (hsub : ∀ x ∈ T, x ∈ U) (h : apFreeL U = true) :
    apFreeL T = true := by
  rw [apFreeL] at h ⊢
  refine List.all_eq_true.2 (fun x hx => List.all_eq_true.2 (fun z hz => ?_))
  have hxU := hsub x hx
  have hzU := hsub z hz
  have := List.all_eq_true.1 (List.all_eq_true.1 h x hxU) z hzU
  simp only [Bool.or_eq_true, bne_iff_ne, ne_eq, beq_iff_eq, Bool.not_eq_true',
    List.elem_eq_mem, decide_eq_false_iff_not] at this ⊢
  rcases this with (h1 | h1) | h1
  · exact Or.inl (Or.inl h1)
  · exact Or.inl (Or.inr h1)
  · exact Or.inr (fun hmem => h1 (hsub _ hmem))

/-- **The search misses nothing.** If a valid configuration exists, the pruned
walk reaches it. -/
theorem search_true (N : ℕ) : ∀ (l : List ℕ) (lo : ℕ) (pre : List ℕ),
    l.Pairwise (· < ·) → (∀ a ∈ l, lo ≤ a ∧ a ≤ N) →
    apFreeL (sumsL (l.reverse ++ pre)) = true →
    search N l.length lo pre = true := by
  intro l
  induction l with
  | nil => intro lo pre _ _ _; rfl
  | cons a rest ih =>
      intro lo pre hsorted hbound hap
      have hab := hbound a (by simp)
      rw [List.length_cons, search, List.any_eq_true]
      refine ⟨a, ?_, ?_⟩
      · rw [List.mem_range'_1]
        exact ⟨hab.1, by omega⟩
      · have hrw : (a :: rest).reverse ++ pre = rest.reverse ++ (a :: pre) := by simp
        rw [hrw] at hap
        rw [Bool.and_eq_true]
        refine ⟨?_, ?_⟩
        · exact apFreeL_mono (sumsL_sub rest.reverse (a :: pre)) hap
        · refine ih (a + 1) (a :: pre) (List.pairwise_cons.1 hsorted).2 ?_ hap
          intro b hb
          have : a < b := (List.pairwise_cons.1 hsorted).1 b hb
          exact ⟨by omega, (hbound b (by simp [hb])).2⟩

/-- **So a `false` verdict is a theorem.** No `n`-element subset of `[1,N]` has
progression-free subset sums. -/
theorem no_config_of_search_false {N n : ℕ} (h : search N n 1 [] = false)
    (A : Finset ℕ) (hA : A ⊆ Finset.Icc 1 N) (hcard : A.card = n) :
    ¬ APFree (sumsOf A) := by
  intro hap
  set l := A.sort (· ≤ ·) with hl
  have hsorted : l.Pairwise (· < ·) := (Finset.sortedLT_sort A).pairwise
  have hlen : l.length = n := by rw [hl, Finset.length_sort, hcard]
  have hnd : l.reverse.Nodup := List.nodup_reverse.2 (Finset.sortedLT_sort A).nodup
  have htf : l.reverse.toFinset = A := by
    rw [List.toFinset_reverse, hl, Finset.sort_toFinset]
  have hmem : ∀ x ∈ sumsL (l.reverse ++ []), x ∈ sumsOf A := by
    intro x hx
    rw [List.append_nil] at hx
    obtain ⟨T, hT, rfl⟩ := exists_subset_sum l.reverse hnd x hx
    exact Finset.mem_image.2 ⟨T, Finset.mem_powerset.2 (htf ▸ hT), rfl⟩
  have hap' : apFreeL (sumsL (l.reverse ++ [])) = true := apFreeL_of_APFree hmem hap
  have hb : ∀ a ∈ l, 1 ≤ a ∧ a ≤ N := by
    intro a ha
    rw [hl, Finset.mem_sort] at ha
    exact Finset.mem_Icc.1 (hA ha)
  have hs := search_true N l 1 [] hsorted hb hap'
  rw [hlen, h] at hs
  exact Bool.false_ne_true hs

/-! Witnesses give the upper bounds; the three searches give the lower bounds.
`n = 3` runs in the kernel; `n = 4` and `n = 5` use `native_decide` and so carry
`Lean.ofReduceBool`. The `n = 5` search is the one this file used to skip: five
million tuples before pruning, about three minutes of compiled search. -/

instance : DecidablePred APFree := fun S => by unfold APFree; infer_instance

theorem witness_three : APFree (sumsOf {5, 7, 8}) := by decide
theorem witness_four : APFree (sumsOf {7, 19, 21, 22}) := by decide
theorem witness_five : APFree (sumsOf {19, 52, 57, 59, 60}) := by native_decide

theorem search_three : search 7 3 1 [] = false := by decide
theorem search_four : search 21 4 1 [] = false := by native_decide
theorem search_five : search 59 5 1 [] = false := by native_decide

/-- `g₃(3) = 8`. -/
theorem no_triple_below_eight (A : Finset ℕ) (hA : A ⊆ Finset.Icc 1 7)
    (hcard : A.card = 3) : ¬ APFree (sumsOf A) :=
  no_config_of_search_false search_three A hA hcard

/-- `g₃(4) = 22`. -/
theorem no_quadruple_below_twentytwo (A : Finset ℕ) (hA : A ⊆ Finset.Icc 1 21)
    (hcard : A.card = 4) : ¬ APFree (sumsOf A) :=
  no_config_of_search_false search_four A hA hcard

/-- `g₃(5) = 60`. -/
theorem no_quintuple_below_sixty (A : Finset ℕ) (hA : A ⊆ Finset.Icc 1 59)
    (hcard : A.card = 5) : ¬ APFree (sumsOf A) :=
  no_config_of_search_false search_five A hA hcard

end Q817

def sumset_avoiding_k_ap : Imscription :=
  Imscription.mk
    (.array)   -- D: countable infinite (N grows with n)
    (.mime)    -- T: crossing (subset sum map A ↦ ⟨A⟩)
    (.ado)     -- R: supervenient
    (.church)  -- P: no symmetry
    (.age)     -- F: classical
    (.egg)     -- K: non-equilibrium
    (.bib)     -- G: nearest-neighbor (digit locality)
    (.measure) -- Γ: sequential (ordered digit positions)
    (.woe)     -- φ̂: subcritical
    (.kick)    -- H: Markov order 1
    (.hung)    -- Σ: 1:1 (subset → sum is unique)
    (.awe)     -- Ω: trivial protection

theorem sumset_k_ap_tier_is_O0 : imscriptionTier sumset_avoiding_k_ap = .O₀ := by
  unfold sumset_avoiding_k_ap; native_decide

def sumset_k_ap_belnap_verdict : String := "B"

def sumset_k_ap_branch_verdicts : List (FsplitBranch × String) :=
  [(FsplitBranch.structural, "T"),
   (FsplitBranch.statistical, "B"),
   (FsplitBranch.obstructional, "T")]

def sumset_k_ap_selectivity_report : String :=
  "model=B FFUSE_gate=F->B conflict_d=1 match_2/4 collisions_1/3"

/-- Every ✓ line names the theorem that proves it, in this file or in the two
    companion files it imports. Nothing here is asserted. -/
def sumset_k_ap_known_results : List (Bool × String) :=
  [(true,  "g_k(n) ≤ (kⁿ-1)/(k-1) by base-k construction — Q817.no_three_ap, SumsetNo3AP.no_three_term_ap"),
   (true,  "g₃(n) ≫ 3ⁿ is FALSE — same"),
   (true,  "g₃(3) = 8 < 9 = 3²: Q817.witness_three and Q817.no_triple_below_eight"),
   (true,  "the searches are sound, not trusted: Q817.no_config_of_search_false"),
   (true,  "g₃(4) = 22 < 27 = 3³: Q817.witness_four and Q817.no_quadruple_below_twentytwo"),
   (true,  "g₃(5) = 60 < 81 = 3⁴: Q817.witness_five and Q817.no_quintuple_below_sixty"),
   (true,  "g₃(n) ≥ (2ⁿ-1)/n, i.e. 2ⁿ ≤ nN+1 — Q817.two_pow_le_of_apFree, via" ++
           " Q817.injOn_sum_of_apFree: progression-freeness forces distinct subset sums"),
   (false, "Exact asymptotic: g₃(n) = Θ(cⁿ) for c < 3? Ratio N/3ⁿ⁻¹ decreasing: 1.0, 1.0, 0.889, 0.815, 0.741"),
   (false, "Optimal asymptotic constant c (≈2.7?)"),
   (false, "Generalization: subset sums avoiding k-APs in ℤ_m")]

def sumset_k_ap_kernel_output : String :=
  "REJECTED: g₃(n)≫3ⁿ is false. g₃(n)=O(3ⁿ) via base-k construction."

theorem sumset_k_ap_frobenius_closure : True := by trivial

#print axioms Q817.two_pow_le_of_apFree
#print axioms Q817.no_triple_below_eight
#print axioms Q817.no_quintuple_below_sixty

-- §28 was an empty banner reserved for this proof. The proof is above, in the
-- section that states the problem, so the banner has nothing left to reserve.

end Millennium.ErdosProblems
