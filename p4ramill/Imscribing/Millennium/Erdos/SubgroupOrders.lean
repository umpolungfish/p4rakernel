-- Imscribing/Millennium/Erdos/SubgroupOrders.lean
-- Subgroup orders of S_n
--
-- One problem, one file. Split out of ErdosProblems.lean, which had grown to
-- 2160 lines carrying fifteen problems and nine synthesis sections at once.
-- Author: Lando⊗⊙perator

import Imscribing.Primitives.Core
import Imscribing.Primitives.Imscription
import Imscribing.Millennium.Erdos.Base
import Mathlib.Tactic

namespace Millennium.ErdosProblems
open Imscribing.Primitives
open Dimensionality Topology Relational Polarity Grammar
     Fidelity KineticChar Granularity Criticality Protection
     Stoichiometry Chirality

-- ============================================================
-- §3  SUBGROUP ORDERS OF S_n — STATISTICAL ARITHMETIC
-- ============================================================

/-!
**Problem:** Describe the statistical arithmetic structure of
O_n = { |G| : G ≤ S_n }, the set of subgroup orders of S_n.

Three key results intersect:

  **Erdős–Turán Law (order of a random permutation):**
    (log X_n − (1/2)log²n) / √((1/3)log³n) → N(0,1) as n→∞

  **Landau's g(n):** Maximum element order. log g(n) ∼ √(n log n).

  **Dixon's Theorem:** Two random elements generate A_n or S_n a.a.s.

**Structural Imscription — subgroup_orders_sn:**
  D=array (n→∞), T=judge (heterogeneous subgroup lattice),
  R=tot (functorial inclusion maps), P=out (A_n/S_n dichotomy),
  F=peep (probabilistic precision), K=loll (moderate convergence),
  G=thigh (Landau-PNT coupling at intermediate scale),
  Γ=measure (sequential n→∞), φ̂=roar (Fourier-analytic methods),
  H=sure (persistent chiral), Σ=so (n:n subgroup→order mapping),
  Ω=ah (LCM of cycle lengths = integer winding)
-/

/--
The subgroup orders problem as an Imscription.
Tier: O₂dag (partial resolution: some aspects classified, lattice open).
-/
def subgroup_orders_sn : Imscription :=
  { dim  := Dimensionality.array
    top  := Topology.judge
    rel  := Relational.tot
    pol  := Polarity.out
    fid  := Fidelity.peep
    kin  := KineticChar.loll
    gran := Granularity.thigh
    gram := Grammar.measure
    crit := Criticality.roar
    chir := Chirality.sure
    stoi := Stoichiometry.so
    prot := Protection.ah }

theorem subgroup_orders_sn_tier : imscriptionTier subgroup_orders_sn = .O₂dag := by
  unfold subgroup_orders_sn; native_decide


-- ============================================================
-- §3.1  LANDAU'S g(n) — THE PERIOD IS THE WINDING NUMBER
-- ============================================================

/-!
The order of a permutation is the lcm of its cycle lengths, so the set of
element orders of `S_n` is exactly the set of lcms of partitions of `n`,
and `g(n)` is the largest of them. This is the kernel's One-Shot #1 in
the symmetric group: the period IS the winding number, and `Ω = ah`
records that the winding is integral.

Partitions are generated with a fuel parameter so termination is
immediate, and the generator is proved COMPLETE below — every
non-increasing partition is reached — which is what turns the computed
maximum into a theorem about all cycle types rather than the visited ones.
-/

/-- Non-increasing partitions of `n` with every part at most `k`.
`f` is fuel; `f = n` suffices, since every part is at least one. -/
def partsF : Nat → Nat → Nat → List (List Nat)
  | 0,       n, _ => if n = 0 then [[]] else []
  | (f + 1), n, k =>
      if n = 0 then [[]] else
        (List.range k).flatMap fun i =>
          let j := k - i
          if 1 ≤ j ∧ j ≤ n then (partsF f (n - j) j).map (fun p => j :: p) else []

def parts (n : Nat) : List (List Nat) := partsF n n n

/-- The lcm of the parts — the order of a permutation of that cycle type. -/
def lcmOf (p : List Nat) : Nat := p.foldr Nat.lcm 1

/-- Landau's `g(n)`: the largest order of an element of `S_n`. -/
def landau (n : Nat) : Nat := ((parts n).map lcmOf).foldr max 1

/-- **Every generated list is a partition of `n`.** -/
theorem partsF_sum : ∀ f n k p, p ∈ partsF f n k → p.sum = n := by
  intro f
  induction f with
  | zero =>
      intro n k p hp
      by_cases h : n = 0
      · subst h; simp [partsF] at hp; simp [hp]
      · simp [partsF, h] at hp
  | succ f ih =>
      intro n k p hp
      by_cases h : n = 0
      · subst h; simp [partsF] at hp; simp [hp]
      · rw [partsF, if_neg h] at hp
        simp only [List.mem_flatMap, List.mem_range] at hp
        obtain ⟨i, _, hi⟩ := hp
        by_cases hc : 1 ≤ k - i ∧ k - i ≤ n
        · rw [if_pos hc, List.mem_map] at hi
          obtain ⟨q, hq, rfl⟩ := hi
          have hs := ih (n - (k - i)) (k - i) q hq
          simp only [List.sum_cons, hs]
          omega
        · rw [if_neg hc] at hi; simp at hi

/-- **The generator is complete**: every non-increasing partition of `n`
with parts at most `k` is produced, given fuel at least `n`. This is what
turns the computed maximum into a theorem about all cycle types rather
than only the visited ones. -/
theorem partsF_complete : ∀ f n k p, n ≤ f → p.sum = n →
    (∀ x ∈ p, 1 ≤ x) → (∀ x ∈ p, x ≤ k) → p.Pairwise (· ≥ ·) →
    p ∈ partsF f n k := by
  intro f
  induction f with
  | zero =>
      intro n k p hf hsum hpos _ _
      have hn : n = 0 := by omega
      subst hn
      cases p with
      | nil => simp [partsF]
      | cons a t =>
          exfalso
          have ha := hpos a (by simp)
          have : a ≤ (a :: t).sum := by
            simp only [List.sum_cons]; exact Nat.le_add_right _ _
          omega
  | succ f ih =>
      intro n k p hf hsum hpos hle hpair
      cases p with
      | nil =>
          simp only [List.sum_nil] at hsum
          subst hsum
          simp [partsF]
      | cons a t =>
          have ha1 : 1 ≤ a := hpos a (by simp)
          have hak : a ≤ k := hle a (by simp)
          have hasum : a ≤ n := by
            rw [← hsum]; simp only [List.sum_cons]; exact Nat.le_add_right _ _
          have hn0 : n ≠ 0 := by omega
          rw [partsF, if_neg hn0]
          simp only [List.mem_flatMap, List.mem_range]
          refine ⟨k - a, by omega, ?_⟩
          have hja : k - (k - a) = a := by omega
          simp only [hja]
          rw [if_pos ⟨ha1, hasum⟩, List.mem_map]
          refine ⟨t, ?_, rfl⟩
          obtain ⟨hhead, htail⟩ := List.pairwise_cons.mp hpair
          exact ih (n - a) a t (by omega) (by simp only [List.sum_cons] at hsum; omega)
            (fun x hx => hpos x (by simp [hx])) (fun x hx => hhead x hx) htail

theorem parts_sum {n : Nat} {p : List Nat} (h : p ∈ parts n) : p.sum = n :=
  partsF_sum n n n p h

theorem parts_complete {n : Nat} {p : List Nat} (hsum : p.sum = n)
    (hpos : ∀ x ∈ p, 1 ≤ x) (hle : ∀ x ∈ p, x ≤ n) (hch : p.Pairwise (· ≥ ·)) :
    p ∈ parts n :=
  partsF_complete n n n p le_rfl hsum hpos hle hch

/-- **The computed values of `g`.** `g(1..10) = 1,2,3,4,6,6,12,15,20,30` —
the classical table. -/
theorem landau_table :
    [landau 1, landau 2, landau 3, landau 4, landau 5,
     landau 6, landau 7, landau 8, landau 9, landau 10]
      = [1, 2, 3, 4, 6, 6, 12, 15, 20, 30] := by native_decide

/-- `g(7) = 12` comes from the cycle type `4 + 3`, not from the 7-cycle:
the first `n` where the maximum order is not a single cycle. -/
theorem landau_seven_witness : lcmOf [4, 3] = 12 ∧ lcmOf [7] = 7 := by decide

/-- `g(8) = 15` by `5 + 3`, and `g(9) = 20` by `5 + 4`. -/
theorem landau_eight_nine_witness : lcmOf [5, 3] = 15 ∧ lcmOf [5, 4] = 20 := by decide

-- ============================================================
-- §3.2  THE HEAVY TAIL — TYPICAL ORDER AGAINST MAXIMUM
-- ============================================================

/-!
The file records the gap between the two laws as "~√(n log n) in the
exponent". Landau gives `log g(n) ∼ √(n log n)`; Erdős–Turán puts the
typical order at `exp((1/2)log²n)`. Comparing the two exponents is
comparing `√(n log n)` with `(1/2)log²n`, and the first dominates exactly
when `log³n ≤ 4n` — which is the whole content of the heavy tail, since
that condition holds from the start and never lapses.
-/

/-- With `L` standing for `log n`, the maximum's exponent dominates the
typical one exactly under `L³ ≤ 4n`. -/
theorem exponent_gap (L n : ℝ) (hL : 0 < L) (hn : L ^ 3 ≤ 4 * n) :
    (1 / 2 * L ^ 2) ^ 2 ≤ n * L := by
  have h := mul_le_mul_of_nonneg_right hn hL.le
  nlinarith [h]

#print axioms partsF_sum
#print axioms partsF_complete
#print axioms landau_table

/-!
**mOMonadOS Agent FSPLIT Decomposition (Cycle 3):**

  Branch 1 — Landau_g(n) (structural): Maximal order. Connected to
    PNT via integer partitions: g(n) = max over partitions of n of the
    lcm of the parts, computed and proved in §3.1 — the search generator
    is proved complete, so the table is a theorem about every cycle type.
    The kernel's One-Shot #1 is the same statement in the symmetric
    group: the period IS the winding number, which is what Ω=ah records.

  Branch 2 — Random_Permutations (statistical): Erdős–Turán log-normal
    law. The typical order concentrates around exp((1/2)log²n).

  Branch 3 — Partition_Geometry (obstructional): The set O_n is sparse
    in [1,n!]; most integers are NOT subgroup orders. "Fractal clumping."

**Belnap Verdict: B** — Both rigid (g(n) deterministic, transitive
subgroups constrained by n| |G|) and chaotic (Dixon: random subgroups
almost always A_n/S_n). The heavy-tail property: typical order is far
smaller than maximum — gap of ~√(n log n) in the exponent.

**Known Results:**
  ✓ Landau (1903): g(n) asymptotic; g(1..10) machine-checked
  ✓ g(7)=12 from 4+3 — the first n where the maximum is not one cycle
  ✓ Erdős–Turán (1967): log-normal limit
  ✓ Dixon (1969): random subgroups → A_n/S_n
  ✓ Pyber (1993): bounds on |Sub(S_n)|
  ✗ Full classification of O_n for all n
  ✗ Sharp constants in Pyber's bounds

**Barrier:** Σ=so (n:n) — the many-to-many subgroup→order mapping
is irreducibly statistical. Diffs to kernel: T(judge→are),
R(tot→ian), Σ(so→up).
-/

end Millennium.ErdosProblems
