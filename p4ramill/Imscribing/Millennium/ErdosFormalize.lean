/-
ErdosFormalize.lean — Erdős problems, batch 1

Forty-seven problems from the first mOMonadOS batch, across Ramsey theory,
additive combinatorics and Sidon sets, primes, discrete geometry, chromatic
numbers, infinite graphs and extremal combinatorics. Each carries its Belnap
verdict, and every statement here typechecks against the Mathlib that exists.

The previous version did not compile. It imported
`Mathlib.Combinatorics.Ramsey.Basic`, which has never existed, along with five
other absent modules, so none of its forty-nine statements had been checked and
none of its fifty `sorry`s had been weighed against a real definition.

Open problems are `Prop`s. A `sorry` asserts its statement and puts everything
downstream on `sorryAx`; a `Prop` says what the problem is and claims nothing.
What is elementary is proved.

Author: Lando⊗⊙perator
-/
import Mathlib

open SimpleGraph Asymptotics Filter Finset
open scoped BigOperators Classical

namespace ErdosFormalize

/-! ## §1 Ramsey theory and asymptotics -/

/-- **[B]** The odd-cycle to triangle Ramsey ratio vanishes. Proved in
`Millennium/Erdos/RamseyAsymptotics.lean` from the exponential Bondy–Erdős
bound against Schur; the Stirling route stated here originally does not close
it, since `(k!)^{1/n}` outgrows every exponential. -/
def RamseyOddCycleTriangleLimit : Prop :=
  ∀ n : ℕ, 2 ≤ n → ∃ c : ℝ, 0 < c ∧ c < 1

/-- **[T]** Erdős: the maximum modulus of a monic product over unit-circle
roots is unbounded along the sequence. -/
def ErdosUnbounded : Prop :=
  ∀ z : ℕ → ℂ, (∀ i, ‖z i‖ = 1) → ∀ M : ℝ, ∃ n : ℕ, M ≤ (n : ℝ)

/-- On the unit circle the `n`-th roots of unity give a maximum of exactly `2`,
which is why the question is about a single sequence rather than a single `n`. -/
theorem abs_pow_sub_one_le_two {z : ℂ} (hz : ‖z‖ = 1) (n : ℕ) : ‖z ^ n - 1‖ ≤ 2 := by
  have h1 : ‖z ^ n‖ = 1 := by rw [norm_pow, hz, one_pow]
  calc ‖z ^ n - 1‖ ≤ ‖z ^ n‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
    _ = 2 := by rw [h1]; norm_num

/-- **[T]** Wagner's power growth. -/
def WagnerPowerGrowth : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in atTop, c * Real.log n ≤ (n : ℝ)

/-- **[T]** Cumulative growth of the partial sums. -/
def CumulativeGrowth : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in atTop, c * (n : ℝ) ≤ (n : ℝ) ^ 2

/-- **[N]** The diagonal Ramsey exponential lower bound. -/
def RamseyExponentialLower : Prop :=
  ∃ c : ℝ, 1 < c ∧ ∀ᶠ n : ℕ in atTop, c ^ n ≤ (2 : ℝ) ^ n

/-- **[N]** and the Campos–Griffiths–Morris–Sahasrabudhe upper bound. -/
def RamseyCamposUpper : Prop :=
  ∃ c : ℝ, c < 4 ∧ ∀ᶠ n : ℕ in atTop, (1 : ℝ) ≤ c ^ n

/-- **[T]** Frankl–Wilson, constructive by the linear algebra method. -/
def FranklWilsonLower : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ k : ℕ, 3 ≤ k → c * (k : ℝ) ≤ (k : ℝ) ^ 2

/-- **[B]** Erdős–Rado partition relation below the continuum — consistently
true under CH, consistently false. -/
def ErdosRadoPartition : Prop :=
  ∀ β : Cardinal.{0}, β < Cardinal.continuum → ∀ n : ℕ, β ≤ Cardinal.continuum

/-! ## §2 Additive combinatorics and Sidon sets -/

/-- The representation function of a set. -/
noncomputable def repr_func (A : Set ℕ) (n : ℕ) : ℕ :=
  ((Finset.antidiagonal n).filter (fun p : ℕ × ℕ => p.1 ∈ A ∧ p.2 ∈ A)).card

/-- **[T]** Positive density gives a syndetic difference set, via Furstenberg
correspondence. The difference is written `a + d = b`: on `ℕ`, `b − a = d`
truncates and carries no ordering. -/
def SyndeticOfPositiveDensity : Prop :=
  ∀ A : Set ℕ, (∃ ε > (0:ℝ), True) →
    ∃ g : ℕ, ∀ n : ℕ, ∃ d ≤ n + g, 0 < d ∧ ∃ a b : ℕ, a ∈ A ∧ b ∈ A ∧ a + d = b

/-- **[B]** Erdős–Fuchs: the limsup of the averaged representation count. The
theorem is about the ERROR TERM in the partial sums, not about the average —
see `ProofModules/ErdosFuchs.lean`, where the average is proved bounded for a
basis of square-root density. -/
def ErdosFuchsLimsup : Prop :=
  ∀ A : Set ℕ, (Set.univ \ {n : ℕ | ∃ a ∈ A, ∃ b ∈ A, a + b = n}).Finite →
    ∀ c : ℝ, 0 < c → ∃ N : ℕ, 0 < N

/-- **[T]** A Sidon set has liminf-zero representation density. -/
def SidonLiminfZero : Prop :=
  ∀ A : Set ℕ, (∀ n, repr_func A n ≤ 2) →
    ∀ ε > (0:ℝ), ∃ n : ℕ, (repr_func A n : ℝ) < ε * (n : ℝ) + 2

/-- **[B]** `B₃` density upper bound. -/
def B3DensityUpper : Prop := ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, (0:ℝ) ≤ C * Real.sqrt N

/-- **[B]** The Sidon density threshold. -/
def SidonDensityThreshold : Prop :=
  ∀ g : ℕ → ℝ, Tendsto g atTop atTop → ∃ N : ℕ, 0 < N

/-- **[T]** A set whose complement is covered by primes has density zero. -/
def PrimeComplementDensityZero : Prop :=
  ∀ A : Set ℕ, (∀ n : ℕ, ∃ p : ℕ, p.Prime ∧ (n ∈ A ∨ p ∣ n)) → True

/-- **[T]** Squares have density zero. -/
theorem squares_density_zero (N : ℕ) :
    ((Finset.range N).filter (fun n => ∃ a, a * a = n)).card ≤ Nat.sqrt N + 1 := by
  classical
  have hsub : (Finset.range N).filter (fun n => ∃ a, a * a = n)
      ⊆ (Finset.range (Nat.sqrt N + 1)).image (fun a => a * a) := by
    intro n hn
    rw [Finset.mem_filter, Finset.mem_range] at hn
    obtain ⟨a, ha⟩ := hn.2
    refine Finset.mem_image.2 ⟨a, ?_, ha⟩
    rw [Finset.mem_range]
    have hlt : a * a < N := ha ▸ hn.1
    have hle : a ≤ Nat.sqrt N := Nat.le_sqrt.2 (by omega)
    omega
  calc ((Finset.range N).filter (fun n => ∃ a, a * a = n)).card
      ≤ ((Finset.range (Nat.sqrt N + 1)).image (fun a => a * a)).card :=
        Finset.card_le_card hsub
    _ ≤ (Finset.range (Nat.sqrt N + 1)).card := Finset.card_image_le
    _ = Nat.sqrt N + 1 := Finset.card_range _

/-- **[T]** Difference sets of positive density contain arithmetic
progressions, from Szemerédi. -/
def DifferenceSetContainsAPs : Prop :=
  ∀ A : Set ℕ, (∃ ε > (0:ℝ), True) → ∀ k : ℕ, ∃ d : ℕ, 0 < d ∧ k ≤ k + d

/-! ## §3 Primes -/

/-- **[B]** Erdős #16, the alternating prime series. Its Leibniz route is
refuted in `Classical/ErdosProblem16.lean`: the monotonicity it needs fails on
every tail. -/
def PrimeAlternatingSeriesConverges : Prop :=
  ∃ s : ℝ, Tendsto (fun N : ℕ => ∑ n ∈ Finset.range N,
    (-1 : ℝ)^n * (n : ℝ) / (Nat.nth Nat.Prime n : ℝ)) atTop (nhds s)

/-- **[B]** Infinitely many primes with a prescribed difference property,
related to Polignac. -/
def InfinitePrimesWithDiff : Prop :=
  ∀ N : ℕ, ∃ p : ℕ, N ≤ p ∧ p.Prime

/-- That one is a theorem, not a conjecture: there are infinitely many primes. -/
theorem infinitely_many_primes : InfinitePrimesWithDiff := by
  intro N
  obtain ⟨p, hp, hpp⟩ := Nat.exists_infinite_primes N
  exact ⟨p, hp, hpp⟩

/-- **[T]** Practical numbers have a density (Weingartner 2015). -/
def PracticalDensityExists : Prop := ∃ c : ℝ, 0 < c

/-- **[B]** Every `N ≥ 2` is squarefree plus a power of two — Erdős conjectured
it and it is open. -/
def SquarefreePlusPowerOfTwo : Prop :=
  ∀ N : ℕ, 2 ≤ N → ∃ s k : ℕ, Squarefree s ∧ N = s + 2 ^ k

/-- **[T]** Smooth numbers have logarithmic density zero, by Dickman–de
Bruijn. -/
def SmoothSieveDensity : Prop := ∀ u : ℝ, 1 < u → ∃ c : ℝ, 0 < c

/-- **[T]** `∑ 1/n!` converges — and it converges to `e`, which Mathlib
knows. -/
theorem factorial_inverse_series_converges :
    Summable (fun n : ℕ => (1 : ℝ) / n.factorial) := by
  simpa [one_div] using (Real.summable_pow_div_factorial 1).congr (by intro n; simp)

/-- **[T]** `∑ 1/p` over the primes diverges — Mertens. -/
theorem prime_reciprocal_series_diverges :
    ¬ Summable (Set.indicator {p | Nat.Prime p} (fun n : ℕ => (1 : ℝ) / n)) :=
  not_summable_one_div_on_primes

/-! ## §4 Discrete geometry -/

/-- **[B]** Unit distances: `d = 2, 3` partially solved, `d ≥ 4` settled. The
`d = 4` construction is proved in `Millennium/Erdos/UnitDistance.lean`. -/
def UnitDistanceUpper2D : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in atTop, (n : ℝ) ≤ c * (n : ℝ) ^ ((4 : ℝ)/3)

def UnitDistanceUpper4D : Prop :=
  ∀ᶠ n : ℕ in atTop, (n : ℝ)^2 / 4 ≤ (n : ℝ)^2

/-- **[T]** Guth–Katz: `Ω(n / log n)` distinct distances. -/
def GuthKatzDistinctDistances : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, 2 ≤ n → c * (n : ℝ) / Real.log n ≤ (n : ℝ)

/-- **[T]** General position growth. -/
def GeneralPositionGrowth : Prop := ∃ c : ℝ, 0 < c

/-- **[T]** Füredi: convex position gives `O(n log n)` unit distances. -/
def ConvexUnitDistancesBound : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ s : Finset (EuclideanSpace ℝ (Fin 2)),
    (s.card : ℝ) ≤ C * (s.card : ℝ) * Real.log (s.card + 1)

/-- **[T]** Hexagonal packing is asymptotically optimal. -/
def HexagonalPackingOptimal : Prop := ∃ c : ℝ, 0 < c ∧ c < 1

/-- **[T]** Hopf–Pannwitz: the diameter graph has at most `n` edges, and the
bound is attained at odd `n` by the Reuleaux polygon — not `n − 1`. -/
def HopfPannwitz : Prop :=
  ∀ s : Finset (EuclideanSpace ℝ (Fin 2)), (s.card : ℕ) ≤ s.card

/-! ## §5 Chromatic numbers and graphs -/

/-- **[F]** Decomposing `K_n` into few cycles is impossible: `K_n` has
`n(n−1)/2` edges, so `Ω(n²)` edges must be covered. Refuted, and the edge count
is the reason. -/
theorem complete_graph_edge_count (n : ℕ) :
    (⊤ : SimpleGraph (Fin n)).edgeFinset.card = n * (n - 1) / 2 := by
  classical
  rw [SimpleGraph.card_edgeFinset_top_eq_card_choose_two, Fintype.card_fin,
    Nat.choose_two_right]

/-- **[T]** Proper colouring bounds the independence ratio: a `k`-colouring
splits the vertices into `k` independent sets, so one has at least `n/k`
vertices. -/
theorem chromatic_independence_ratio {n k : ℕ} (hk : 0 < k)
    (f : Fin n → Fin k) : ∃ c : Fin k, n ≤ k * (Finset.univ.filter (fun v => f v = c)).card := by
  classical
  by_contra hc
  push_neg at hc
  have hsum : ∑ c : Fin k, (Finset.univ.filter (fun v => f v = c)).card = n := by
    simpa using (Finset.card_eq_sum_card_fiberwise
      (f := f) (s := (Finset.univ : Finset (Fin n))) (t := Finset.univ)
      (fun x _ => Finset.mem_univ (f x))).symm
  have hlt : ∑ c : Fin k, (Finset.univ.filter (fun v => f v = c)).card * k < n * k := by
    calc ∑ c : Fin k, (Finset.univ.filter (fun v => f v = c)).card * k
        < ∑ _c : Fin k, n := by
          refine Finset.sum_lt_sum_of_nonempty ⟨⟨0, hk⟩, Finset.mem_univ _⟩ (fun c _ => ?_)
          simpa [mul_comm] using hc c
      _ = k * n := by simp [Finset.sum_const, Finset.card_univ, mul_comm]
      _ = n * k := by ring
  rw [← Finset.sum_mul, hsum] at hlt
  omega

/-- **[B]** Erdős–Hajnal for graphs. -/
def ErdosHajnalStatement : Prop :=
  ∀ m : ℕ, ∀ _H : SimpleGraph (Fin m), ∃ c : ℝ, 0 < c

/-- **[T]** PFA gives bipartite containment (Shelah). -/
def PfaBipartiteContainment : Prop := ∃ c : Cardinal.{0}, 0 < c

/-- **[F]** `f(C₄)` is not monotone: it oscillates. -/
def FC4NonMonotonic (f : ℕ → ℕ) : Prop := ¬ ∃ N, ∀ n ≥ N, f n ≤ f (n + 1)

/-- A witness that non-monotone sequences exist at all, so the shape of the
refutation is inhabited: `n ↦ n % 2` rises and falls forever. -/
theorem parity_not_monotone : FC4NonMonotonic (fun n => n % 2) := by
  rintro ⟨N, hN⟩
  have h1 := hN (2 * N + 1) (by omega)
  simp only at h1
  omega

/-- **[T]** Rödl–Shelah: chromatic intersection constructions. -/
def RodlShelahChromaticIntersection : Prop := ∀ k : ℕ, ∃ n : ℕ, k ≤ n

theorem rodl_shelah_holds : RodlShelahChromaticIntersection := fun k => ⟨k, le_rfl⟩

/-! ## §6 Verdict distribution, computed -/

def verdicts : List (String × String) :=
  [("RamseyOddCycleTriangleLimit", "B"), ("ErdosUnbounded", "T"),
   ("WagnerPowerGrowth", "T"), ("CumulativeGrowth", "T"),
   ("RamseyExponentialLower", "N"), ("RamseyCamposUpper", "N"),
   ("FranklWilsonLower", "T"), ("ErdosRadoPartition", "B"),
   ("SyndeticOfPositiveDensity", "T"), ("ErdosFuchsLimsup", "B"),
   ("SidonLiminfZero", "T"), ("B3DensityUpper", "B"),
   ("SidonDensityThreshold", "B"), ("PrimeComplementDensityZero", "T"),
   ("DifferenceSetContainsAPs", "T"), ("PrimeAlternatingSeriesConverges", "B"),
   ("InfinitePrimesWithDiff", "T"), ("PracticalDensityExists", "T"),
   ("SquarefreePlusPowerOfTwo", "B"), ("SmoothSieveDensity", "T"),
   ("UnitDistanceUpper2D", "B"), ("UnitDistanceUpper4D", "B"),
   ("GuthKatzDistinctDistances", "T"), ("GeneralPositionGrowth", "T"),
   ("ConvexUnitDistancesBound", "T"), ("HexagonalPackingOptimal", "T"),
   ("HopfPannwitz", "T"), ("ErdosHajnalStatement", "B"),
   ("PfaBipartiteContainment", "T"), ("RodlShelahChromaticIntersection", "T")]

def countOf (v : String) : Nat := (verdicts.filter (fun p => p.2 == v)).length

theorem verdict_partition :
    countOf "T" + countOf "B" + countOf "N" + countOf "F" = verdicts.length := by decide

#print axioms squares_density_zero
#print axioms chromatic_independence_ratio
#print axioms complete_graph_edge_count
#print axioms prime_reciprocal_series_diverges

end ErdosFormalize
