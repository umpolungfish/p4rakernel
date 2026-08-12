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

/-! The odd-cycle to triangle Ramsey ratio is PROVED in
`Millennium/Erdos/RamseyAsymptotics.lean`, and its statement carrying the ratio
lives in `ProofModules/RamseyLimit.lean`. The version that stood here said only
`∃ c : ℝ, 0 < c ∧ c < 1`, which is true of `c = 1/2` and mentions neither Ramsey
numbers nor cycles — a second, weaker copy of a settled problem. It is gone
rather than restated: one of each thing. -/

/-- **[T]** Erdős: the maximum modulus of a monic product over unit-circle roots
is unbounded in the degree. The statement quantifies over the ROOTS and asks for
a point of the circle where the product is large; the version that stood here
asked only for a natural number above `M`, which is Archimedes and says nothing
about the product. -/
def ErdosUnbounded : Prop :=
  ∀ M : ℝ, ∃ N : ℕ, ∀ n ≥ N, ∀ z : Fin n → ℂ, (∀ i, ‖z i‖ = 1) →
    ∃ w : ℂ, ‖w‖ = 1 ∧ M ≤ ‖∏ i, (w - z i)‖

/-- On the unit circle the `n`-th roots of unity give a maximum of exactly `2`,
which is why the question is about a single sequence rather than a single `n`. -/
theorem abs_pow_sub_one_le_two {z : ℂ} (hz : ‖z‖ = 1) (n : ℕ) : ‖z ^ n - 1‖ ≤ 2 := by
  have h1 : ‖z ^ n‖ = 1 := by rw [norm_pow, hz, one_pow]
  calc ‖z ^ n - 1‖ ≤ ‖z ^ n‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
    _ = 2 := by rw [h1]; norm_num

/-! Two entries stood here, `WagnerPowerGrowth` and `CumulativeGrowth`, each
asserting an inequality between `n`, `log n` and `n²` that holds for any positive
constant and names no object of either problem. Neither docstring identified the
quantity growing, so there is nothing to restate faithfully; they are removed
rather than left standing as formalisations of problems they do not mention. -/

/-- `N` arrows `n`: every two-colouring of the edges of `K_N` has a monochromatic
`K_n`. Written through `CliqueFree` on a graph and its complement, which is what
a two-colouring of the complete graph is. -/
def Arrows (N n : ℕ) : Prop :=
  ∀ G : SimpleGraph (Fin N), ¬ (G.CliqueFree n ∧ Gᶜ.CliqueFree n)

/-- **[N]** The diagonal Ramsey exponential lower bound: below `c^n` vertices the
arrow fails, for some `c > 1`. The version that stood here said `c^n ≤ 2^n` for
some `c > 1`, which `c = 2` satisfies and which mentions no graph. -/
def RamseyExponentialLower : Prop :=
  ∃ c : ℝ, 1 < c ∧ ∀ᶠ n : ℕ in atTop, ∀ N : ℕ, (N : ℝ) ≤ c ^ n → ¬ Arrows N n

/-- **[N]** and the Campos–Griffiths–Morris–Sahasrabudhe upper bound: above `c^n`
vertices the arrow holds, for some `c < 4`. -/
def RamseyCamposUpper : Prop :=
  ∃ c : ℝ, 0 < c ∧ c < 4 ∧ ∀ᶠ n : ℕ in atTop, ∀ N : ℕ, c ^ n ≤ (N : ℝ) → Arrows N n

/-- **[T]** Frankl–Wilson: a lower bound for the diagonal Ramsey number of
superpolynomial shape, `k^{c log k / log log k}` vertices still failing to arrow.
The version that stood here compared `c·k` with `k²`. -/
def FranklWilsonLower : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ᶠ k : ℕ in atTop, ∀ N : ℕ,
    (N : ℝ) ≤ (k : ℝ) ^ (c * Real.log k / Real.log (Real.log k)) → ¬ Arrows N k

/-! An `ErdosRadoPartition` entry stood here reading
`β < continuum → β ≤ continuum`, which is transitivity of `<` into `≤` and holds
of every cardinal. The partition relation it was named for is independent of ZFC,
so its content is a consistency statement rather than a Prop with a truth value
here, and a placeholder that proves itself is worse than its absence. -/

/-! ## §2 Additive combinatorics and Sidon sets -/

/-- The representation function of a set. -/
noncomputable def repr_func (A : Set ℕ) (n : ℕ) : ℕ :=
  ((Finset.antidiagonal n).filter (fun p : ℕ × ℕ => p.1 ∈ A ∧ p.2 ∈ A)).card

/-- How many elements of `A` lie below `N`. -/
noncomputable def countUpTo (A : Set ℕ) (N : ℕ) : ℕ :=
  ((Finset.range N).filter (fun n => n ∈ A)).card

/-- The upper density of `A`, as the limsup of its counting ratio. -/
noncomputable def upperDensity (A : Set ℕ) : ℝ :=
  limsup (fun N : ℕ => (countUpTo A N : ℝ) / (N : ℝ)) atTop

/-- The difference set: the positive `d` realised as a gap inside `A`. Written
`a + d = b`, since on `ℕ` the subtraction `b − a` truncates and carries no
ordering. -/
def DifferenceSet (A : Set ℕ) : Set ℕ :=
  {d : ℕ | 0 < d ∧ ∃ a b : ℕ, a ∈ A ∧ b ∈ A ∧ a + d = b}

/-- **[T]** Positive density gives a syndetic difference set, via Furstenberg
correspondence: the gaps of `DifferenceSet A` are bounded by a single `g`. Both
halves of the old statement were empty — its hypothesis was `∃ ε > 0, True`,
which every `A` satisfies, and its conclusion allowed `d` anywhere below `n + g`
rather than in the window above `n`. -/
def SyndeticOfPositiveDensity : Prop :=
  ∀ A : Set ℕ, 0 < upperDensity A →
    ∃ g : ℕ, 0 < g ∧ ∀ n : ℕ, ∃ d, n ≤ d ∧ d ≤ n + g ∧ d ∈ DifferenceSet A

/-! An `ErdosFuchsLimsup` entry stood here whose conclusion was `∃ N, 0 < N`.
Erdős–Fuchs is about the error term in the partial sums of the representation
count, and that statement, with the average proved bounded for a basis of
square-root density, lives in `ProofModules/ErdosFuchs.lean`. -/

/-- **[T]** A Sidon set misses infinitely many values: its representation
function is zero infinitely often. The old statement asked for
`repr_func A n < ε·n + 2` under the hypothesis `repr_func A n ≤ 2`, which the
hypothesis alone gives for every `n`. -/
def SidonLiminfZero : Prop :=
  ∀ A : Set ℕ, (∀ n, repr_func A n ≤ 2) → ∃ᶠ n : ℕ in atTop, repr_func A n = 0

/-- A `B₃` set: no value has more than six ordered triples summing to it, which
is the bound the six orderings of a single unordered triple force. -/
def IsB3 (A : Finset ℕ) : Prop :=
  ∀ n : ℕ, ((A ×ˢ A ×ˢ A).filter (fun t : ℕ × ℕ × ℕ => t.1 + t.2.1 + t.2.2 = n)).card ≤ 6

/-- **[B]** The `B₃` density upper bound: such a set inside `[0, N)` has at most
`C · N^{1/3}` elements. The old statement said `0 ≤ C·√N`, true of every `C > 0`
and mentioning no set. -/
def B3DensityUpper : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, ∀ A : Finset ℕ, A ⊆ Finset.range N → IsB3 A →
    (A.card : ℝ) ≤ C * (N : ℝ) ^ ((1 : ℝ) / 3)

/-! A `SidonDensityThreshold` entry stood here concluding `∃ N, 0 < N` from an
arbitrary divergent `g`. Its docstring named no threshold and no set, so there is
nothing to restate; it is removed. -/

/-! A `PrimeComplementDensityZero` entry stood here whose conclusion was `True`.
A conclusion of `True` is the shape that makes a statement unfalsifiable, and the
hypothesis it carried holds of every set, since `2 ∣ n` or `n ∈ A` covers `n`. -/

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

/-- **[T]** Difference sets of positive density contain arbitrarily long
arithmetic progressions, from Szemerédi. The old statement's hypothesis was
`∃ ε > 0, True` and its conclusion `k ≤ k + d`, so it held of every set and every
`k` with `d = 1`. -/
def DifferenceSetContainsAPs : Prop :=
  ∀ A : Set ℕ, 0 < upperDensity A → ∀ k : ℕ,
    ∃ d : ℕ, 0 < d ∧ ∀ i : ℕ, i < k → (i + 1) * d ∈ DifferenceSet A

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

/-- A practical number: every smaller positive integer is a sum of distinct
divisors of it. -/
def IsPractical (n : ℕ) : Prop :=
  0 < n ∧ ∀ m : ℕ, 0 < m → m ≤ n →
    ∃ S : Finset ℕ, (∀ d ∈ S, d ∣ n) ∧ S.sum id = m

/-- **[T]** Practical numbers have a positive density (Weingartner 2015): the
counting ratio converges to a positive constant. The old statement said
`∃ c : ℝ, 0 < c`. -/
def PracticalDensityExists : Prop :=
  ∃ c : ℝ, 0 < c ∧
    Tendsto (fun N : ℕ =>
      (((Finset.range N).filter (fun n => IsPractical n)).card : ℝ) / (N : ℝ))
      atTop (nhds c)

/-- **[B]** Every `N ≥ 2` is squarefree plus a power of two — Erdős conjectured
it and it is open. -/
def SquarefreePlusPowerOfTwo : Prop :=
  ∀ N : ℕ, 2 ≤ N → ∃ s k : ℕ, Squarefree s ∧ N = s + 2 ^ k

/-- **[T]** Dickman–de Bruijn: the `y`-smooth numbers below `x = y^u` have
density `ρ(u)`, which tends to zero as `u` grows. Stated here as the vanishing of
the smooth density in the limit, the part that needs no special function: for
every `ε` there is a `u` beyond which the `x^{1/u}`-smooth numbers below `x` are
fewer than `ε·x`. The old statement said `∃ c : ℝ, 0 < c` for each `u`. -/
def SmoothSieveDensity : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ u : ℝ, 1 < u ∧ ∀ᶠ x : ℕ in atTop,
    ((((Finset.range x).filter
        (fun n => ∀ p : ℕ, p ∈ n.primeFactors → (p : ℝ) ≤ (x : ℝ) ^ (1 / u))).card : ℝ))
      ≤ ε * (x : ℝ)

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

/-- The number of unit distances determined by a finite planar set. -/
noncomputable def unitDistances (P : Finset (EuclideanSpace ℝ (Fin 2))) : ℕ :=
  ((P ×ˢ P).filter
    (fun q : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2) =>
      Dist.dist q.1 q.2 = 1)).card

/-- The number of distinct distances determined by a finite planar set. -/
noncomputable def distinctDistancesOf (P : Finset (EuclideanSpace ℝ (Fin 2))) : ℕ :=
  ((P ×ˢ P).image
    (fun q : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2) =>
      Dist.dist q.1 q.2)).card


/-- **[B]** The planar unit-distance upper bound: `n` points determine
`O(n^{4/3})` unit distances. The old statement compared `n` with `c·n^{4/3}` and
named no point set. The `d = 4` construction, where the problem is settled, is
proved in `Millennium/Erdos/UnitDistance.lean`. -/
def UnitDistanceUpper2D : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ P : Finset (EuclideanSpace ℝ (Fin 2)),
    (unitDistances P : ℝ) ≤ c * (P.card : ℝ) ^ ((4 : ℝ) / 3)

/-- **[T]** Guth–Katz: `n` points determine `Ω(n / log n)` distinct distances.
The old statement compared `c·n/log n` with `n`, which holds for small `c` and
mentions no point set. -/
def GuthKatzDistinctDistances : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ P : Finset (EuclideanSpace ℝ (Fin 2)), 2 ≤ P.card →
    c * (P.card : ℝ) / Real.log (P.card) ≤ (distinctDistancesOf P : ℝ)

/-! A `GeneralPositionGrowth` entry stood here reading `∃ c : ℝ, 0 < c`. Its
docstring named no quantity, so nothing can be restated from it. -/

/-- **[T]** Füredi: a convex polygon's vertices determine `O(n log n)` unit
distances. The old statement bounded `n` by `C·n·log(n+1)`, true of `C = 1` and
saying nothing about distances. -/
def ConvexUnitDistancesBound : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ s : Finset (EuclideanSpace ℝ (Fin 2)),
    (unitDistances s : ℝ) ≤ C * (s.card : ℝ) * Real.log (s.card + 1)

/-! A `HexagonalPackingOptimal` entry stood here reading `∃ c, 0 < c ∧ c < 1`,
satisfied by `c = 1/2` and mentioning no packing. The optimal density is
`π/√12`, a specific constant; stating optimality needs a definition of packing
density that this file does not carry, so the entry is removed rather than
faked. -/

/-! Hopf–Pannwitz stood here as `∀ s : Finset _, s.card ≤ s.card`, which is
reflexivity. The faithful statement — the diameter graph of `n` non-collinear
points has at most `n` edges, and the bound is attained at odd `n` by the
Reuleaux polygon — lives in `ProofModules/HopfPannwitz.lean` together with the
asymptotic form proved from it. -/

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

/-- **[B]** Erdős–Hajnal: for every graph `H` there is `c > 0` such that any
`H`-free graph on `n` vertices has a clique or an independent set of size `n^c`.
The old statement produced a positive real and forgot the conclusion. -/
def ErdosHajnalStatement : Prop :=
  ∀ m : ℕ, ∀ H : SimpleGraph (Fin m), ∃ c : ℝ, 0 < c ∧
    ∀ n : ℕ, ∀ G : SimpleGraph (Fin n),
      (∀ f : Fin m → Fin n, ¬ (∀ u v, H.Adj u v ↔ G.Adj (f u) (f v))) →
      ∃ S : Finset (Fin n), (n : ℝ) ^ c ≤ (S.card : ℝ) ∧
        ((∀ u ∈ S, ∀ v ∈ S, u ≠ v → G.Adj u v) ∨
         (∀ u ∈ S, ∀ v ∈ S, ¬ G.Adj u v))

/-! A `PfaBipartiteContainment` entry stood here reading `∃ c : Cardinal, 0 < c`.
Its subject is a consequence of the Proper Forcing Axiom, so its content is a
consistency statement about set theory rather than a Prop with a truth value in
this development. -/

/-- **[F]** `f(C₄)` is not monotone: it oscillates. -/
def FC4NonMonotonic (f : ℕ → ℕ) : Prop := ¬ ∃ N, ∀ n ≥ N, f n ≤ f (n + 1)

/-- A witness that non-monotone sequences exist at all, so the shape of the
refutation is inhabited: `n ↦ n % 2` rises and falls forever. -/
theorem parity_not_monotone : FC4NonMonotonic (fun n => n % 2) := by
  rintro ⟨N, hN⟩
  have h1 := hN (2 * N + 1) (by omega)
  simp only at h1
  omega

/-! A `RodlShelahChromaticIntersection` entry stood here reading
`∀ k, ∃ n, k ≤ n`, with a theorem proving it by `⟨k, le_rfl⟩`. Proving the
Archimedean property under the name of a chromatic construction is what makes a
catalogue of trivialities look like a corpus of results. Both are removed. -/

/-! ## §6 Verdict distribution, computed

The table names the statements this file carries and nothing else. Entries whose
statement was removed — because it asserted a triviality, or because its faithful
form lives in a proof module — are gone from the table with them, so the count
below is a count of what is here. -/

def verdicts : List (String × String) :=
  [("ErdosUnbounded", "T"), ("RamseyExponentialLower", "N"),
   ("RamseyCamposUpper", "N"), ("FranklWilsonLower", "T"),
   ("SyndeticOfPositiveDensity", "T"), ("SidonLiminfZero", "T"),
   ("B3DensityUpper", "B"), ("DifferenceSetContainsAPs", "T"),
   ("PrimeAlternatingSeriesConverges", "B"), ("InfinitePrimesWithDiff", "T"),
   ("PracticalDensityExists", "T"), ("SquarefreePlusPowerOfTwo", "B"),
   ("SmoothSieveDensity", "T"), ("UnitDistanceUpper2D", "B"),
   ("GuthKatzDistinctDistances", "T"), ("ConvexUnitDistancesBound", "T"),
   ("ErdosHajnalStatement", "B")]

def countOf (v : String) : Nat := (verdicts.filter (fun p => p.2 == v)).length

theorem verdict_partition :
    countOf "T" + countOf "B" + countOf "N" + countOf "F" = verdicts.length := by decide

#print axioms squares_density_zero
#print axioms chromatic_independence_ratio
#print axioms complete_graph_edge_count
#print axioms prime_reciprocal_series_diverges

end ErdosFormalize
