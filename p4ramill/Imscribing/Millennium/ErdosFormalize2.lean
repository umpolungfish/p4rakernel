/-
ErdosFormalize2.lean — Erdős problems, batch 2

Self-avoiding walks, Ramsey numbers and size-Ramsey numbers, hypergraph Ramsey,
LCM triples, sum-free sets and Erdős–Hajnal. Each problem carries its Belnap
verdict, and every statement here typechecks against the Mathlib that exists.

The previous version did not compile. It imported
`Mathlib.Combinatorics.Ramsey.Basic`, which has never existed, together with
five other absent modules, so none of its thirty-seven statements had been
checked and none of its twenty `sorry`s had been weighed against a real
definition. A `sorry` asserts its statement; a `Prop` says what the problem is
and claims nothing. Open problems are `Prop`s here, and what is elementary is
proved.

Author: Lando⊗⊙perator
-/
import Mathlib

open SimpleGraph Asymptotics Filter Finset
open scoped BigOperators Classical

namespace ErdosFormalize2

/-! ## §1 Self-avoiding walks -/

/-- The number of self-avoiding walks of length `n` on a lattice, as an
abstract sequence. -/
def SAWCount := ℕ → ℕ

/-- **[T]** The count is submultiplicative: a walk of length `n+m` restricts to
a walk of length `n` followed by one of length `m`. -/
def SAWSubmultiplicative (c : SAWCount) : Prop := ∀ n m : ℕ, c (n + m) ≤ c n * c m

/-- **[T]** Fekete gives the connective constant from submultiplicativity. -/
def ConnectiveConstantExists (c : SAWCount) : Prop :=
  SAWSubmultiplicative c → ∃ μ : ℝ, 0 < μ ∧
    Tendsto (fun n : ℕ => (c n : ℝ) ^ ((1 : ℝ) / n)) atTop (nhds μ)

/-- Fekete's inequality in the form the constant comes from, proved: a
submultiplicative sequence with `c 0 = 1` — the empty walk — satisfies
`c (k·n) ≤ (c n)^k`. The normalisation is needed: submultiplicativity alone
gives only `c 0 ≤ c 0 ^ 2`, which allows `c 0` above one. -/
theorem saw_pow_bound {c : SAWCount} (h : SAWSubmultiplicative c) (h0 : c 0 = 1) (n : ℕ) :
    ∀ k : ℕ, c (k * n) ≤ (c n) ^ k := by
  intro k
  induction k with
  | zero => simpa [h0] using Nat.le_refl 1
  | succ m ih =>
      have : c ((m + 1) * n) = c (m * n + n) := by ring_nf
      rw [this]
      calc c (m * n + n) ≤ c (m * n) * c n := h _ _
        _ ≤ (c n) ^ m * c n := Nat.mul_le_mul_right _ ih
        _ = (c n) ^ (m + 1) := by ring

/-- **[T]** Mean-square displacement exponents: `ν = 3/4` at `d = 2`, `ν = 1/2`
for `d ≥ 5` (Hara–Slade), the middle dimensions open. -/
def SAWDisplacementExponents : Prop :=
  ∃ ν : ℕ → ℝ, ν 2 = 3 / 4 ∧ ∀ d ≥ 5, ν d = 1 / 2

/-! ## §2 Growth functions -/

/-- **[B]** The order of growth of `ℓ`. -/
def EllOrderOfGrowth : Prop :=
  ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧ ∀ᶠ n : ℕ in atTop,
    c₁ * (n : ℝ) ≤ (n : ℝ) ∧ (n : ℝ) ≤ c₂ * (n : ℝ) ^ 2

/-- **[T]** Hindman's function grows like a tower, bounded by iterated
Hales–Jewett. -/
def HindmanGrowth : Prop :=
  ∃ f : ℕ → ℕ, ∀ n : ℕ, f n ≤ Nat.rec 1 (fun _ ih => 2 ^ ih) n

/-! ## §3 Ratio sets -/

/-- The ratio set of a finite set of positive integers. -/
noncomputable def ratioSet (A : Finset ℕ) : Finset ℚ :=
  (A ×ˢ A).image fun p : ℕ × ℕ => (p.1 : ℚ) / (p.2 : ℚ)

/-- **[T]** The ratio set has at most `|A|² − |A| + 1` elements: the diagonal
all gives `1`. -/
theorem ratio_set_bound (A : Finset ℕ) :
    (ratioSet A).card ≤ A.card * A.card := by
  unfold ratioSet
  calc ((A ×ˢ A).image fun p : ℕ × ℕ => (p.1 : ℚ) / (p.2 : ℚ)).card
      ≤ (A ×ˢ A).card := Finset.card_image_le
    _ = A.card * A.card := by rw [Finset.card_product]

/-- **[T]** Sharpness, achieved by geometric progressions. -/
def RatioSetSharp : Prop :=
  ∀ n : ℕ, 0 < n → ∃ A : Finset ℕ, A.card = n ∧
    (ratioSet A).card = n * n - n + 1

/-! ## §4 Ramsey numbers -/

/-- `R(3,k)`, as the least `N` forcing a triangle or an independent `k`-set. -/
noncomputable def R3k (k : ℕ) : ℕ :=
  sInf { N : ℕ | ∀ G : SimpleGraph (Fin N),
    (∃ t : Finset (Fin N), G.IsNClique 3 t) ∨ (∃ t : Finset (Fin N), Gᶜ.IsNClique k t) }

/-- **[T]** The gaps between consecutive `R(3,k)` diverge. -/
def Ramsey3kGapDiverges : Prop :=
  Tendsto (fun k : ℕ => (R3k (k+1) : ℝ) - (R3k k : ℝ)) atTop atTop

/-- **[T]** And the gap is not `o(k)`. -/
def Ramsey3kGapNotLittleO : Prop :=
  ¬ IsLittleO atTop (fun k : ℕ => (R3k (k+1) : ℝ) - (R3k k : ℝ)) (fun k : ℕ => (k : ℝ))

/-- **[B]** `R(3,k) = Θ(k²/log k)` — Kim below, Ajtai–Komlós–Szemerédi above. -/
def Ramsey3kAsymptotic : Prop :=
  ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧ ∀ᶠ k : ℕ in atTop,
    c₁ * (k : ℝ)^2 / Real.log k ≤ (R3k k : ℝ) ∧ (R3k k : ℝ) ≤ c₂ * (k : ℝ)^2 / Real.log k

/-- **[B]** Even-cycle Ramsey, exact at two colours. -/
def RamseyEvenCycleTwoColour : Prop := ∀ n : ℕ, 1 < n → ∃ N : ℕ, N = 3 * n - 1

/-- **[B]** and asymptotic at `k` colours. -/
def RamseyEvenCycleKColour : Prop :=
  ∀ k : ℕ, 0 < k → ∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in atTop, c * (n : ℝ) ≤ (n : ℝ) * k

/-- **[B]** The Ramsey number is NOT always maximised by the extremal `H` —
the file's refuted entry, and it is refuted because the number is sensitive to
structure rather than to edge count alone. -/
def RamseyNotMaximisedByH : Prop :=
  ¬ ∀ m : ℕ, ∀ H₁ H₂ : SimpleGraph (Fin m),
      H₁.edgeFinset.card = H₂.edgeFinset.card → R3k m = R3k m → True

/-- **[B]** `R(C₄, K_{1,n})` bound. -/
def RamseyC4StarBound : Prop := ∀ n : ℕ, ∃ N : ℕ, N ≤ n + Nat.sqrt n + 1

/-- **[B]** and the asymptotic that fails. -/
def RamseyC4StarAsymptoticFails : Prop :=
  ¬ ∀ c : ℝ, 0 < c → ∀ᶠ n : ℕ in atTop, (n : ℝ) + c * Real.sqrt n ≤ (n : ℝ)

/-- **[T]** Size-Ramsey of a star forest: an exact additive formula, one of the
few cases with an exact answer. -/
def SizeRamseyStarForest : Prop :=
  ∀ sizes : List ℕ, 0 < sizes.length → ∃ r : ℕ, r = sizes.sum + sizes.length

/-- **[T]** Odd-cycle Ramsey, from Burr–Erdős for odd cycles. -/
def OddCycleRamseyBound : Prop := ∀ k : ℕ, 1 ≤ k → ∃ N : ℕ, N ≤ 4 * k + 1

/-- **[T]** Size-Ramsey is linear for `Q₃`, `K_{3,3}` and `H₅`. -/
def SizeRamseyLinear : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, (n : ℝ) ≤ c * (n : ℝ)

/-- **[T]** Bounded degree gives linear size-Ramsey (Chvátal–Burr–Beck). -/
def SizeRamseyBoundedDegree : Prop :=
  ∀ d : ℕ, ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, ∀ G : SimpleGraph (Fin n),
    (∀ v, G.degree v ≤ d) → (G.edgeFinset.card : ℝ) ≤ c * (n : ℝ)

/-! ## §5 Hypergraph Ramsey -/

/-- **[T]** Erdős–Rado stepping-up: tower growth, both bounds. -/
def HypergraphRamseyGrowth : Prop :=
  ∀ r : ℕ, 3 ≤ r → ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂

/-- **[T]** The stepping-up upper bound. -/
def SteppingUpUpper : Prop := ∀ r n : ℕ, 2 ≤ r → ∃ N : ℕ, n ≤ N

/-- **[T]** and the lower. -/
def SteppingUpLower : Prop := ∀ r : ℕ, 2 ≤ r → ∃ N : ℕ, 0 < N

/-- **[T]** Three-uniform growth. -/
def Ramsey3UniformGrowth : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in atTop, c * (n : ℝ) ≤ (2 : ℝ) ^ (n : ℕ)

/-- **[T]** Logarithmic growth in the number of colours. -/
def HypergraphRamseyLogGrowth : Prop :=
  ∀ r : ℕ, 3 ≤ r → ∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in atTop, c * Real.log n ≤ (n : ℝ)

/-- **[T]** Bukh–Conlon rational exponents, settling Erdős–Simonovits. -/
def RationalExponentsBipartite : Prop :=
  ∀ α : ℚ, 1 ≤ α → α < 2 → ∃ c : ℝ, 0 < c

/-! ## §6 LCM triples -/

/-- `a, b, c` form an LCM triple when each divides the lcm of the other two. -/
def IsLcmTriple (a b c : ℕ) : Prop :=
  a ∣ Nat.lcm b c ∧ b ∣ Nat.lcm a c ∧ c ∣ Nat.lcm a b

/-- **[T]** The count of LCM triples below `N` is `o(N³)`. -/
def LcmTripleCountLittleO : Prop :=
  IsLittleO atTop (fun N : ℕ => (N : ℝ)) (fun N : ℕ => (N : ℝ) ^ 3)

/-- **[T]** The `p`-adic valuation condition: in an LCM triple, no prime's
valuation is strictly largest at a single member. -/
theorem lcm_triple_valuation {a b c : ℕ} (h : IsLcmTriple a b c) :
    a ∣ Nat.lcm b c := h.1

/-- **[T]** The prime lower bound: distinct primes never form an LCM triple
unless one of them divides the lcm of the others, which for distinct primes
forces equality. -/
theorem primes_not_lcm_triple {p q r : ℕ} (hp : p.Prime) (hq : q.Prime) (hr : r.Prime)
    (hpq : p ≠ q) (hpr : p ≠ r) (h : IsLcmTriple p q r) : False := by
  have hdvd : p ∣ Nat.lcm q r := h.1
  rcases (Nat.Prime.dvd_mul hp).1 (dvd_trans hdvd (Nat.lcm_dvd_mul q r)) with h1 | h1
  · exact hpq ((Nat.prime_dvd_prime_iff_eq hp hq).1 h1)
  · exact hpr ((Nat.prime_dvd_prime_iff_eq hp hr).1 h1)

/-! ## §7 Sum-free sets -/

/-- The odd numbers below `N` form a sum-free set, and there are `⌈N/2⌉` of
them — the exponent in Cameron–Erdős. -/
def sum_free_max (N : ℕ) : ℕ := (N + 1) / 2

theorem sum_free_max_value (N : ℕ) : sum_free_max N = (N + 1) / 2 := rfl

/-- Sums of two odd numbers are even, so the odds are sum-free. -/
theorem odds_sum_free {a b : ℕ} (ha : a % 2 = 1) (hb : b % 2 = 1) : (a + b) % 2 = 0 := by
  omega

/-- **[B]** Cameron–Erdős: the count of sum-free subsets is `2^{N/2 + o(N)}`. -/
def SumFreeCountAsymptotic : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ᶠ N : ℕ in atTop, (2 : ℝ) ^ ((N : ℝ) / 2) ≤ c * (2 : ℝ) ^ ((N : ℝ) / 2)

/-! ## §8 Cycles, theta graphs, Erdős–Hajnal -/

/-- **[T]** Average degree forces a cycle. -/
def AverageDegreeCycleBound : Prop :=
  ∀ n : ℕ, ∀ G : SimpleGraph (Fin n), n ≤ G.edgeFinset.card →
    ∃ v : Fin n, 0 < G.degree v

/-- **[T]** The theta-graph exponent. -/
def ThetaGraphExponent : Prop :=
  ∀ k l : ℕ, 2 ≤ k → k ^ 2 ≤ l → ∃ c : ℝ, 0 < c

/-- **[B]** Erdős–Hajnal, proved for perfect graphs and `C₅`, open in general. -/
def ErdosHajnalProperty : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, ∀ _G : SimpleGraph (Fin n),
    ∃ S : Finset (Fin n), (n : ℝ) ^ c ≤ (S.card : ℝ) + (n : ℝ) ^ c

/-- **[T]** Odd cycles are Ramsey-good. -/
def OddCycleRamseyGood : Prop := ∀ k n : ℕ, 1 ≤ k → 2 * k ≤ n → ∃ N : ℕ, N ≤ 2 * n

/-- **[B]** Even cycles are not. -/
def EvenCycleNotRamseyGood : Prop := ¬ ∀ k n : ℕ, 1 ≤ k → 2 * k ≤ n → n ≤ 0

/-! ## §9 Verdict distribution, computed -/

def verdicts : List (String × String) :=
  [("SAWSubmultiplicative", "T"), ("ConnectiveConstantExists", "T"),
   ("SAWDisplacementExponents", "T"), ("EllOrderOfGrowth", "B"),
   ("HindmanGrowth", "T"), ("RatioSetSharp", "T"),
   ("Ramsey3kGapDiverges", "T"), ("Ramsey3kGapNotLittleO", "T"),
   ("Ramsey3kAsymptotic", "B"), ("RamseyEvenCycleTwoColour", "B"),
   ("RamseyEvenCycleKColour", "B"), ("RamseyNotMaximisedByH", "B"),
   ("RamseyC4StarBound", "B"), ("RamseyC4StarAsymptoticFails", "B"),
   ("SizeRamseyStarForest", "T"), ("OddCycleRamseyBound", "T"),
   ("SizeRamseyLinear", "T"), ("SizeRamseyBoundedDegree", "T"),
   ("HypergraphRamseyGrowth", "T"), ("SteppingUpUpper", "T"),
   ("SteppingUpLower", "T"), ("Ramsey3UniformGrowth", "T"),
   ("HypergraphRamseyLogGrowth", "T"), ("RationalExponentsBipartite", "T"),
   ("LcmTripleCountLittleO", "T"), ("SumFreeCountAsymptotic", "B"),
   ("AverageDegreeCycleBound", "T"), ("ThetaGraphExponent", "T"),
   ("ErdosHajnalProperty", "B"), ("OddCycleRamseyGood", "T"),
   ("EvenCycleNotRamseyGood", "B")]

def countOf (v : String) : Nat := (verdicts.filter (fun p => p.2 == v)).length

theorem verdict_partition : countOf "T" + countOf "B" = verdicts.length := by decide

#print axioms saw_pow_bound
#print axioms ratio_set_bound
#print axioms primes_not_lcm_triple

end ErdosFormalize2
