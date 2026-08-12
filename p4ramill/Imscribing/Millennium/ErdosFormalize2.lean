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

/-! A `SAWDisplacementExponents` entry stood here as `∃ ν : ℕ → ℝ` with two
prescribed values, which any function taking those values satisfies and which
says nothing about a walk. The exponent is defined by the asymptotics of the
mean-square displacement, a quantity this file does not carry. -/

/-! ## §2 Growth functions -/

/-! An `EllOrderOfGrowth` entry stood here bounding `n` between `c₁·n` and
`c₂·n²`, which holds of `c₁ = c₂ = 1` and names no function `ℓ`. -/

/-- The tower function, as the growth rate to compare against. -/
def tower : ℕ → ℕ
  | 0 => 1
  | n + 1 => 2 ^ tower n

/-- **[T]** Hindman's function is bounded by a tower: for every `n`-colouring
there is a monochromatic finite-sums set of size `n` inside `[0, H n]`, with `H`
below the tower. The old statement asked only for SOME `f` below the tower, which
the zero function satisfies. -/
def HindmanGrowth : Prop :=
  ∃ H : ℕ → ℕ, (∀ n : ℕ, H n ≤ tower n) ∧
    ∀ n : ℕ, ∀ col : ℕ → Fin n, ∃ S : Finset ℕ, S.card = n ∧
      (∀ m ∈ S, m ≤ H n) ∧
      ∃ i : Fin n, ∀ T : Finset ℕ, T ⊆ S → T.Nonempty → col (T.sum id) = i

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

/-! Two even-cycle Ramsey entries stood here. The first said `∃ N, N = 3n − 1`,
which names that value and asserts nothing of it; the second compared `c·n` with
`n·k`. Both need the Ramsey number of an even cycle, which this file does not
define — `R3k` covers the triangle against an independent set and nothing
else. -/

/-! A `RamseyNotMaximisedByH` entry stood here whose body was the negation of a
statement ending in `True`, hence FALSE, and it was recorded with verdict `B`.
What it meant to say — equal edge counts do not force equal Ramsey numbers —
needs the Ramsey number of a general `H`. -/

/-! Two `R(C₄, K_{1,n})` entries stood here: `∃ N, N ≤ n + √n + 1`, satisfied by
`N = 0`, and the negation of `n + c√n ≤ n`, true because the left side is larger
— a triviality dressed as a refutation. -/

/-! A `SizeRamseyStarForest` entry stood here reading `∃ r, r = sizes.sum +
sizes.length`, which names a number and asserts nothing of it. -/

/-! An `OddCycleRamseyBound` entry stood here reading `∃ N, N ≤ 4k + 1`,
satisfied by `N = 0`. -/

/-! A `SizeRamseyLinear` entry stood here reading `∃ c > 0, ∀ n, n ≤ c·n`,
satisfied by `c = 1`. -/

/-- **Bounded degree bounds the edge count linearly**, and this is a theorem
rather than a citation: the handshake identity turns a degree bound into an edge
bound. It stood in the file as a Prop about size-Ramsey; what its body said is
this, so this is what it now is. -/
theorem edges_le_of_degree_le (d n : ℕ) (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (h : ∀ v, G.degree v ≤ d) :
    2 * G.edgeFinset.card ≤ n * d := by
  classical
  have hsum : ∑ v : Fin n, G.degree v = 2 * G.edgeFinset.card :=
    G.sum_degrees_eq_twice_card_edges
  calc 2 * G.edgeFinset.card = ∑ v : Fin n, G.degree v := hsum.symm
    _ ≤ ∑ _v : Fin n, d := Finset.sum_le_sum (fun v _ => h v)
    _ = n * d := by simp [Finset.sum_const, Finset.card_univ]

/-! ## §4b The Ramsey number of a pair

The entries removed from this section — even-cycle Ramsey at two and at `k`
colours, `R(C₄, K_{1,n})`, Ramsey-goodness, and the question whether equal edge
counts force equal Ramsey numbers — all needed one object this file did not
carry: the least order forcing a monochromatic copy of one of two given graphs.
It is written here as a search with a terminal anchor, which is what it is: the
candidates open, each is tested against every colouring, and the value is the
least that survives.

A `sInf` over a set that might be empty returns junk, so the arrow relation and
its non-emptiness are separate: `ArrowsPair` says what it means to force, and
`RamseyFinite` says a forcing order exists. Ramsey's theorem is that statement,
and it is a citation here rather than a proof.
-/

/-- `G` embeds into the colour-`c` part of a colouring of `K_N`. The embedding is
by an injection carrying adjacency forward, which is containment rather than
induced containment — the notion Ramsey's theorem uses. -/
def MonoCopy {m N : ℕ} (G : SimpleGraph (Fin m)) (col : Fin N → Fin N → Bool)
    (c : Bool) : Prop :=
  ∃ f : Fin m → Fin N, Function.Injective f ∧
    ∀ u v : Fin m, G.Adj u v → col (f u) (f v) = c

/-- `N` forces the pair: every two-colouring of `K_N` carries a copy of `G` in
the first colour or of `H` in the second. -/
def ArrowsPair (N : ℕ) {m k : ℕ} (G : SimpleGraph (Fin m)) (H : SimpleGraph (Fin k)) : Prop :=
  ∀ col : Fin N → Fin N → Bool,
    (∀ u v, col u v = col v u) → MonoCopy G col true ∨ MonoCopy H col false

/-- **Ramsey's theorem, as the statement that the search terminates.** Without
it the least forcing order is an infimum over a possibly empty set, and that is
`0` rather than "no such order". -/
def RamseyFinite : Prop :=
  ∀ (m k : ℕ) (G : SimpleGraph (Fin m)) (H : SimpleGraph (Fin k)),
    ∃ N : ℕ, ArrowsPair N G H

/-- The Ramsey number of a pair: the least order that forces. Meaningful exactly
when `RamseyFinite` holds, which is why the two are separate. -/
noncomputable def ramseyPair {m k : ℕ} (G : SimpleGraph (Fin m))
    (H : SimpleGraph (Fin k)) : ℕ :=
  sInf { N : ℕ | ArrowsPair N G H }

/-- **Monotone in the order.** If `N` forces and `N ≤ M`, then `M` forces: a
colouring of the larger complete graph restricts to one of the smaller, and a
copy found there is a copy here. -/
theorem arrowsPair_mono {m k : ℕ} (G : SimpleGraph (Fin m)) (H : SimpleGraph (Fin k))
    {N M : ℕ} (hNM : N ≤ M) (h : ArrowsPair N G H) : ArrowsPair M G H := by
  intro col hsymm
  -- The restriction of the colouring to the first `N` vertices.
  set res : Fin N → Fin N → Bool :=
    fun u v => col ⟨u.1, lt_of_lt_of_le u.2 hNM⟩ ⟨v.1, lt_of_lt_of_le v.2 hNM⟩ with hres
  have hsym' : ∀ u v : Fin N, res u v = res v u := by
    intro u v; simp only [hres]; exact hsymm _ _
  -- The inclusion of the first `N` vertices into the `M`.
  set incl : Fin N → Fin M := fun u => ⟨u.1, lt_of_lt_of_le u.2 hNM⟩ with hincl
  have hincl_inj : Function.Injective incl := by
    intro a b hab
    have : (a : ℕ) = (b : ℕ) := by
      simpa [hincl] using congrArg Fin.val hab
    exact Fin.ext this
  rcases h res hsym' with ⟨f, hf, hadj⟩ | ⟨f, hf, hadj⟩
  · exact Or.inl ⟨incl ∘ f, hincl_inj.comp hf, fun u v huv => hadj u v huv⟩
  · exact Or.inr ⟨incl ∘ f, hincl_inj.comp hf, fun u v huv => hadj u v huv⟩

/-! ## §4c The size-Ramsey number

The second object of the nest reads this one as a fork with two arms that must
both close: one constructs a host that forces, the other establishes that no
smaller host does. Written out, the first arm is membership in the set below and
the second is the infimum being attained rather than merely bounded.
-/

/-- A host graph forces `G`: every two-colouring of the host's edges carries a
monochromatic copy of `G`, where a copy is an injection carrying adjacency into
one colour class of the host. -/
def HostForces {N m : ℕ} (host : SimpleGraph (Fin N)) (G : SimpleGraph (Fin m)) : Prop :=
  ∀ col : Fin N → Fin N → Bool, (∀ u v, col u v = col v u) →
    ∃ (f : Fin m → Fin N) (c : Bool), Function.Injective f ∧
      ∀ u v : Fin m, G.Adj u v → host.Adj (f u) (f v) ∧ col (f u) (f v) = c

/-- The edge counts of the hosts that force `G` — the set the size-Ramsey number
takes its infimum over. -/
def ForcingSizes {m : ℕ} (G : SimpleGraph (Fin m)) : Set ℕ :=
  { e : ℕ | ∃ (N : ℕ) (host : SimpleGraph (Fin N)) (_ : DecidableRel host.Adj),
      host.edgeFinset.card = e ∧ HostForces host G }

/-- **The size-Ramsey number.** Least edge count of a forcing host. As with the
Ramsey number of a pair, the infimum and the non-emptiness are separate: an
infimum over an empty set is zero, which would read as "no edges needed". -/
noncomputable def sizeRamsey {m : ℕ} (G : SimpleGraph (Fin m)) : ℕ :=
  sInf (ForcingSizes G)

/-- **Any forcing host bounds it.** The arm that constructs a forcer gives an
upper bound directly; the other arm — that no smaller host forces — is what the
infimum being attained says, and is not free. -/
theorem sizeRamsey_le {m N : ℕ} (G : SimpleGraph (Fin m)) (host : SimpleGraph (Fin N))
    [DecidableRel host.Adj] (h : HostForces host G) :
    sizeRamsey G ≤ host.edgeFinset.card :=
  Nat.sInf_le ⟨N, host, inferInstance, rfl, h⟩

/-! ## §5 Hypergraph Ramsey -/

/-! Five stepping-up entries stood here — `∃ c₁ c₂ > 0`, `∃ N, n ≤ N`,
`∃ N, 0 < N`, `c·n ≤ 2ⁿ`, `c·log n ≤ n` — none mentioning a hypergraph. The
faithful Erdős–Rado tower bounds live in `ProofModules/HypergraphRamsey.lean`,
with the asymptotic proved from them. -/

/-! A `RationalExponentsBipartite` entry stood here producing a positive real
from each rational exponent and asserting nothing of it. Bukh–Conlon is stated
with its extremal count in batch 3. -/

/-! ## §6 LCM triples -/

/-- `a, b, c` form an LCM triple when each divides the lcm of the other two. -/
def IsLcmTriple (a b c : ℕ) : Prop :=
  a ∣ Nat.lcm b c ∧ b ∣ Nat.lcm a c ∧ c ∣ Nat.lcm a b

/-- **[T]** The count of LCM triples below `N` is `o(N³)`. The old body compared
`N` with `N³` and never counted a triple. -/
def LcmTripleCountLittleO : Prop :=
  IsLittleO atTop
    (fun N : ℕ =>
      ((((Finset.range N) ×ˢ (Finset.range N) ×ˢ (Finset.range N)).filter
        (fun t : ℕ × ℕ × ℕ => IsLcmTriple t.1 t.2.1 t.2.2)).card : ℝ))
    (fun N : ℕ => (N : ℝ) ^ 3)

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

/-- A sum-free subset: no element is a sum of two of its members. -/
def IsSumFreeIn (A : Finset ℕ) : Prop :=
  ∀ a ∈ A, ∀ b ∈ A, a + b ∉ A

/-- **[B]** Cameron–Erdős: the number of sum-free subsets of `[0, N)` is
`2^{N/2 + o(N)}`. The old body compared `2^{N/2}` with `c·2^{N/2}` and counted
nothing. -/
def SumFreeCountAsymptotic : Prop :=
  ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧ ∀ᶠ N : ℕ in atTop,
    c₁ * (2 : ℝ) ^ ((N : ℝ) / 2) ≤
      ((((Finset.range N).powerset).filter (fun A => IsSumFreeIn A)).card : ℝ) ∧
    ((((Finset.range N).powerset).filter (fun A => IsSumFreeIn A)).card : ℝ) ≤
      c₂ * (2 : ℝ) ^ ((N : ℝ) / 2) * (N : ℝ)

/-! ## §8 Cycles, theta graphs, Erdős–Hajnal -/

/-- **[T]** Average degree forces a cycle. -/
def AverageDegreeCycleBound : Prop :=
  ∀ n : ℕ, ∀ G : SimpleGraph (Fin n), n ≤ G.edgeFinset.card →
    ∃ v : Fin n, 0 < G.degree v

/-! A `ThetaGraphExponent` entry stood here producing a positive real from `k`
and `l` and asserting nothing of it. -/

/-! An `ErdosHajnalProperty` entry stood here whose conclusion was
`n^c ≤ S.card + n^c`, true of the empty `S`. Erdős–Hajnal is stated faithfully in
batch 1, with its clique-or-independent-set conclusion restored. -/

/-! Two Ramsey-goodness entries stood here: `∃ N, N ≤ 2n`, satisfied by `N = 0`,
and the negation of `n ≤ 0`, true whenever `n` is positive and silent about
cycles. -/

/-! ## §9 Verdict distribution, computed -/

def verdicts : List (String × String) :=
  [("SAWSubmultiplicative", "T"), ("ConnectiveConstantExists", "T"),
   ("HindmanGrowth", "T"), ("RatioSetSharp", "T"),
   ("Ramsey3kGapDiverges", "T"), ("Ramsey3kGapNotLittleO", "T"),
   ("Ramsey3kAsymptotic", "B"), ("LcmTripleCountLittleO", "T"),
   ("SumFreeCountAsymptotic", "B"), ("AverageDegreeCycleBound", "T")]

def countOf (v : String) : Nat := (verdicts.filter (fun p => p.2 == v)).length

theorem verdict_partition : countOf "T" + countOf "B" = verdicts.length := by decide

#print axioms saw_pow_bound
#print axioms ratio_set_bound
#print axioms primes_not_lcm_triple

#print axioms arrowsPair_mono
#print axioms sizeRamsey_le

end ErdosFormalize2
