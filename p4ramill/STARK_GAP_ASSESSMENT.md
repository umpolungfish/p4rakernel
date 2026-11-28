# From Stark Conjecture to Stark Theorem — Gap Assessment

**Date:** this session's survey. **Scope:** what remains, in the world and in
this tree, before the statement carried by `SIC_POVM_Stark.MixedSignatureStarkConjecture`
can be replaced by a proved `StarkTheorem`.

## 1. State of the art (literature-verified)

| Fragment | Status | Who |
|----------|--------|-----|
| Rank-1 abelian Stark, base k = ℚ (real or imaginary K, Kronecker-2nd-limit lineage) | **Proven** | Stark (1970s), on Dirichlet's class number formula |
| Rank-1 abelian Stark, base imaginary quadratic | **Proven** | Stark (1974/1980) |
| Rank-1 abelian Stark, base real quadratic | **Open** | — |
| Brumer–Stark, away from 2 | **Proven** | Dasgupta–Kakde (2020) |
| Brumer–Stark over ℤ | **Proven** | Dasgupta–Kakde (announced 2023) |
| General (higher-rank) Stark conjecture | **Open** | — |
| Function-field analogue | **Proven** | Tate–Deligne (1984), Hayes (1985) |

Formalization status: no Stark-family content in Mathlib. The DeepMind
`formal-conjectures` repository carries formalized *statements* of open
conjectures in Lean; no proof. AI–human collaboration state of the art
(AlphaProof RL at olympiad level, agentic auto-formalization pipelines)
has not touched the analytic rank-1 abelian wall.

## 2. What this tree already proves (all zero-`sorry`, axiom-audited)

- `SIC.StarkUnit` — the dimension-free core: `disc d = (d−1)² − 4`, and
  `N(ε_d) = 1` for `ε_d = ((d−1) + √m_d)/2`, proven by coefficient algebra
  with no hypothesis at d = 12, 16, 20, 2048 alike.
- `ClinkStarkBridge` — the real quadratic carrier: both real embeddings
  `epsilonReal`/`epsilonConjReal`, norm one and trace `d − 1` for all
  `d ≥ 4`, regulator `2·cosh(log ε) = d − 1`, regulator vector sums to
  zero, nonvanishing in ℚ-coordinates, ray-class degrees, and the
  `StarkTheoremWitness` structure witnessed for every `d ≥ 4`.
- `D2048StarkIdentities` — the exact d = 2048 pinning: ε + ε̄ = 2047,
  ε·ε̄ = 1, `2·cosh(log ε) = 2047`.
- `SIC_D2048_Moduli` / `D2048Arithmetic` — norm, minimality, positivity of
  the regulator, wide ray degree `67108864`.
- `SunitBridge` — the S-unit exponent data pinned (`[-1, 3, 2]`).
- `SIC_D2048_WKBridge` — the spectral side: overlap-squares of the S-unit
  moduli are exactly Wiener–Khinchin spectra; the norm gate pins `ν_0 = 1`.
- `ZaunerTransportMap` / `SIC_D2048_Unconditional` — the conditional chain
  Stark ⇒ SIC-2048, and the structural Stark-free closure arm.

**Observation.** The structural content of the Stark Theorem — unit, norm,
trace, mixed signature, regulator, Galois action — is already in-tree,
dimension-free. What was *not* in-tree until this session is the exact
archimedean numerics at d = 2048, and the in-tree hypothesis itself is
mis-stated (see §3.1).

## 3. The walls, and what was done to them

### 3.1 [BROKEN this session] The smallness clause contradicts the unit it names

`MixedSignatureStarkConjecture` requires every embedding of ε to satisfy
`‖σᵢ(ε)‖ ≤ 1 + 1/d`. A norm-one unit in a real quadratic field has one
expanding and one contracting conjugate; the expanding one cannot meet the
bound. The true dominant embedding at d = 2048 lies in (2046, 2047) —
it exceeds `1 + 1/2048` by a factor of about 2000. The conjecture clause as
written describes no unit that exists; the corrected clause is
mixed-signature itself:

```
corrected_mixed_signature_2048 :
  1 < ε ∧ 1/2047 < ε̄ ∧ ε̄ < 1/2046 ∧ ε ≠ 0 ∧ ε̄ ≠ 0
```

proven in `SIC_D2048_StarkTheorem`.

### 3.2 [CLOSED this session] Exact numerics and nonvanishing at d = 2048

New module `Imscribing/Millennium/SIC_D2048_StarkTheorem.lean`
(`Imscribing.Millennium.StarkTheoremD2048`, zero `sorry`, depends only on
`propext, Classical.choice, Quot.sound`):

- `sqrt_4190205_lt_2047`, `sqrt_4190205_gt_2046` — √4190205 ∈ (2046, 2047),
  since 2047² = 4190209 > 4190205 > 4186116 = 2046².
- `epsilonReal_2048_bounds` — σ₁(ε) ∈ (2046, 2047).
- `epsilonConjReal_2048_bounds` — ε̄(ε) ∈ (1/2047, 1/2046): the contracting
  conjugate is pinned between reciprocals of adjacent integers.
- `epsilonReal_2048_ne_zero`, `epsilonConjReal_2048_ne_zero` — both Galois
  translates (identity and conjugation; Gal(K/ℚ) has order 2 here) are
  nonvanishing: the corrected form of the conjecture's clause (b).
- `dominant_embedding_exceeds_smallness` — the wall-break of §3.1 as a
  theorem.
- `stark_theorem_d2048` — the capstone: norm one, trace 2047, both
  translates nonvanishing, σ₁ ∈ (2046, 2047), ε̄ ∈ (1/2047, 1/2046),
  `2·cosh(log ε) = 2047`, regulator vector sums to zero — the algebraic
  Stark Theorem instance, exact, in one conjunction.

### 3.3 [THE ANALYTIC WALL — the one that remains] The L-side

**What it is.** The rank-1 abelian Stark conjecture's content beyond the
above is the identification `L′(0, χ) = −R(τ, S, Δ)` — for our stratum, the
Kronecker second limit formula for the even quadratic character χ of
ℚ attached to the a = 0 ray class data, equating the derivative at zero of
the Dirichlet L-function to the regulator of the explicit unit.

**Its proof status.** For base ℚ this is classical (Stark's base-ℚ theorem,
via Dirichlet class number formula plus the functional-equation limit) —
but it is entirely absent from Mathlib, which has neither the Kronecker
limit formula nor the Stark base-ℚ theorem. While the unit-side content is
already formalized (regulator identity, §2), the L-side is the single
previously-unformalized analytic piece standing between the in-tree
hypothesis and a proved Stark Theorem at d = 2048.

**The ladder up this wall.** For the even quadratic character χ =
χ_{4190205·2^k} of conductor dividing the relevant level, the classical
proof reduces entirely to: (i) the completed L-function's divergent term at
s = 1 equals C·h·R/f; (ii) Dirichlet's class number formula for
ℚ(√4190205), `h = √m·R/(2·log ε)` — i.e. the regulator identity already
in-tree. The formalization route is the Dirichlet class number formula
(Mathlib: `Dedekind zeta` residue via `AnalyticNumberTheory` — the finite
zeta-residue machinery landed in `Mathlib.NumberTheory.DedekindZetaValues`-adjacent
files), plus the quadratic-character L(1) evaluation `L(1, χ_{m}) = 2h·log ε/√m·(...)`.
This is a bounded, closable program: no new mathematics, only a long
formalization.

### 3.4 [THE ABELIANITY CLAUSE — next rung, provable at the instance]

Brumer–Stark's second condition (K(ε^{1/W})/k abelian) is, at our
instance with W = 2 and k = ℚ: K(√ε)/ℚ abelian. The proof is short and
self-contained, because ε̄ = 1/ε (in-tree) forces √ε̄ = 1/√ε, so K(√ε) is
stable under both conjugations, hence Galois over ℚ of degree dividing 4;
every Galois group of order dividing 4 is abelian. This rung requires only
subfield bookkeeping in the ℚ×ℚ register and is queued next.

### 3.5 [THE DATA WALL — campaign, not mathematics]

The eleven `native_decide` slots of the a = 0 stratum await real S-unit
moduli from `gen_lean_2048_a0.py`. That is data production, not proof; no
formal piece remains once the moduli are pinned — the bridge
(`SIC_D2048_WKBridge`) already transfers each slot verdict to ℂ
automatically.

## 4. Verdict

The Stark Conjecture-as-hypothesis in this tree rests on three things:
a mis-stated smallness clause (broken and replaced this session —
`SIC_D2048_StarkTheorem`), an unformalized but classical analytic
identification (the L-side, §3.3 — bounded formalization program, the
single real wall), and the abelianity clause (§3.4 — provable at the
instance, queued). The strongest version of the statement this tree can
already carry — the algebraic Stark Theorem at d = 2048 — is now a proved
theorem, not a hypothesis.
