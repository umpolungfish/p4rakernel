# A Formal Wiener–Khinchin Identity over Z/dZ, and its Stark-Unit Bridge at d = 2048

**Modules:**
- `Imscribing/Millennium/WKExpand.lean` — Fourier coefficients and the expansion lemma
- `Imscribing/Millennium/WienerKhinchinFull.lean` — the identity (Part I)
- `Imscribing/Millennium/SIC_D2048_WKBridge.lean` — the Stark-unit bridge (Part II)

**Status:** fully proven, zero `sorry`, no `sorryAx` in the axiom dependencies —

```
lake build Imscribing.Millennium.WienerKhinchinFull   # succeeds
lake build Imscribing.Millennium.SIC_D2048_WKBridge   # succeeds
```

Axiom audit of the headline theorems (`wk_full`, `wk_2048`, `comp_overlap_eq_nu`,
`a0_spectrum`, `nu0_of_norm_gate`): `[propext, Classical.choice, Quot.sound]` only.

## Abstract

We formalize, in Lean 4 against Mathlib, the finite-diagram Wiener–Khinchin
identity: the modulus squared of the b-th Fourier coefficient of a weight
`N : ZMod d → ℝ` equals the discrete Fourier transform of its deterministic
autocorrelation. Concretely,

```
wk_full : star (nu d N b) * nu d N b
        = ∑ m : ZMod d, ((corr d N m : ℝ) : ℂ) * w ^ (b * m).val
```

where `w = fourierRoot d := exp (2πi / d)` is the primitive d-th root of
unity, `nu d N b = ∑ k, ↑(N k) * w ^ (b * k).val` is the b-th Fourier
coefficient (from `Imscribing.Millennium.WKExpand`), and

```
corr d N m = ∑ l : ZMod d, N (m + l) * N l
```

is the additive autocorrelation. This is the a=0 ⇄ flatness equivalence piece
of the Montgomery–Vaughan 220 program: the spectrum of the correlation
(every term `corr(m) w^{bm}` weighted by a positive modulus square) is the
power spectrum of `N`.

Part II instantiates this at `d = 2048` on the S-unit moduli of the Stark-unit
field `ℚ(√4190205)`: it proves that the exact-arithmetic register of the
a = 0 stratum (`SIC_D2048_A0Stratum`'s sparse ring `R = F₂₀₄₈[ω]/(ω²⁰⁴⁸−1)`)
and the spectral register of Part I agree under evaluation — the Gaussian
overlap-square of the eleventh-hour campaign *is* the Wiener–Khinchin
spectrum, exactly.

# Part I — The identity (WienerKhinchinFull)

## Setting

All weights are real-valued functions on the cyclic group `ZMod d`, `d ≠ 0`;
the coefficient `ν_b` and the root extract `w` live in `ℂ`, with `star` the
complex conjugation antinvolution of `ℂ`. The statement is an identity of
complex numbers, derived from a completed square (`star ν * ν ≥ 0` in
spirit), so it carries the positive-definiteness pressure of the classical
Wiener–Khinchin theorem into the finite setting without measure theory.

## Proof outline

The proof is a single tactic block of five moves after expanding
`star (nu d N b) * nu d N b` via `wk_expand` into the double sum
`∑ k ∑ l, ↑(N l) * (star w)^{b·l} * ↑(N k) * w^{b·k}`:

1. **Root-of-unity lemmas.** `w ^ d = 1` (from `exp_nat_mul`-style
   exponent splitting plus `exp_eq_one_iff`), hence `w ^ (n % d) = w ^ n`
   via `Nat.div_add_mod`, hence the character law
   `w ^ (u + v).val = w ^ u.val * w ^ v.val`.

2. **Exponent identity.** `(star w)^{b·l} * w^{b·(l+m)} = w^{b·m}`, by
   splitting `b·(l+m) = b·l + b·m` with the character law and collapsing
   `(star w)^{b·l} * w^{b·l} = 1` via `fourierRoot_star_mul`.

3. **Summand key.** Up to commuting the real factors,
   `↑(N l) · (star w)^{b·l} · ↑(N (l+m)) · w^{b·(l+m)} = ↑(N l) · ↑(N (l+m)) · w^{b·m}`.

4. **Two-step reindexing of the double sum.** Instead of a product-equiv on
   `ZMod d × ZMod d` (whose projections of an opaque `have`-equiv do not
   reduce definitionally — the failure mode of the earlier `change`-based
   attempt), the reindexing is split into two single-index translations,
   each a `Fintype.sum_equiv` with an *inline* equiv:
   - reverse the inner index: `(k, l) ↦ (k, k − m)`, then swap sums;
   - translate forward: `m ↦ j = k − m`, folded back with the cancel law
     `(z + m) − m = z`, landing on `∑ m ∑ l, ↑(N l) * ↑(N (l+m)) * w^{b·m}`.

5. **Folding.** `Finset.sum_mul` factors `w^{b·m}` out of the inner sum,
   and the remaining real sum is `corr d N m` up to `add_comm` inside `N`
   (the `congrArg N (add_comm l m)` step) and `mul_comm` of the two factors;
   `push_cast` moves the coercion through the sum.

## Formal hygiene

- No `sorry`, no axioms beyond Lean's; plain `rw`/`calc`/`simp`/`push_cast`.
- The proof is immune to the earlier scratch-copy vs module divergence: it
  contains no `change` tactics and no local-notation-sensitive patterns, so
  the scratch probe (`lake env lean`) and the module (`lake build`) agree.

# Part II — Stark units: the d = 2048 bridge (SIC_D2048_WKBridge)

## The Stark-unit field

The SIC-POVM base field in dimension `d` is `ℚ(√m_d)` with the Appleby
discriminant `m_d = (d−3)(d+1)`. The Stark unit is

```
ε_d = ((d−1) + √m_d) / 2,        N(ε_d) = 1
```

and `SIC.StarkUnit` proves the norm-one statement *dimension-free*: the
discriminant shifts to `N² − 4` for `N = d−1` (`disc_eq`), and
`normForm m_d (N/2) (1/2) = 1` is a two-line `ring` identity in the
coefficients (`norm_one`). At `d = 2048`:

- `m_2048 = (2048−3)(2048+1) = 2047² − 4 = 4190205` (`SIC.StarkUnit.d2048`
  — the field is `F₂₀₄₈ = ℚ(√4190205)`, and `m2048_not_square` certifies it
  genuinely quadratic);
- `ε_2048 = (2047 + √4190205)/2`;
- the S-unit moduli campaign feeds modulus data `N : ℕ → F₂₀₄₈` into the
  a = 0 stratum's eleven coarse slots `O_{0,b}(N) · Ō_{0,b}(N) = 1/2049`,
  `b ∈ {1, 2, 4, …, 1024}` (`a0_b_values`, the 2-adic orbit reps with
  `v₂(a) = 999`).

The a = 0 stratum module carries **no modulus values** — every slot is
parametric in `N`, pending `gen_lean_2048_a0.py` pinning real S-unit moduli.
The bridge keeps that discipline: it fixes *no data* and proves only how the
register of the stratum relates to the spectrum of Part I.

## Two registers, one theorem

Lean carries the same campaign in two registers:

| Register | Object | Home |
|----------|--------|------|
| Exact arithmetic | `R = F₂₀₄₈[ω]/(ω²⁰⁴⁸−1)`, sparse assoc lists `RElt` with `radd`/`rmul`/`rconj` | `SIC_D2048_A0Stratum` |
| Evaluation | `φ : F₂₀₄₈ ↪ ℂ`, `a₀ + a₁θ ↦ a₀ + a₁·√4190205` (`phi`), and `comp : R → ℂ`, `∑ φ(c)·w^e` | `SIC_D2048_WKBridge` |
| Spectral | `ν_b = ∑ ↑(N k) w^{bk}` and `corr` | `WKExpand` / `WienerKhinchinFull` |

The bridge proves the registers agree exactly, no `sorry`, no data:

| Theorem | Content |
|---------|---------|
| `sq_s2048`, `s2048` | `√4190205` lands in `ℂ`: `s² = m_d` (`phi` respects the norm form) |
| `w2048_one`, `w2048_mod` | `ω = e^{2πi/2048}` is a certified 2048-th root of unity in `ℂ` |
| `comp_rmul_hom` | `comp` is a ring homomorphism `R → ℂ`: the sparse arithmetic (`radd`, `rmul`, `rK`, `omegaPow`, `rinsert`) reduces faithfully under `φ` |
| `comp_overlap_a0` | `comp (overlap_a0 N b) = ∑ k, ↑φ(N k) · w ^ (b·k % 2048)` — the exact-arithmetic overlap evaluates to the Fourier sum, term by term |
| `phi_Nr` | `φ (N k) = ↑(Nr N k)` for `k < 2048` — the F₂₀₄₈-coefficient reads off as a real modulus |

| Theorem | Content |
|---------|---------|
| `wk_2048` | Part I instantiated at `d = 2048` for pushed-forward real data `Nr N` |
| `comp_overlap_eq_nu` | `comp (overlap_a0 N b) = ν_b(Nr N)` — **exactly**: the overlap in `R` evaluated in `ℂ` *is* the b-th Fourier coefficient of the S-unit moduli |
| `a0_spectrum` | `star (comp (overlap_a0 N b)) * comp (overlap_a0 N b) = ∑ m, ↑(corr m) · w^{b·m}` — the overlap-square of the Stark-unit moduli is the Wiener–Khinchin spectrum |
| `nu0_of_norm_gate` | the norm gate `⊞_k N_k = 1` forces `ν_0(Nr N) = 1` — the b = 0 slot of the same equation, i.e. the moduli sum itself is pinned |

## What the bridge observes

1. **The slot target becomes a spectral statement.** Once `gen_lean_2048_a0.py`
   pins S-unit moduli and the `native_decide` slots fire
   (`a0_overlap_sq_eq N b = true` in `R`), `a0_spectrum` transfers each
   verdict to `ℂ` automatically: `∑_m corr(m) ω^{bm} = 1/2049` on every
   coarse rep `b`. Conversely the spectrum side is now *computable* in
   floating point + exact rational autocorrelation of the moduli alone.

2. **One correlation, eleven slots.** The right side of `a0_spectrum` is
   independent of the slot's b beyond the root-of-unity weight `ω^{bm}`:
   the autocorrelation `corr` of the moduli is a single object, and the
   eleven coarse slots are eleven probes of its spectrum. The
   Wiener–Khinchin identity is what makes "many slots, one datum" a theorem
   instead of an accident.

3. **Positivity holds by kind.** `star (comp O) * comp O` is a modulus
   square, hence `≥ 0` in `ℝ` — the a = 0 flatness pressure of the
   Montgomery–Vaughan pipeline applies to any admissible S-unit data, and
   `corr(0) = ∑_k N_k²` is the lower anchor
   (`corr ≥ corr(0)`-style arguments become available).

4. **The norm gate is the b = 0 slot.** `nu0_of_norm_gate` shows the gate
   `⊞ N_k = 1` (the mass normalization of the S-unit data) is precisely
   the vanishing of the b = 0 deviation — the boundary condition the
   fiducial's flatness must meet.

## Role in the program

Part I gives the general finite identity behind the Erdős-220 flatness
pipeline (`Imscribing/Millennium/Erdos/Proofs/MontgomeryVaughan220/Fourier.lean`).
Part II connects it to the d = 2048 Stark-unit stratum: the exact-arithmetic
register `R` of `SIC_D2048_A0Stratum` evaluates faithfully into `ℂ`
(`comp_rmul_hom`), the slots become Fourier coefficients
(`comp_overlap_eq_nu`), the slot squares become power spectra
(`a0_spectrum`), and the norm gate pins `ν_0 = 1` (`nu0_of_norm_gate`). The
remaining open planks are unchanged: real S-unit moduli pinned by
`gen_lean_2048_a0.py` (promoting the `native_decide` slots), the
a-parameterized generalization beyond `a = 0`, and the positivity orbit
`corr 0 = ∑ N l * N l ≥ 0`.
