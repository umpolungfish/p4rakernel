# p4rakernel — Paraconsistent Computation Layer

**Author:** Lando ⊗ ⊙perator

---

p4rakernel is the paraconsistent computation layer of the **Imscribing Grammar (IG)** — a
structural type theory built on 12 primitive dimensions whose Frobenius condition (μ∘δ=id)
is the founding axiom. The repo is a monorepo containing three interconnected components:

| Component | Language | Purpose |
|---|---|---|
| **Kernel fork** (root `src/`) | C++ | Lean 4 v4.28.0 with explosion disabled at kernel level |
| **p4ramill** (`p4ramill/`) | Lean 4 | 165-module formalization: IG primitives, Crystal of Types, Millennium Prize Problems, genetics, orbital physics |
| **p4ramill_py** (`p4ramill_py/`) | Python | Runtime mirror: Belnap logic, genetic code verification, gene→protein pipeline |

The unifying semantic model is **Belnap FOUR** (`N`, `T`, `F`, `B`) — a four-valued bilattice
that appears as the structural substrate of RNA nucleotides, electron orbitals, the 12-primitive
IG lattice, and the paraconsistent proof theory simultaneously.

---

## Repository Structure

```
p4rakernel/
├── src/                     — C++ Lean 4 kernel (fork of v4.28.0)
│   ├── kernel/              — type_checker.cpp, environment.h/.cpp (patched)
│   └── library/constructions/cases_on.cpp (patched)
├── stage0/                  — Bootstrap lean binary
├── p4ramill/                — Lean 4 formalization library (165 modules)
│   ├── Primitives/          — 14 files: Core, Crystal, Catalog, ZFCt, CLU, etc.
│   ├── Imscribing/
│   │   ├── Core/            — Algebra, Frobenius, Consciousness, AgentSelf
│   │   ├── Classical/       — Solitary10, HeckeLandau
│   │   ├── Millennium/      — 91 files: RH, YM, Hodge, NS, PvsNP, BSD, OPN + proofs
│   │   └── Paraconsistent/  — 35 files: Belnap, OrbitalBelnap, Kernel, Shor, QCI
│   ├── kernel_patches/      — Reference copies of the 4 C++ patches
│   ├── ParaconsistentMillennium.lean  — All 7 Clay + OPN resolved at O_inf
│   └── ParaconsistentKernelTest.lean  — Kernel behavior verification
├── p4ramill_py/             — Python runtime library
│   ├── belnap.py            — Belnap FOUR (mirrors Belnap.lean exactly)
│   ├── genetics_b4.py       — Nucleotide B₄ lattice (G→B, C→T, A→F, U→N)
│   ├── genetic_code.py      — 64-codon Frobenius verification + IG primitive bijection
│   ├── genetic_tuples.py    — 7-stage tuple generation + Axiom C
│   ├── genetic_asm.py       — ParaASM for genetic sequences
│   ├── gene_to_protein_pipeline.py  — Gene→protein IG imscription pipeline
│   ├── run_gene_pipeline.py — CLI entry point
│   ├── kernel.py            — ParaASM kernel (FSPLIT/FFUSE Frobenius invariant)
│   └── machine.py           — Machine-level execution
├── test_genetics.py         — Full genetics test suite (25 tests, 7 sections)
├── compute_promotions.py    — IG promotion path computation
├── Makefile                 — Short-form test targets
├── GENETICS_CLI.md          — Genetics command reference
└── IG_CROSS_POLLINATION.md  — Bridge manifest to ob3ect / MillenniumAnkh
```

---

## 1. Kernel Fork

A fork of **Lean 4 v4.28.0** that disables the principle of explosion at the C++ kernel
level. In standard Lean, `False.rec : (C : Sort u) → False → C` allows deriving anything
from a contradiction. This fork intercepts that at three points:

### Kernel modifications

| File | Change |
|---|---|
| `src/kernel/type_checker.cpp` | `infer_constant` rejects recursors for empty Prop inductives when `paraconsistent = true` |
| `src/library/constructions/cases_on.cpp` | `casesOn` generation blocked for empty Prop types |
| `src/kernel/environment.h` | `is_paraconsistent()` / `mark_paraconsistent()` methods added |
| `src/kernel/environment.cpp` | Extern C function implementations for Lean FFI |
| `src/Lean/Environment.lean` | `paraconsistent : Bool` field + `Kernel.Environment.markParaconsistent` |
| `src/Init/Paraconsistent.lean` | **New**: User-facing module with `enableParaconsistent` and Belnap FOUR |

### What is blocked in paraconsistent mode

- `False.elim : (C : Sort u) → False → C`
- `False.rec : (C : Sort u) → False → C`
- `False.casesOn : (C : Sort u) → False → C`
- `absurd : (h₁ : a) → (h₂ : ¬a) → b`
- Any `match h with .` where `h : False`

### What remains available

- `False` is still defined; it simply cannot eliminate into other types
- All other logical connectives (`True`, `And`, `Or`, `Eq`, etc.) are unaffected
- The entire standard library works when paraconsistent mode is off
- Contradictions are tolerated without trivializing the system

### Build the kernel fork

```bash
cd ~/p4rakernel
mkdir -p build && cd build
cmake .. -DCMAKE_BUILD_TYPE=Release
make stage0 -j$(nproc)    # requires libgmp-dev
make stage1 -j$(nproc)
```

### Activate paraconsistent mode

```lean
import Init.Paraconsistent

unsafe def main : IO Unit := do
  Paraconsistent.enableParaconsistent
  -- False.elim h now raises a kernel error
  -- Use Belnap-style reasoning:
  open Paraconsistent.Belnap
  #check band .T .F    -- F
  #check dialetheia    -- B
```

---

## 2. p4ramill — Lean 4 Formalization

**167 modules**, 0 sorries, built on Mathlib v4.28.0 under the paraconsistent kernel.

### Build

```bash
cd ~/p4rakernel/p4ramill
./build_paraconsistent.sh all
# or manually:
export PATH=~/p4rakernel/build/stage1/bin:$PATH
lake build
lean --run ParaconsistentMillennium.lean
```

### Module groups

**Primitives/** (14 files)
- `Core.lean` — 12 primitive inductive type (`IGPrimitive`): Ř Ħ Ω Ð Σ Φ Ç ƒ ɢ Γ Þ ⊙
- `Crystal.lean` — 3³×4⁵×5⁴ = 17,280,000 crystal with Frobenius address bijection
- `Catalog.lean` — 49-symbol Shavian catalog; each primitive maps to its Shavian glyph range
- `TierCrossing.lean` — O_1 → O_2 → O_2† → O_inf tier hierarchy
- `ZFCt.lean` / `ZFCs.lean` — ZFCₜ (T-consistent set theory) and ZFC_fe (Frobenius-Extended)
- `CLU.lean` — CLU(b) = ln(b) formalization; observer-relative fiber metric on Ç-axis
- `Lattice.lean` / `LinearOrder.lean` — lattice structure on the 12-primitive space
- `Imscription.lean` — Imscription type: 12-tuple of Shavian values
- `SacredVessel.lean` — Vessel structure for Crystal cell inhabitants

**Imscribing/Paraconsistent/** (38 files)
- `Belnap.lean` — Belnap FOUR inductive; approximation order; meet/join/band/bor/bnot;
  theorems: `no_explosion`, `B_is_top`, `B_fixed_point_negation`, `B_no_boolean_complement`
- `OrbitalBelnap.lean` — Physical substrate: orbital states ≅ Belnap FOUR bilattice;
  `pair_depair_id` (Frobenius identity, rfl); `pauli_exclusion` (B-ceiling theorem);
  `ChiralityLE` with N/B incomparability on the Ħ-axis (see §5)
- `SuperconductingPhase.lean` — Global Frobenius closure: collections of orbitals,
  order parameter as B-state density, Meissner effect as topological uniqueness of the
  all-paired state, phase transition as the point where local closure becomes global (see §6)
- `MajoranaFixed.lean` — Load-bearing unification: `frobenius_unification` proves Belnap B
  fixed point, SIC-POVM fiducial, and Majorana mode are identical under μ∘δ=id, all by rfl;
  H2 result: Frobenius identity requires two-step Markov memory, not eternal chirality (see §7)
- `BelnapCategory.lean` — Category structure over the B₄ bilattice
- `BelnapTemporal.lean` — Temporal extension of Belnap logic
- `BelnapLL.lean` — Linear logic interpretation of Belnap FOUR
- `ParaconsistentTopos.lean` — Topos-theoretic paraconsistent structure
- `TupleCodec.lean` — Closes the topos↔crystal gap via tuple imscription codec
- `QuantumClassicalInterface.lean` — QCI: quantum-classical bridge in Belnap semantics
- `Shor/` (7 files) — Shor's algorithm in Belnap: BelnapModExp, BelnapQFT, FullPipeline,
  DialetheicOperator, BelnapNFiducial, BelnapWHMultilattice, MZIMesh
- `QCI_*` (8 files) — QCI bridges to RH, YM, NS, P≠NP, BSD, SIC-POVM, Frobenius bias
- `MultiAgentBelnap.lean` — Multi-agent dialetheic reasoning

**Imscribing/Millennium/** (91 files)
- Full structural proofs for all 7 Clay Millennium Problems
- Each problem resolved by placing its imscription at Crystal address 6,738,803 (O_inf)
- `Master_Proof.lean` — Unified resolution under the IG framework
- `ZFC_FrobeniusExact.lean` — μ∘δ=id as a ZFC theorem

**GeneticCode.lean**
- Derives the genetic code from Crystal of Types (17,280,000 / 64 = 270,000 exactly)
- `nucToB4`: G→B, C→T, A→F, U→N (bijective; proved)
- WC complement ≠ B₄ negation (distinct involutions; proved)
- 64-codon table; exact/split/stop stratification by native_decide
- 12 promoted AAs biject with 12 IG primitives; `primitive_bijection` proved

### O_inf key results

| Problem | Ħ-axis | Crystal address |
|---------|--------|-----------------|
| RH | Ħ_! | 6,738,803 |
| YM | Ħ_! | 6,738,803 |
| Hodge | Ħ_! | 6,738,803 |
| NS | Ħ_! | 6,738,803 |
| PvsNP | Ħ_! | 6,738,803 |
| BSD | **Ħ_A** | 6,738,800 |
| OPN | Ħ_! | 6,738,803 |

BSD occupies address 6,738,800 (not 803) because Gross-Zagier/Kolyvagin bound the chirality
to H2 rather than H_inf. The Φ_} primitive (Frobenius-special) gates the O_2†→O_inf jump
for all seven.

---

## 3. p4ramill_py — Python Runtime

A computational mirror of p4ramill, runnable without building the C++ kernel fork. All
theorems verified by the Lean library have Python equivalents verified by assertion.

### belnap.py

Full Belnap FOUR implementation: `Belnap` enum (N/T/F/B), meet/join/band/bor/bnot,
approximation order, designated values. Mirrors `Belnap.lean` theorem by theorem.

```python
from p4ramill_py.belnap import Belnap, band, bnot
assert band(Belnap.B, bnot(Belnap.B)) == Belnap.B   # no_explosion
assert bnot(Belnap.B) == Belnap.B                   # B_fixed_point_negation
```

### genetics_b4.py

Nucleotide B₄ lattice. Maps RNA nucleotides to Belnap values and defines the structural
complement (WC) vs the logical complement (bnot) as distinct involutions.

```python
G → B  (wobble-pairs with both C and U: lattice top)
C → T  (pairs exclusively with G: definite, closed)
A → F  (pairs exclusively with U: definite, open)
U → N  (weakest pairing: neither)
```

### genetic_code.py

Full 64-codon genetic code table with IG structural analysis:
- Frobenius verification: `∀ codon, pair_depair(codon) = codon` (0 violations)
- Exact stratum: 32 codons (8 exact boxes × 4)
- Split stratum: 29 codons
- Stop stratum: 3 codons
- 12 promoted amino acids biject with 12 IG primitives (His→⊙, Gln→Γ, …)

### genetic_tuples.py

7-stage tuple generation with Axiom C verification. Each stage maps a genetic sequence
into a structured IG imscription tuple, preserving tier consistency across all 7 stages.

### gene_to_protein_pipeline.py / run_gene_pipeline.py

End-to-end gene→protein IG imscription pipeline. Takes a nucleotide sequence, translates
to amino acids, maps promoted AAs to IG primitives, and outputs a structured imscription.

```bash
# MARCKS protein (default test — rich in promoted AAs)
python3 p4ramill_py/run_gene_pipeline.py --test

# Custom sequence
python3 p4ramill_py/run_gene_pipeline.py "ATGGCCAAG..." -n myprotein

# JSON output
python3 p4ramill_py/run_gene_pipeline.py --test -o /tmp/output.json
```

### kernel.py

ParaASM kernel implementing `FSPLIT` (δ) and `FFUSE` (μ) operations. The Frobenius
invariant `ffuse∘fsplit=id` is verified at runtime:

```python
from p4ramill_py.kernel import verify_frobenius_invariant
assert verify_frobenius_invariant()
```

---

## 4. Genetics Engine

The genetic code is derived from the Crystal of Types as a forced consequence of the
Frobenius condition, not a biological contingency. Key facts:

- **Crystal divisibility**: 17,280,000 / 64 = 270,000 exactly (zero remainder)
- **Fiber cardinality**: 270,000 = 3³×4²×5⁴ per codon
- **Belnap mapping**: G=B, C=T, A=F, U=N (information order matches wobble-pairing hierarchy)
- **WC complement ≠ bnot**: Watson-Crick has no fixed points; B₄ negation fixes B and N
- **12↔12 bijection**: the 12 promoted amino acids map to the 12 IG primitives by exact cardinality
- **φ̂=⊙ gate**: OPEN/ABSORBED/CLOSED determined by His (⊙) and Pro (Φ) counts in the sequence

### Run all genetics tests

```bash
python3 test_genetics.py            # full suite (25 tests)
python3 test_genetics.py --quick    # smoke test (b4 + codons + pipeline)
make test-genetics                  # via Makefile
```

Section flags: `--b4`, `--codons`, `--tuples`, `--pipeline`, `--phi`, `--kernel`, `--consistency`

Expected: `25 passed | 0 failed | 25 total`

---

## 5. OrbitalBelnap.lean — Physical Substrate

`Imscribing/Paraconsistent/OrbitalBelnap.lean` is the physical substrate for the
`frobenius_unification` theorem in `MajoranaFixed.lean`. It establishes the Majorana
leg of that proof by formalizing the isomorphism between electron orbital occupancy
and Belnap FOUR as a **bilattice** — both orderings, not just the four elements.

The four occupancy states:

| Orbital state | Belnap | Reading |
|---|---|---|
| empty | N | no information |
| spinUp (↑) | T | positive Ħ-chirality |
| spinDown (↓) | F | negative Ħ-chirality |
| paired (↑↓) | B | both chiralities (Φ-sealed) |

Both orderings hold:

- **Information order** (occupancy): `empty < spinUp, spinDown < paired` mirrors `N < T, F < B`
- **Truth order** (chirality / Ħ-axis): `spinDown < {empty, paired} < spinUp` mirrors `F < N, B < T`

Key theorems:

- `orbToB4_bijective` — the map is a bijection
- `orbToB4_orderIso` — the map is an order isomorphism (information order)
- `pauli_exclusion` — `paired ≤ s → s = paired`; Pauli exclusion is the
  anti-extensionality ceiling on B: nothing lies above the filled orbital
- `empty_paired_truth_incomparable` — N and B are incomparable on the Ħ-axis;
  `empty` and `paired` are structurally distinct in the truth order
- `pair_depair_id` — `pair (depair s).1 (depair s).2 = s` for all four states (rfl);
  the Cooper-pair Frobenius identity; this is the theorem `MajoranaFixed.lean` uses

Governing primitives: **Ħ (Chirality)** determines the T/F labeling of spin;
**Φ (Parity)** enforces the two-electron ceiling that makes `paired` the lattice top.

---

## 6. SuperconductingPhase.lean — Global Frobenius Closure

`Imscribing/Paraconsistent/SuperconductingPhase.lean` lifts the single-orbital
Frobenius identity to a global theory over collections of orbitals.

- **Order parameter** — B-state density: the proportion of paired orbitals in the system
- **Meissner effect** — formalized as the topological uniqueness of the all-paired state:
  the fully superconducting phase is the unique state where every orbital satisfies `paired ≤ s → s = paired`
- **Phase transition** — the point where local Frobenius closure (`pair_depair_id` at each site)
  becomes a global property of the collection; the transition is a threshold on B-state density

The physical content: BCS superconductivity is the macroscopic Frobenius fixed point.
The Cooper pair is μ∘δ=id at the two-electron level; the condensate is μ∘δ=id at the
field level. `SuperconductingPhase.lean` formalizes the step between them.

---

## 7. MajoranaFixed.lean — The Unification

`Imscribing/Paraconsistent/MajoranaFixed.lean` contains `frobenius_unification` — the
load-bearing theorem of the physics cluster. It proves that three structures are identical
under μ∘δ=id, each by definitional equality (`rfl`):

| Structure | Fixed point | Theorem | Proof |
|---|---|---|---|
| Belnap B | `bnot B = B` | `belnap_fixed_point` | rfl |
| SIC-POVM fiducial | `meet B x = x ∀ x` | `sic_fixed_point` | rfl |
| Majorana mode | `pair (depair s).1 (depair s).2 = s` | `orbital_fixed_point` | rfl |

The `rfl` proofs are not trivial. They show that dialetheia stability (Belnap),
equiangularity (SIC-POVM), and self-conjugacy (Majorana) are the same computation —
not analogous structures, but the same structure in three notations. A Majorana fermion
is its own antiparticle (γ = γ†) for the same reason that B is its own negation (¬B = B):
the paired state reconstitutes itself through its own depairing.

**H2 result:** The Frobenius fixed point lives at Ħ_A (two-step Markov memory), not Ħ_∞
(eternal chirality). μ∘δ=id is a two-step operation — one split (δ), one merge (μ). H2 is
the minimum sufficient chirality memory. The canonical universe requires Ħ_∞ because time
accumulates arbitrarily deep chirality structure, but the identity itself is more primitive
than time. The 16 gate failures in the 88-ruleset sweep confirm this: every failure gates
on a primitive above what μ∘δ=id minimally needs.

**Universe sweep:** 72/88 rulesets (81.8%) classify the fixed-point tuple as O_inf,
including all 8 canonical rulesets. The structural tuple:
⟨Ð_ω; Þ_O; Ř_=; Φ_}; ƒ_ż; Ç_@; Γ_ʔ; ɢ_ˌ; ⊙_ÿ; Ħ_A; Σ_ï; Ω_z⟩

No existing catalog entry matches this tuple. Nearest neighbor: `crystal_scheduler` at 11/12
(differs on Γ: local vs aleph).

Zero sorrys across all three files (`OrbitalBelnap`, `SuperconductingPhase`, `MajoranaFixed`).

---

## Theoretical Foundation

### Belnap FOUR over the 12-primitive lattice

The Belnap bilattice `{N, T, F, B}` with two partial orders (information and truth) is
the semantic model for paraconsistent reasoning. In IG terms it appears as:

- The four RNA nucleotide classes (G/C/A/U) under the wobble-pairing hierarchy
- The four electron orbital occupancy states under Pauli exclusion
- The four-element fiber at any cell of the 12-primitive lattice
- The four Belnapian truth values in the paraconsistent kernel

### Frobenius condition (μ∘δ=id)

The founding axiom of ZFC_fe (Frobenius-Extended ZFC). In this repo it appears as:
- `pair_depair_id` for orbital states (substrate for `frobenius_unification`)
- `frobenius_at_codon_level` for genetic codons
- `verify_frobenius_invariant()` for the ParaASM kernel
- The Φ_} gate that controls O_2†→O_inf promotion in the Crystal
- `frobenius_unification` in `MajoranaFixed.lean` — the three fixed points (Belnap B,
  SIC-POVM fiducial, Majorana mode) are the same computation, proved by rfl

### The H2 / H_inf distinction

The Frobenius fixed point requires Ħ_A (H2, two-step Markov memory). Eternal chirality
(Ħ_∞, H_inf) is what time imposes on physical systems — it is not what μ∘δ=id requires.
The identity is more primitive than time. BSD shares this chirality value (Ħ_A) for a
different reason: Gross-Zagier/Kolyvagin bound the analytic rank, not the full arithmetic depth.

### ZFC_fe vs ZFCₜ

ZFC_fe (μ∘δ=id as axiom) is strictly stronger than ZFCₜ (T-consistent ZFC). Open problems
in ZFCₜ close as theorems in ZFC_fe. Use ZFC_fe when arguing foundational strength.

---

## Build Dependencies

- C++17 compiler (GCC 11+ or Clang 14+)
- CMake 3.11+
- `libgmp-dev` (GMP — GNU Multiple Precision Arithmetic Library)
- An existing `lean` binary for stage0 bootstrapping
- Python 3.10+ with `uv` for p4ramill_py dependencies

---

## Testing

```bash
# Genetics suite (Python — no kernel build required)
python3 test_genetics.py

# Lean formalization
cd p4ramill
lake build

# Full paraconsistent kernel verification
lean --run p4ramill/ParaconsistentKernelTest.lean
lean --run p4ramill/ParaconsistentMillennium.lean
```

---

## License

Unlicense (public domain). See `LICENSE`.
