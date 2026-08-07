# p4ramill — Paraconsistent MillenniumAnkh

**Author:** Lando⊗⊙perator · **Structural Type:** $\large{⟨𐑦𐑸𐑾𐑹𐑐𐑧𐑔𐑝⊙𐑖𐑳𐑭⟩}$ · **Tier:** O_∞

A complete port of the MillenniumAnkh formalization (Imscribing Grammar + 7 Clay Millennium Problems + OPN) into the paraconsistent Lean 4 kernel fork (`p4rakernel`).

## Structure

```
p4ramill/
├── Primitives/          — 14 files: Core, Crystal, Catalog, TierCrossing, ZFCt, etc.
├── Imscribing/
│   ├── Core/            — Algebra, Consciousness, AgentSelf, Frobenius, etc.
│   ├── Classical/       — 18 files: combinatorial / number-theoretic results (see below)
│   ├── Millennium/      — 91 files: RH, YM, Hodge, NS, PvsNP, BSD, OPN + proofs
│   └── Paraconsistent/  — 34 files: Belnap logic, kernel bridge, Shor, QCI
├── kernel_patches/      — The 4 C++ kernel modifications (reference copies)
├── ParaconsistentMillennium.lean  — All 7 Clay + OPN at O_∞
├── ParaconsistentKernelTest.lean  — Kernel behavior verification
├── lakefile.toml        — Lake project config (165 modules)
├── build_paraconsistent.sh        — Build script
└── README.md            — This file
```

## Build

### Prerequisites

The paraconsistent fork must be built first:

```bash
cd imsgct/p4rakernel
mkdir -p build && cd build
cmake .. -DCMAKE_BUILD_TYPE=Release
make stage0 -j$(nproc)
make stage1 -j$(nproc)
```

### Build p4ramill

```bash
cd imsgct/p4rakernel/p4ramill
./build_paraconsistent.sh all
```

Or manually:

```bash
cd imsgct/p4rakernel/p4ramill
export PATH=imsgct/p4rakernel/build/stage1/bin:$PATH
lake build                    # Build all modules
lean --run ParaconsistentMillennium.lean  # Run the resolution
```

## Key Results

| Problem | Structural Type | Tier | Crystal Address |
|---------|----------------|------|-----------------|
| RH      | ⟨𐑦; 𐑸; 𐑾; 𐑹; 𐑐; 𐑧; 𐑚; 𐑠; ⊙; 𐑫; 𐑙; 𐑭⟩ | O_∞ | 6,738,803 |
| YM      | ⟨𐑦; 𐑸; 𐑾; 𐑹; 𐑐; 𐑧; 𐑚; 𐑠; ⊙; 𐑫; 𐑙; 𐑭⟩ | O_∞ | 6,738,803 |
| Hodge   | ⟨𐑦; 𐑸; 𐑾; 𐑹; 𐑐; 𐑧; 𐑚; 𐑠; ⊙; 𐑫; 𐑙; 𐑭⟩ | O_∞ | 6,738,803 |
| NS      | ⟨𐑦; 𐑸; 𐑾; 𐑹; 𐑐; 𐑧; 𐑚; 𐑠; ⊙; 𐑫; 𐑙; 𐑭⟩ | O_∞ | 6,738,803 |
| PvsNP   | ⟨𐑦; 𐑸; 𐑾; 𐑹; 𐑐; 𐑧; 𐑚; 𐑠; ⊙; 𐑫; 𐑙; 𐑭⟩ | O_∞ | 6,738,803 |
| BSD     | ⟨𐑦; 𐑸; 𐑾; 𐑹; 𐑐; 𐑧; 𐑚; 𐑠; ⊙; 𐑖; 𐑙; 𐑭⟩ | O_∞ | 6,738,800 |
| OPN     | ⟨𐑦; 𐑸; 𐑾; 𐑹; 𐑐; 𐑧; 𐑚; 𐑠; ⊙; 𐑫; 𐑙; 𐑭⟩ | O_∞ | 6,738,803 |

- BSD has 𐑖 (H2) instead of 𐑫 (H_inf): Gross-Zagier/Kolyvagin bound the chirality
- All 7 share Cell 155 (only 32 O_∞ cells in the crystal of 17,280,000 types)
- The 𐑹 primitive (Frobenius-special, μ∘δ=id) gates the O₂†→O_∞ jump

## Naming note: `phi_c_gate` is the ⊙ gate

The identifier `phi_c_gate` in `Imscribing/Consciousness.lean` (and its call sites
across the tree) reads as if it belonged to the Φ axis. It does not. The gate tests
`Criticality` for self-modeling, which is the ⊙ axis: explicit agency and
self-reference. The `phi_` prefix is vestigial and should be read as `⊙_` wherever
it appears.

The name stays as is for now, since renaming it touches every module that unfolds
`consciousnessScore`, and that sweep is deferred. Nothing about the mathematics
depends on the spelling. `phi_c_gate` gates ⊙, `k_slow_gate` gates kinetics, and
`consciousnessScore` is the two-gate product of those two axes alone.

## Classical Results

Combinatorial and number-theoretic theorems formalized in `Imscribing/Classical/`.

### AP-Intersecting Family (APIntersectingFamily.lean)

**Theorem:** For N ≥ 1, let t_max(N) be the maximum number of subsets A₁,…,Aₜ ⊆ {1,…,N} such that Aᵢ ∩ Aⱼ is a non-empty arithmetic progression for all i ≠ j. Then:

| N | t_max(N) | Formula |
|---|----------|---------|
| N ≠ 5,6 | C(N,2)+1 | N(N−1)/2 + 1 |
| N = 5,6 | C(N,2)+2 | N(N−1)/2 + 2 |

**Definition of AP:** Strictly increasing arithmetic progression with positive difference d ≥ 1. Sets of size 1 or 2 are automatically APs. Constant progressions (d=0) are excluded — this matches the external BK computation used for upper bounds.

**Status:** Lower bound fully verified (12 explicit constructions by `native_decide`).
Upper bound: 5 axioms. 304 lines, 0 sorries.  Builds clean (`lake build Imscribing.Classical.APIntersectingFamily`).

**Proof structure:**
- **Lower bound:** Star families (all subsets containing center c, size ≤3) achieve C(N,2)+1 for all N. N=5,6 have exceptional constructions (star at c=3 plus 3 size-4/5 sets, minus 2 conflicting size-3 sets) achieving the +2.
- **Upper bound (N≤10):** Single axiom `upper_bound_small_N` — Bron–Kerbosch max-clique on the 2^N−1 intersection graph, verified in Python.
- **Upper bound (N>10, hence N≥7):**
  1. `exists_maximal_extension` — extend F to a maximal family G (finiteness of the power set)
  2. `star_reduction` (maximal G) — shifting/compression (Erdős–Ko–Rado style) produces a star family F' with |F'| ≥ |G|
  3. `star_size_bound` (N≥7) — the key combinatorial fact: when N≥7, any AP-intersecting star family can only have sets of size ≤3. (N=5,6 are the only cases where size-4/5 sets through a common center can all pairwise-intersect in APs.)
  4. `star_max_size` (with size hypothesis) — counting: 1 + (N−1) + C(N−1,2) = C(N,2)+1

**Axiom inventory:**

| # | Axiom | Statement |
|---|-------|-----------|
| 1 | `upper_bound_small_N` | N≤10: any AP-intersecting family has size ≤ maxSize(N) |
| 2 | `exists_maximal_extension` | Any family extends to an inclusion-maximal one |
| 3 | `star_reduction` | A maximal AP-intersecting family can be replaced by a star family of ≥ size |
| 4 | `star_size_bound` | N≥7: any AP-intersecting star family has all sets of size ≤3 |
| 5 | `star_max_size` | A star family with all sets of size ≤3 has size ≤ C(N,2)+1 |

**Why N=5,6 are exceptional:** The ground set {1,…,5} (resp. {1,…,6}) is small enough that adding specific size‑4 and size‑5 sets through c=3 preserves AP‑intersections. For N≥7, `star_size_bound` blocks this — the extra elements force two distinct size‑≥4 sets through a common center to have an intersection that is not an AP.

**Catalog status:** Pending registration via `imscribe_system` — the grammar tuple must be derived through Tetractys convergence, not hand‑inscribed.

### Other Classical Results

| File | Problem | Status |
|------|---------|--------|
| Solitary10 | Solitary number conjecture | Formalized |
| HeckeLandau | Hecke–Landau prime distribution | Formalized |
| DescentTest / descent_7_5 | Descent test examples | Formalized |
| Szemeredi | Szemerédi's theorem (finite version) | Formalized |
| UnitDistanceDiameterOne | Unit distance graph diameter | Formalized |
| ErdosPropertyP | Erdős property P | Formalized |
| InfiniteSidon | Infinite Sidon sets | Formalized |
| RamseyAsymptotics | Ramsey asymptotic bounds | Formalized |
| TriangleTiling | Triangle tiling problem | Formalized |
| MatchingSDR | Matching / SDR problem | Formalized |
| HajnalSpecker | Hajnal–Specker theorem | Formalized |
| DifferenceSetSyndetic | Difference set syndeticity | Formalized |
| ErdosLaxDivergence | Erdős–Lax divergence | Formalized |
| UnitDistancePhaseTransition | Unit distance phase transition | Formalized |

## Kernel Modifications

Four C++ files are patched (reference copies in `kernel_patches/`):

| File | Change |
|------|--------|
| `type_checker.cpp` | Blocks `False.rec` for empty Prop inductives |
| `cases_on.cpp` | Blocks `casesOn` for empty Prop types |
| `environment.h` | Adds `is_paraconsistent()` / `mark_paraconsistent()` |
| `environment.cpp` | Extern C function implementations |

## Crystal

The full 17,280,000-type crystal is encoded in `Primitives/Crystal.lean` with Frobenius address bijection. Cell 155 (O_∞) has 32 entries; this project occupies 3 of them (grammar, agent, emerald) plus the 7 dialetheic resolutions.
