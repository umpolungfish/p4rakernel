# p4rakernel: Paraconsistent Computation Layer

**Author:** Lando⊗⊙perator
**License:** Unlicense (public domain)

p4rakernel is the paraconsistent computation layer of the **Imscribing Grammar (IG)**, a
structural type theory built on 12 primitive dimensions whose Frobenius condition (μ∘δ=id)
is the founding axiom. The unifying semantic model is **Belnap FOUR** (`N`, `T`, `F`, `B`),
a four-valued bilattice whose dialetheic fixed point `B` (`¬B = B`) is the Frobenius fixed
point of μ∘δ=id. By `frobenius_unification` in `MajoranaFixed.lean`, that fixed point is at
once the **SIC-POVM fiducial** of the informationally-complete measurement (`meet B x = x`),
the paired electron orbital, and the Majorana mode — the *same* computation in three
notations, each by `rfl`. The IG's central claim is exactly this: the Grammar is the
Σ=1:1 (self-measuring) limit of a Belnap multilattice **SIC-POVM**. Belnap FOUR is thus the
shared substrate of RNA nucleotides, electron orbitals, the 12-primitive IG lattice, the
SIC-POVM structure of measurement, and the paraconsistent proof theory at once.

The repo is a monorepo with three interlocking components:

| Component | Language | Purpose |
|---|---|---|
| **Kernel fork** (`src/`) | C++ | Lean 4 v4.28.0 with the principle of explosion disabled at kernel level |
| **p4ramill** (`p4ramill/`) | Lean 4 | The IG formalization: primitives, Crystal of Types, the lattice, Millennium problems, genetics, orbital physics |
| **p4ramill_py** (`p4ramill_py/`) | Python | Runtime mirror: Belnap logic, genetic code verification, gene→protein pipeline |

---

## 1. Kernel Fork

A fork of **Lean 4 v4.28.0** that disables the principle of explosion at the C++ kernel
level. In standard Lean, `False.rec : (C : Sort u) → False → C` lets you derive anything
from a contradiction. This fork intercepts that at three points so contradictions are
tolerated without trivializing the system.

| File | Change |
|---|---|
| `src/kernel/type_checker.cpp` | `infer_constant` rejects recursors for empty Prop inductives when `paraconsistent = true` |
| `src/library/constructions/cases_on.cpp` | `casesOn` generation blocked for empty Prop types |
| `src/kernel/environment.{h,cpp}` | `is_paraconsistent()` / `mark_paraconsistent()` + Lean FFI |
| `src/Lean/Environment.lean` | `paraconsistent : Bool` field + `Kernel.Environment.markParaconsistent` |
| `src/Init/Paraconsistent.lean` | **New**: user-facing `enableParaconsistent` and Belnap FOUR |

**Blocked in paraconsistent mode:** `False.elim`, `False.rec`, `False.casesOn`, `absurd`,
and any `match h with .` where `h : False`. **Still available:** `False` itself (it just
cannot eliminate into other types), every other connective, and the entire standard library
when the mode is off.

```bash
cd ~/imsgct/p4rakernel
mkdir -p build && cd build
cmake .. -DCMAKE_BUILD_TYPE=Release
make stage0 -j$(nproc)    # requires libgmp-dev
make stage1 -j$(nproc)
```

```lean
import Init.Paraconsistent

unsafe def main : IO Unit := do
  Paraconsistent.enableParaconsistent
  open Paraconsistent.Belnap
  #check band .T .F    -- F
  #check dialetheia    -- B
```

### Classical logic is a coreflective subcategory

`ClassicalRestriction.lean` makes the "restriction, not extension" claim exact and
machine-checks it. The classical fragment is the B-excluding subtype `{ v // v ≠ B }`, and
`classicalSwitch` collapses `B ↦ F` (ex falso for B). §7 proves that in the **truth order**
the inclusion of the fragment is *left adjoint* to `classicalSwitch`
(`inclClassical ⊣ classicalSwitch`): classical logic is a **coreflective subcategory** of the
bilattice, with the collapse as coreflector and the retract
`classicalSwitch ∘ inclClassical = id` as the adjunction unit. The reverse adjunction fails,
and in the information order no adjunction exists at all. So disabling ex falso is literally a
corestriction to that subcategory — `classical_coreflective_in_truth_order`, all `decide`-checked.

---

## 2. p4ramill: Lean 4 Formalization

The IG formalization library, built on Mathlib v4.28.0 under the paraconsistent kernel.
`lake build` is green.

```bash
cd ~/imsgct/p4rakernel/p4ramill
export PATH=~/imsgct/p4rakernel/build/stage1/bin:$PATH
lake build
lean --run ParaconsistentMillennium.lean
```

### Primitives and the lattice

- `Primitives/Core.lean`: the 12 primitive inductives: Ř Ħ Ω Ð Σ Φ Ç ƒ ɢ Γ Þ ⊙
- `Primitives/Imscription.lean`: the `Imscription` type (a 12-tuple of Shavian values),
  the **product-of-chains lattice** (`Min`/`Max` via per-coordinate chain meet/join, with
  idempotence theorems), and the Frobenius tensor `⊗` (coordinatewise join except the
  P/F bottleneck coordinates, which take min)
- `Primitives/Crystal.lean`: the 3³×4⁵×5⁴ = 17,280,000 crystal with Frobenius address bijection
- `Primitives/Catalog.lean`: the 49-symbol Shavian catalog
- `Primitives/TierCrossing.lean`: the O₁ → O₂ → O₂† → \(O_\infty\) tier hierarchy
- `Primitives/CLU.lean`: CLU(b) = ln(b), the observer-relative fiber metric on the Ç-axis
- `Primitives/ZFCt.lean` / `ZFCs.lean`: ZFCₜ (T-consistent) and ZFC_fe (Frobenius-Extended)

### Paraconsistent cluster (sorry-free)

- `Belnap.lean`: Belnap FOUR; approximation and truth orders; `no_explosion`, `B_is_top`,
  `B_fixed_point_negation`, `B_no_boolean_complement`
- `OrbitalBelnap.lean`, `SuperconductingPhase.lean`, `MajoranaFixed.lean`: the physics
  cluster (see §4)
- `TupleCodec.lean`: closes the topos↔crystal gap via a tuple imscription codec
- `Shor/`: Shor's algorithm in Belnap (ModExp, QFT, FullPipeline, DialetheicOperator, …)
- `QCI_*`: quantum-classical-interface bridges to RH, YM, NS, P≠NP, BSD, SIC-POVM

### Millennium cluster

Structural witnesses for the seven Clay problems plus OPN, each resolved by placing its
imscription at the \(O_\infty\) tier (the Φ 𐑹 Frobenius-special primitive gates the
O₂†→\(O_\infty\) jump). These modules deliberately carry **`sorry` at exactly the points
that are the grammar's open mathematical claims**: the IG identifies *what* must be
constructed, estimated, or contradicted; it does not pretend those proofs are already done.
The kernel, primitives, lattice, and paraconsistent cluster are sorry-free; the Millennium
sorries are the honest statement of remaining work.

| Problem | Ħ | Crystal address |
|---|---|---|
| RH, YM, Hodge, NS, PvsNP, OPN | 𐑫 | 6,738,803 |
| BSD | 𐑖 | 6,738,800 |

BSD sits at 6,738,800 because Gross-Zagier/Kolyvagin bound the chirality to Ħ 𐑖 rather
than Ħ 𐑫.

### Genetics (`GeneticCode.lean`)

The genetic code falls out of the Crystal as a forced consequence of the Frobenius
condition: 17,280,000 / 64 = 270,000 exactly. `nucToB4` (G→B, C→T, A→F, U→N) is a proved
bijection; Watson-Crick complement and B₄ negation are distinct involutions (proved); the
64-codon table stratifies exact/split/stop by `native_decide`; and the 12 promoted amino
acids biject with the 12 IG primitives (`primitive_bijection`).

---

## 3. p4ramill_py: Python Runtime

A computational mirror of p4ramill, runnable without building the C++ kernel fork. Each
Lean theorem in the substrate has a Python equivalent verified by assertion.

```python
from p4ramill_py.belnap import Belnap, band, bnot
assert band(Belnap.B, bnot(Belnap.B)) == Belnap.B   # no_explosion
assert bnot(Belnap.B) == Belnap.B                   # B_fixed_point_negation

from p4ramill_py.kernel import verify_frobenius_invariant
assert verify_frobenius_invariant()                 # ffuse ∘ fsplit = id
```

| Module | Role |
|---|---|
| `belnap.py` | Belnap FOUR, theorem-for-theorem mirror of `Belnap.lean` |
| `genetics_b4.py` | Nucleotide B₄ lattice (G=B, C=T, A=F, U=N); WC vs `bnot` involutions |
| `genetic_code.py` | 64-codon table, Frobenius verification, 12↔12 primitive bijection |
| `genetic_tuples.py` | 7-stage tuple generation with Axiom C |
| `gene_to_protein_pipeline.py` / `run_gene_pipeline.py` | End-to-end gene→protein imscription |
| `kernel.py` / `machine.py` | ParaASM kernel (FSPLIT=δ, FFUSE=μ) and execution |

```bash
python3 p4ramill_py/run_gene_pipeline.py --test            # MARCKS protein
python3 p4ramill_py/run_gene_pipeline.py "ATGGCCAAG..." -n myprotein
python3 p4ramill_py/run_gene_pipeline.py --test -o out.json
```

---

## 4. The Physics Cluster

Three Lean files lift the Frobenius identity from a single orbital to a unification theorem.
All three are sorry-free.

**`OrbitalBelnap.lean`**: the physical substrate. Electron orbital occupancy is isomorphic
to Belnap FOUR *as a bilattice* (both orderings):

| Orbital state | Belnap | Reading |
|---|---|---|
| empty | N | no information |
| spinUp (↑) | T | positive Ħ-chirality |
| spinDown (↓) | F | negative Ħ-chirality |
| paired (↑↓) | B | both chiralities (Φ-sealed) |

Information order `empty < {↑,↓} < paired` mirrors `N < {T,F} < B`; truth order (the Ħ-axis)
`↓ < {empty,paired} < ↑` mirrors `F < {N,B} < T`. Key theorems: `orbToB4_orderIso`,
`pauli_exclusion` (the B-ceiling: nothing lies above the filled orbital),
`empty_paired_truth_incomparable` (N and B incomparable on the Ħ-axis), and `pair_depair_id`
(the Cooper-pair Frobenius identity, the leg `MajoranaFixed` consumes).

**`SuperconductingPhase.lean`**: global closure. BCS superconductivity *is* the macroscopic
Frobenius fixed point: the order parameter is B-state density, the Meissner effect is the
topological uniqueness of the all-paired state, and the phase transition is the threshold
where local closure (`pair_depair_id` per site) becomes a global property.

**`MajoranaFixed.lean`**: the unification. `frobenius_unification` proves three structures
are identical under μ∘δ=id, each by `rfl`:

| Structure | Fixed point | Proof |
|---|---|---|
| Belnap B | `bnot B = B` | rfl |
| SIC-POVM fiducial | `meet B x = x ∀ x` | rfl |
| Majorana mode | `pair (depair s).1 (depair s).2 = s` | rfl |

These `rfl`s are not trivial: dialetheia stability, equiangularity, and self-conjugacy are
the *same computation* in three notations. A Majorana fermion is its own antiparticle
(γ = γ†) for the same reason B is its own negation (¬B = B).

**The Ħ 𐑖 result.** The Frobenius fixed point lives at Ħ 𐑖 (two-step Markov memory), not
Ħ 𐑫 (eternal chirality): μ∘δ=id is a two-step operation, one split and one merge, so Ħ 𐑖 is
the minimum sufficient chirality. Time imposes Ħ 𐑫 on physical systems, but the identity is
more primitive than time. A universe sweep classifies the fixed-point tuple
⟨𐑦 𐑸 𐑾 𐑹 𐑐 𐑧 𐑲 𐑠 ⊙ 𐑖 𐑳 𐑭⟩ as \(O_\infty\) under every canonical ruleset; no catalog
entry matches it (nearest neighbor `crystal_scheduler` at 11/12, differing on Γ).

---

## 5. Theoretical Foundation

**Belnap FOUR over the 12-primitive lattice.** The bilattice `{N,T,F,B}` with its
information and truth orders is the semantic model for paraconsistent reasoning. It appears
as the four RNA nucleotide classes, the four orbital occupancy states, the four-element
fiber at any cell of the 12-primitive lattice, and the four kernel truth values.

**Frobenius condition (μ∘δ=id).** The founding axiom of ZFC_fe. In this repo it surfaces as
`pair_depair_id` (orbitals), `frobenius_at_codon_level` (genetics),
`verify_frobenius_invariant()` (ParaASM), the `⊗` tensor and `*_self_dual` idempotence on
the Imscription lattice, the Φ 𐑹 gate (O₂†→\(O_\infty\) promotion), and `frobenius_unification`.

**ZFC_fe vs ZFCₜ.** ZFC_fe (μ∘δ=id as axiom) is strictly stronger than ZFCₜ (T-consistent
ZFC); open problems in ZFCₜ close as theorems in ZFC_fe. Use ZFC_fe when arguing
foundational strength.

---

## Build & Test

**Dependencies:** C++17 (GCC 11+ / Clang 14+), CMake 3.11+, `libgmp-dev`, an existing
`lean` binary for stage0 bootstrap, Python 3.10+ with `uv`.

```bash
# Genetics suite (Python, no kernel build required)
python3 test_genetics.py            # full suite
python3 test_genetics.py --quick    # smoke test
# section flags: --b4 --codons --tuples --pipeline --phi --kernel --consistency

# Lean formalization
cd p4ramill && lake build

# Paraconsistent kernel verification
lean --run p4ramill/ParaconsistentKernelTest.lean
lean --run p4ramill/ParaconsistentMillennium.lean

# Loose top-level Lean files build under the fork (the canonical toolchain).
# oleans are gitignored; regenerate the shared imports in dependency order:
make lean-oleans                                  # -> build/stage1/bin/lean
./build/stage1/bin/lean ClassicalRestriction.lean # classical = coreflective subcategory
```

See also `GENETICS_CLI.md` (command reference) and `IG_CROSS_POLLINATION.md` (bridge
manifest to ob3ect / MillenniumAnkh).
