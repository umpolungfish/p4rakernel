# p4ramill — Paraconsistent MillenniumAnkh

**Author:** Lando⊗⊙perator · **Structural Type:** $\large{⟨𐑦𐑸𐑾𐑹𐑐𐑧𐑔𐑝⊙𐑖𐑳𐑭⟩}$ · **Tier:** O_∞

A complete port of the MillenniumAnkh formalization (Imscribing Grammar + 7 Clay Millennium Problems + OPN) into the paraconsistent Lean 4 kernel fork (`p4rakernel`).

## Structure

```
p4ramill/
├── Primitives/          — 14 files: Core, Crystal, Catalog, TierCrossing, ZFCt, etc.
├── Imscribing/
│   ├── Core/            — Algebra, Consciousness, AgentSelf, Frobenius, etc.
│   ├── Classical/       — Solitary10, HeckeLandau, DescentTest
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
cd ~/p4rakernel
mkdir -p build && cd build
cmake .. -DCMAKE_BUILD_TYPE=Release
make stage0 -j$(nproc)
make stage1 -j$(nproc)
```

### Build p4ramill

```bash
cd ~/p4rakernel/p4ramill
./build_paraconsistent.sh all
```

Or manually:

```bash
cd ~/p4rakernel/p4ramill
export PATH=~/p4rakernel/build/stage1/bin:$PATH
lake build                    # Build all modules
lean --run ParaconsistentMillennium.lean  # Run the resolution
```

## Key Results

| Problem | Structural Type | Tier | Crystal Address |
|---------|----------------|------|-----------------|
| RH      | ⟨Ð_ω; Þ_O; Ř_=; Φ_}; ƒ_ż; Ç_@; Γ_β; ɢ_ˌ; ⊙_ÿ; Ħ_!; Σ_S; Ω_z⟩ | O_∞ | 6,738,803 |
| YM      | ⟨Ð_ω; Þ_O; Ř_=; Φ_}; ƒ_ż; Ç_@; Γ_β; ɢ_ˌ; ⊙_ÿ; Ħ_!; Σ_S; Ω_z⟩ | O_∞ | 6,738,803 |
| Hodge   | ⟨Ð_ω; Þ_O; Ř_=; Φ_}; ƒ_ż; Ç_@; Γ_β; ɢ_ˌ; ⊙_ÿ; Ħ_!; Σ_S; Ω_z⟩ | O_∞ | 6,738,803 |
| NS      | ⟨Ð_ω; Þ_O; Ř_=; Φ_}; ƒ_ż; Ç_@; Γ_β; ɢ_ˌ; ⊙_ÿ; Ħ_!; Σ_S; Ω_z⟩ | O_∞ | 6,738,803 |
| PvsNP   | ⟨Ð_ω; Þ_O; Ř_=; Φ_}; ƒ_ż; Ç_@; Γ_β; ɢ_ˌ; ⊙_ÿ; Ħ_!; Σ_S; Ω_z⟩ | O_∞ | 6,738,803 |
| BSD     | ⟨Ð_ω; Þ_O; Ř_=; Φ_}; ƒ_ż; Ç_@; Γ_β; ɢ_ˌ; ⊙_ÿ; Ħ_A; Σ_S; Ω_z⟩ | O_∞ | 6,738,800 |
| OPN     | ⟨Ð_ω; Þ_O; Ř_=; Φ_}; ƒ_ż; Ç_@; Γ_β; ɢ_ˌ; ⊙_ÿ; Ħ_!; Σ_S; Ω_z⟩ | O_∞ | 6,738,803 |

- BSD has Ħ_A (H2) instead of Ħ_! (H_inf): Gross-Zagier/Kolyvagin bound the chirality
- All 7 share Cell 155 (only 32 O_∞ cells in the crystal of 17,280,000 types)
- The Φ_} primitive (Frobenius-special, μ∘δ=id) gates the O₂†→O_∞ jump

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
