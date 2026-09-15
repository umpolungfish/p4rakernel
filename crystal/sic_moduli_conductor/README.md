# The Conductor of the SIC-POVM Moduli Field — crystal

Everything the paper claims, in a form you can boot and follow. Nothing here
cites another manuscript; every claim below resolves to a Lean module in this
repository or a kernel verb you can run.

## What is in here

| Path | What it carries |
|---|---|
| `momonados/d2048_exact_sic.rs` | the instantiation: the Stark unit, the S-unit monomial, the Gauss-sum levels, the representation cost, and the Welch check |
| `d12_psi_uhi.pkl` | the recovered d=12 SIC fiducial the Welch check runs on |
| `../../p4ramill/Imscribing/Millennium/SIC_D2048_Moduli.lean` | the tower: every ray class degree, computed, zero axioms and zero sorries |
| `../../p4ramill/Imscribing/Millennium/SIC_Moduli_Report.lean` | the per-dimension report |
| `../../verify_sic_moduli.sh` | elaborates the modules and prints what was checked per dimension |

## Booting it

The instantiation is a module of the mOMonadOS bare-metal kernel
(`https://github.com/umpolungfish/momonad_os`), at the commit named in
`MANIFEST.txt`. Drop `momonados/d2048_exact_sic.rs` into that kernel's `src/`,
wire the verbs listed below into the `d2048` dispatch, and build for
`x86_64-unknown-none`. Then:

```
./run_serial_cmds.sh "d2048 exact"        # unit, monomial, levels
./run_serial_cmds.sh "d2048 scaling"      # what the representation costs
./run_serial_cmds.sh "d2048 crossover"    # the threshold with its gate model exposed
./run_serial_cmds.sh "d2048 welch"        # equiangularity, measured where a fiducial exists
./run_serial_cmds.sh "fibqc verify"       # the kernel's own verification surface
```

For the Lean side, `./verify_sic_moduli.sh` at the repository root elaborates
the modules through the kernel and prints, dimension by dimension across
d = 2, 4, 8, 12, 16, 20, 2048, what was checked and the axiom dependency of each
headline theorem.

## Claim to verb

| Paper claim | Where it runs | What it prints |
|---|---|---|
| eps_d is a unit of norm 1; g_- and g_+ carry norms -(d-3) and d+1 | `d2048 exact` | the three elements with their norms |
| the monomial at exponents [-1,3,2] is exact | `d2048 exact` | the exact i128 triple and its norm |
| that monomial is 1/d - 2/d^3 + O(d^-4) | `d2048 exact` | monomial against 1/d and the gap |
| exactness is not evaluability | `d2048 exact` | the rationalized reading, correct to every digit shown |
| sqrt(m_d) from its four cyclotomic levels | `d2048 exact` | each Gauss sum, the radical, the component it came from, the product against sqrt(m_d) |
| the representation costs about 13*log2(d) bits | `d2048 scaling` | measured widths from d=16 to 2^20, refusing rows that exceed i128 |
| the crossover threshold depends on the gate model | `d2048 crossover` | four models, t_gate varied, largest reachable d at each |
| Welch saturation at d=12 | `d2048 welch` | all 143 overlaps, worst deviation |
| no fiducial at d=2048 | `d2048 welch` | says so, and why the two routes are closed |
| the tower, computed rather than asserted | `./verify_sic_moduli.sh` | every ray class degree, zero axioms |

## What is NOT here

There is no d=2048 fiducial. The paper determines the conductor; it does not
produce a vector. `d2048 welch` prints that distinction rather than computing
1/2049 from 2048 and presenting it as verification.
