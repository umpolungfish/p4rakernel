# A One-Shot Topological Readout of the Modular Period — crystal

The readout runs. Nothing here refers to another manuscript.

## Booting

The instantiation is part of the mOMonadOS bare-metal kernel
(`https://github.com/umpolungfish/momonad_os`) at the commit in `MANIFEST.txt`.
Build for `x86_64-unknown-none` and run:

```
./run_serial_cmds.sh "oneshots"       # the readout, end to end
./run_serial_cmds.sh "fibqc verify"   # the anyon algebra it stands on
./run_serial_cmds.sh "bi 1 2 1"       # the braid image of a word
```

## Claim to verb

| Paper claim | Where it runs | What it prints |
|---|---|---|
| the modular period is a winding number, read in one shot | `oneshots` #1 | `ord_N(a) = r via winding_order`, a=7, N=15, r=4 |
| the Jones-invariant phase of a modular-exponentiation braid carries it | `oneshots` #7 | winding 137/250, residual, period 4 |
| that phase is off the tenths lattice | `oneshots` #7, #8 | `off_lattice=true`, so no finite braid word lands on it exactly |
| the off-lattice phase is the floor, not a compiler artifact | `oneshots` #8 | the floor named as the phase's own property |
| the period recovers a factorization | `oneshots` #9 | N=15, a=4, r=2, 3x5=15 |
| the underlying anyon algebra is consistent | `fibqc verify` | 22 items, each PASS or named |

Each one-shot prints its own inputs alongside its answer, so the readout can be
re-run at other a and N rather than taken on the printed case alone.
