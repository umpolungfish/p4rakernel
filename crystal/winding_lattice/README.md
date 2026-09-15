# Windings: the Phase Lattice of the Fibonacci Anyon Model — crystal

Boot the kernel and the paper's claims print themselves. Nothing here refers to
another manuscript.

## Booting

The instantiation is part of the mOMonadOS bare-metal kernel
(`https://github.com/umpolungfish/momonad_os`) at the commit in `MANIFEST.txt`.
Build for `x86_64-unknown-none` and run:

```
./run_serial_cmds.sh "fibqc verify"      # the whole algebra, item by item
./run_serial_cmds.sh "fibqc algebra"     # F, R, and the derived constants
./run_serial_cmds.sh "bi 1 2 1"          # a braid word and its image
```

## Claim to verb

| Paper claim | Where it runs | What it prints |
|---|---|---|
| every phase native to the model is a multiple of a tenth of a winding | `fibqc verify` | `Phase lattice = tenths of a winding: PASS` |
| the model's constants follow from the golden ratio | `fibqc verify` | `Constants derivable from PHI: PASS` |
| F is unitary and satisfies the pentagon | `fibqc verify` | `F unitary`, `Pentagon form (F^2=I, anti-diag, a^2+b^2=1)` |
| the braid relation holds | `fibqc verify` | `Braid relation (Y-B): PASS`, `Braid Artin B_n<=8: PASS` |
| spin-statistics and the S matrix | `fibqc verify` | `Spin-statistics`, `S unitary`, `S^2=I` |
| the TQFT data is consistent | `fibqc verify` | `TQFT identities`, `Verlinde formula` |
| a braid word's image in the representation | `bi <generators>` | the matrix, and the winding it carries |

Each line prints PASS or names the item that failed. The check is the kernel's
own; it runs at boot as well as on demand.
