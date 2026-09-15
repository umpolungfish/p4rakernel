# p4ramill

Lean 4 formalization of the Imscribing Grammar in the paraconsistent kernel.
The library combines the twelve-primitive Crystal, Belnap/SIXTEEN₃ logic,
IUTT packets and transport, and Witness/Closure readings of mathematical
objects.

## Build

```bash
cd /home/mrnob0dy666/imsgct/p4rakernel/p4ramill
export PATH="$PWD/../build/stage1/bin:$PATH"
lake build
```

The default library target is `Imscribing`. Individual modules can be checked
quickly with, for example:

```bash
lake build Imscribing.ABC_ThetaTransport
lake build Imscribing.Millennium.Goldbach_ABC_ThetaBridge
```

## Where to look

| Directory/file | Contents |
|---|---|
| `Imscribing/Primitives/` | Grammar coordinates, Crystal, catalog, tiers |
| `Imscribing/Paraconsistent/` | Belnap FOUR, SIXTEEN₃, Frobenius, Witness values |
| `Imscribing/IUTT.lean` | packets, state decomposition, transport, Closure laws |
| `Imscribing/ABC*.lean` | arithmetic calibration, measurements, Θ transport |
| `Imscribing/Millennium/` | conjecture statements and native bridges |
| `Imscribing/Classical/` | combinatorial and number-theoretic results |
| `ParaconsistentMillennium.lean` | aggregate entry point |
| `lakefile.toml` | module registration |

## The bridge pattern

The active conjecture modules use one common shape:

```text
native datum → calibrated packet → ambient state
             → Witness → Θ transport → Closure
```

Current bridges include ABC, BSD, RH, Hodge, Navier–Stokes, Yang–Mills,
Goldbach, and OPN. A bridge may be finite, conditional, or supplied by an
existing project channel. It records that scope in its types instead of
pretending that an open universal statement has become a conventional proof.

## Reading the logic

`Verdict P : Type` retains a constructor tag. `proved`, `refuted`, `held`, and
`admitted` are distinct values; `held` carries `P` and an independent second
reading and classifies as Belnap `B`. This is the value-level Witness used by
the bridge modules. `IUTT.State` retains the larger trilattice ambient and its
truth, falsity, and information lanes.

## Verification expectations

`lake build` is the formal interface check. Warnings about axioms or `sorry`
identify declared mathematical boundaries and should be read, not hidden.
The full historical inventory, architecture notes, and theorem details are
preserved in [`README_FULL.md`](README_FULL.md).

## License

Unlicense (public domain).
