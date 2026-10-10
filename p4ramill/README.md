# p4ramill

p4ramill is the Lean formalization of the Imscribing Grammar on the modified
p4rakernel. It combines the twelve-primitive Crystal, Belnap FOUR and
SIXTEEN_3, executable lattice programs, arithmetic transport, and
Witness/Closure readings of mathematical objects.

The executable re-entry interface compiles S/K/I programs over the native
carrier into complete value tables with reduction witnesses. The native solver
computes candidate fixed points, and Lean certificates establish their least
and greatest bounds, settled feedback traces, and enclosure of every fixed
state. The corpus also supplies domain constructions and typed transport interfaces.

## Select the fork and check a focused target

```sh
cd /home/mrnob0dy666/imsgct/p4rakernel/p4ramill
export PATH="$PWD/../build/stage1/bin:$PATH"
lake env lean --version
```

Compile the executable re-entry modules in dependency order, using one worker
and one compiler process at a time. These commands use the existing project dependencies:

```sh
for module in TemporalSemantics CombinatoryReentry CombinatoryFixedPoint \
  TrilatticePrograms CombinatoryFixedPointBounds; do
  lake env lean -j1 "Imscribing/Paraconsistent/$module.lean" \
    -o ".lake/build/lib/lean/Imscribing/Paraconsistent/$module.olean" || exit "$?"
done
```

Then execute the audit modules sequentially:

```sh
for module in TemporalSemanticsAudit CombinatoryReentryAudit \
  CombinatoryFixedPointAudit TrilatticeProgramsAudit \
  CombinatoryFixedPointBoundsAudit; do
  lake env lean -j1 "Imscribing/Paraconsistent/$module.lean" || exit "$?"
done
```

The default `lake build` target is the full `Imscribing` library. Use the focused
checks above for re-entry work and run builds separately from quantum membrane workloads.

## Try a held value or a composed program

```lean
import Imscribing.Paraconsistent.CombinatoryFixedPointBounds

open Imscribing.Paraconsistent.CombinatoryReentry
open Imscribing.Paraconsistent.CombinatoryFixedPoint
open Imscribing.Paraconsistent.CombinatoryFixedPointBounds
open Imscribing.Paraconsistent.TrilatticePrograms
open Imscribing.Paraconsistent.Temporal.Semantics

-- Retained singleton T settles at the subset containing T and F.
#eval (solveProgram 32 (seededOperator (FDE.singleton .T))).map (·.point)

-- Retention after injection: endpoints are empty and the T/F frame.
#eval (solveBounds 4 (retainAfterInject
  (Lean.Sixteen3.ofMask 6) (FDE.singleton .B))).map
  fun bounds => (bounds.lower.point, bounds.upper.point)

-- Injection after retention: endpoints are B and the T/F/B subset.
#eval (solveBounds 4 (injectAfterRetain
  (Lean.Sixteen3.ofMask 6) (FDE.singleton .B))).map
  fun bounds => (bounds.lower.point, bounds.upper.point)
```

`solveProgram` returns a least-point certificate. `solveGreatest` returns a
greatest-point certificate. `solveBounds` compiles one table and returns both
certificates for that table. Their feedback signals start at empty and full;
each is proved settled from tick four onward. The original program has a
certified data reduction at either endpoint.

`Bounds.encloses_fixed` proves every fixed state lies between those endpoints.
`Bounds.unique_of_equal` certifies uniqueness when they agree. `Bounds.contains`
tests the interval and `Bounds.isFixed` tests the actual map equation. Raw
negation has empty/full bounds, while singleton T continues to move to singleton F.

Lifted FOUR negation exchanges T/F memberships. The information complement
used to compute the greatest point toggles all four memberships. Singleton B
and the T/F subset remain distinct native states throughout these interfaces.

## Where to look

| Directory or module | Contents |
|---|---|
| `Imscribing/Primitives/` | Grammar coordinates, Crystal, catalog, tiers |
| `Imscribing/Paraconsistent/TemporalSemantics.lean` | Held negation closure, two-tick signals, retained-seed feedback |
| `Imscribing/Paraconsistent/CombinatoryReentry.lean` | S/K/I, Y conversion, abstraction, contraction witnesses, resumable execution |
| `Imscribing/Paraconsistent/TrilatticePrograms.lean` | Six native operations, seeded and diagonal maps, injection/retention composition |
| `Imscribing/Paraconsistent/CombinatoryFixedPoint.lean` | Certified tables and least information fixed points |
| `Imscribing/Paraconsistent/CombinatoryFixedPointBounds.lean` | Greatest points, endpoint bounds, enclosure and uniqueness |
| `Imscribing/Paraconsistent/` | Belnap FOUR, SIXTEEN_3, Frobenius, Witness values |
| `Imscribing/IUTT.lean` | Packets, state decomposition, transport, Closure laws |
| `Imscribing/ABC*.lean` | Arithmetic calibration, measurements, Θ transport |
| `Imscribing/Millennium/` | Conjecture statements, SIC constructions, native bridges |
| `Imscribing/Classical/` | Combinatorial and number-theoretic results |
| `Imscribing/NS_*.lean` | Re-entry carrier, differential injection, residual continuation |
| `ParaconsistentMillennium.lean` | Aggregate entry point |
| `lakefile.toml` | Module registration |

## Witness and transport

The active conjecture modules share the interface

```text
native datum → calibrated packet → ambient state
             → Witness → Θ transport → Closure
```

Current bridges include ABC, BSD, RH, Hodge, Navier–Stokes, Yang–Mills,
Goldbach, and OPN. Finite, conditional, and supplied project channels record
their mathematical scope in their types.

`Verdict P : Type` retains its constructor tag. `proved`, `refuted`, `held`, and
`admitted` are distinct values; `held` carries `P` and an independent second
reading and classifies as Belnap B. `IUTT.State` retains the larger trilattice
ambient and its truth, falsity, and information lanes.

## Read the checks and the documentation

Audit modules print axiom dependencies and execute concrete controls. The
bounds audit checks seeded maps, diagonals, constants, Y-computed constants,
retained negation, and both composition orders. It rejects non-greatest and
non-fixed candidates and insufficient reduction fuel. Earlier least-point and
trilattice audits also pass with the shared table helpers. Records are retained in
[`../measurements/temporal_reentry_20261010/`](../measurements/temporal_reentry_20261010/).

Compiler output identifies declarations that use axioms or `sorry`. Those
dependencies belong to each theorem statement and audit. Endpoint enclosure,
uniqueness, greatest-point program reduction, and settled feedback theorems
print no axiom dependencies.

The [kernel README](../README.md) explains native declarations and mode
boundaries. The [implementation guide](../../ig-docs/trilattice_reentry_kernel.md)
develops the carrier, executable calculus, solver, and bounds, with a
[rendered PDF](../../ig-docs/trilattice_reentry_kernel.pdf). The historical
inventory and domain theorem details remain in [`README_FULL.md`](README_FULL.md).

## License

Unlicense (public domain).
