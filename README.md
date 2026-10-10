# p4rakernel

p4rakernel is the Lean kernel and formalization layer of the **Imscribing
Grammar**. The modified kernel supplies the native SIXTEEN_3 carrier and
checked re-entry declarations. The `p4ramill` corpus builds executable lattice
programs, temporal signals, S/K/I combinators, fixed-point bounds, and certified cycles on
that carrier, alongside the Grammar's arithmetic and geometric constructions.

Re-entry makes a monotone carrier map available as a stored fixed value in
proofs and executable code. The combinator interface retains the computation
that produced each table entry and certifies both endpoints of the map's
fixed-state space. Feedback from an arbitrary starting state carries a certified
transient and primitive period. Its finite clock reads arbitrary ticks by phase
lookup. An experiment can follow individual contractions, resume feedback at a
chosen tick, or inspect fixed and oscillating memberships.

| Component | Role |
|---|---|
| [`src/`](src/) | Lean kernel fork, native trilattice operations, re-entry declarations, mode controls |
| [`p4ramill/`](p4ramill/README.md) | Lean corpus, executable combinators, certified fixed points, domain applications |
| [`tests/`](tests/) | Native carrier, declaration, mode, module, and execution controls |
| [`p4ramill_py/`](p4ramill_py/) | Runtime mirror and genetics pipeline |

## Use the local kernel

The built fork lives in `build/stage1/bin`. From the repository root, select it
before working in the corpus:

```sh
cd p4ramill
export PATH="$PWD/../build/stage1/bin:$PATH"
lake env lean --version
```

From the repository root, rebuild the kernel with its native CMake targets:

```sh
cmake -S . -B build -DCMAKE_BUILD_TYPE=Release
cmake --build build --target stage1 -j2
```

Run kernel builds, corpus checks, and quantum membrane workloads separately.
The focused corpus commands bound compiler concurrency and avoid launching the
full library build.

## The native carrier and its three orders

The implemented member of the ${SIXTEEN}_3$ family is

$$
\mathrm{SIXTEEN}_3=\mathcal P(\{N,T,F,B\}).
$$

Its independent memberships `hasN`, `hasT`, `hasF`, and `hasB` give sixteen
states. `Sixteen3.ofMask` uses weights 1, 2, 4, and 8 in that order.
`Sixteen3.none` is the empty subset; `Sixteen3.all` contains all four members.
Singleton N is distinct from the empty subset, and singleton B is distinct
from the subset containing T and F.

| Order | Inclusion memberships | Reverse inclusion memberships | Operations |
|---|---|---|---|
| Information `le_i` | N, T, F, B | None | `join_i`, `meet_i` |
| Truth `le_t` | T, B | N, F | `join_t`, `meet_t` |
| Falsity `le_f` | F, B | N, T | `join_f`, `meet_f` |

The command module and corpus use the same `Lean.Sixteen3` as the kernel.

| Implementation | Responsibility |
|---|---|
| [`src/Lean/Sixteen3.lean`](src/Lean/Sixteen3.lean) | Carrier, orders, six operations, solver interface |
| [`src/kernel/sixteen3.h`](src/kernel/sixteen3.h) | Native value, full-table monotonicity check, least fixed-point solver |
| [`src/Init/Paraconsistent.lean`](src/Init/Paraconsistent.lean) | Mode commands and declaration interface |
| [`src/Lean/Elab/Declaration.lean`](src/Lean/Elab/Declaration.lean) | Re-entry elaboration and complete map reduction |
| [`src/Lean/Meta/GetUnfoldableConst.lean`](src/Lean/Meta/GetUnfoldableConst.lean) | Stored payload unfolding |
| `src/kernel/declaration.{h,cpp}`, `src/kernel/environment.{h,cpp}` | Native declaration representation and insertion |

## Declare a checked re-entry value

```lean
import Init.Paraconsistent
open Lean

enable_trilattice

reentry injectedTruth (f : Sixteen3) : Sixteen3 :=
  Sixteen3.join_i f (Sixteen3.ofBelnap false true false false)

example : injectedTruth = Sixteen3.ofBelnap false true false false := rfl
example : injectedTruth.hasT = true := rfl
```

The elaborator reduces the declared map on all sixteen states. The native
solver checks information monotonicity across the complete table and iterates
from the empty subset. Four strict membership increases and a stability check
suffice. Malformed and nonmonotone tables are rejected, including failures away
from the iteration path.

The resulting declaration stores its `Sixteen3.mk` payload. Kernel reduction
unfolds this value; the compiler inlines it for `#eval` and compiled execution.
Module export and import retain the same memberships.

## Execute programs and inspect fixed points and cycles

The corpus connects combinator execution and native solving through a complete
value table. Each entry carries a proof of reduction from the original program.
Candidate endpoints are validated against that table before certificates are returned.

| Module in `p4ramill/Imscribing/Paraconsistent/` | Interface |
|---|---|
| [`TemporalSemantics.lean`](p4ramill/Imscribing/Paraconsistent/TemporalSemantics.lean) | Lifted FOUR negation, held closure, seeded feedback, tick signals |
| [`CombinatoryReentry.lean`](p4ramill/Imscribing/Paraconsistent/CombinatoryReentry.lean) | S/K/I, abstraction, Y conversion, certified contractions, resumable execution, six native operations |
| [`TrilatticePrograms.lean`](p4ramill/Imscribing/Paraconsistent/TrilatticePrograms.lean) | Seeded and diagonal programs, injection, retention, ordered composition, endpoint laws |
| [`CombinatoryFixedPoint.lean`](p4ramill/Imscribing/Paraconsistent/CombinatoryFixedPoint.lean) | Certified tables, least fixed points, feedback from empty |
| [`CombinatoryFixedPointBounds.lean`](p4ramill/Imscribing/Paraconsistent/CombinatoryFixedPointBounds.lean) | Greatest fixed points, feedback from full, enclosure, uniqueness from equal endpoints |
| [`CombinatoryDynamics.lean`](p4ramill/Imscribing/Paraconsistent/CombinatoryDynamics.lean) | Arbitrary-seed feedback, certified transient and primitive period, cached phase lookup, periodic continuation, restart |

Lifted FOUR negation exchanges T and F memberships while preserving N and B.
Raw negation unfolds a two-tick signal. `hold` computes the information union
of a state and its negation. `seededOperator` retains a seed through each
negation tick; feedback from empty settles at the seed's held closure. The evaluator exposes contractions
and proves that splitting a reduction budget preserves the result. Y has an
explicit conversion theorem in this term language.

`solveBounds` tabulates a program once, then computes the least point of that
map and the least point of its information-order dual using the native solver.
Information complement toggles all memberships; complementing the dual result
produces the greatest-point candidate. Both endpoints are checked against the
original table. Successful bounds carry fixedness, monotonicity, extremality,
and settlement proofs from feedback tick four onward, starting at empty and full.

Retain the T/F frame after injecting singleton B, then reverse the order:

```lean
import Imscribing.Paraconsistent.CombinatoryFixedPointBounds

open Imscribing.Paraconsistent.CombinatoryFixedPointBounds
open Imscribing.Paraconsistent.TrilatticePrograms

#eval (solveBounds 4 (retainAfterInject
  (Lean.Sixteen3.ofMask 6) (Lean.Sixteen3.ofMask 8))).map
  fun bounds => (bounds.lower.point, bounds.upper.point)

#eval (solveBounds 4 (injectAfterRetain
  (Lean.Sixteen3.ofMask 6) (Lean.Sixteen3.ofMask 8))).map
  fun bounds => (bounds.lower.point, bounds.upper.point)
```

The first program has endpoints empty and T/F. The second has endpoints B and
T/F/B. Composition order determines which memberships persist.
`Bounds.encloses_fixed` proves every fixed state lies between the endpoints;
`Bounds.unique_of_equal` proves uniqueness when they coincide. `Bounds.isFixed`
checks the map equation; `Bounds.contains` checks interval membership. A state
inside the interval can still move under the program.

`analyzeOrbit fuel program seed` compiles the same reduction-certified table
and searches for its first repeated state. A returned `Cycle` proves closure,
distinctness before the repeat, periodicity of all subsequent ticks, and a
program reduction at each tick. Period one certifies a fixed state; a longer
primitive period certifies movement. `findCycle table seed` reuses a table
already obtained from an endpoint certificate.

```lean
import Imscribing.Paraconsistent.CombinatoryDynamics

open Imscribing.Paraconsistent.CombinatoryDynamics
open Imscribing.Paraconsistent.CombinatoryReentry
open Imscribing.Paraconsistent.Temporal.Semantics

#eval (analyzeOrbit 1 .negation (FDE.singleton .T)).map
  fun cycle => (cycle.entry, cycle.period, cycle.loop)

#eval (analyzeOrbit 32 (seededOperator (FDE.singleton .N)) (FDE.singleton .T)).map
  fun cycle => (cycle.entry, cycle.period, cycle.loop)
```

Raw negation returns entry zero and period two, alternating singleton T and F.
Retaining singleton N gives one transient tick followed by the N/F and N/T
cycle. Both signals retain their states and their reduction witnesses.

Build `cycle.clock` once to cache native states, then use `clock.read tick` for
direct observations. Transient ticks keep their original positions; later
ticks use their offset from the cycle entry modulo its primitive period.
`Clock.read_eq_orbit` proves every cached read equals the original feedback.
`Clock.program_tick` and `Clock.restart` retain reduction and continuation
proofs for the cached interface.

```lean
import Imscribing.Paraconsistent.CombinatoryDynamics

open Imscribing.Paraconsistent.CombinatoryDynamics
open Imscribing.Paraconsistent.Temporal.Semantics

#eval (analyzeOrbit 1 .negation (FDE.singleton .T)).map
  fun cycle =>
    let clock := cycle.clock
    (clock.read 1_000_000_000_000_000_001,
      clock.read 1_000_000_000_000_000_002)
```

These consecutive observations return singleton F and singleton T through the
cached clock.

Every seeded native join or meet is supported. Its endpoints are obtained by
applying the seeded operation to information bottom and top. Constant maps,
including constants computed through Y, have equal endpoints. Identity, raw
negation, and `hold` have empty/full endpoints.

## Contradiction modes and classical restriction

`enable_paraconsistent` activates checks on recursors for empty `Prop`
inductives. Kernel constant checking rejects the raw recursor, and `casesOn`
generation is blocked for empty predicates, including parameterized and
indexed predicates. Mode changes preserve pending asynchronous kernel checks.

```lean
import Init.Paraconsistent

enable_paraconsistent
#is_paraconsistent
-- A direct h.rec with h : False is rejected while this mode is enabled.
disable_paraconsistent
```

Already compiled wrappers such as `False.elim` do not expose their raw recursor
to this check. The mode controls distinguish direct recursor use from imported wrappers.

[`ClassicalRestriction.lean`](p4ramill/Imscribing/Paraconsistent/ClassicalRestriction.lean)
formalizes the B-excluding Belnap subtype `{v // v ≠ B}` and the collapse
`classicalSwitch`, which sends B to F. In truth order, inclusion is left adjoint
to collapse and the composite on the subtype is identity. The reverse
adjunction and the information-order adjunction fail.

## Grammar corpus and domain constructions

The twelve primitives are ⊢ ⊣ ≻ ≺ ⋈ ⊤ ∈ ∋ ⊙ ⊥ ⊞ ⊡. Their mixed-radix Crystal
has size $3^3\cdot4^5\cdot5^4=17{,}280{,}000$, and split/fuse closure is
$\mu\circ\delta=\mathrm{id}$. The corpus includes Belnap and trilattice laws,
Frobenius constructions, orbital/Majorana readings, genetics, SIC-POVM
constructions, arithmetic transport, and Millennium witnesses.

The canonical catalog addresses include CL8NK
⟨𐑦𐑸𐑾𐑹𐑐𐑧𐑔𐑵⊙𐑫𐑳𐑟⟩ and CL9NK
⟨𐑛𐑥𐑑𐑬𐑐𐑪𐑔𐑝⊙𐑫𐑳𐑭⟩. The runtime mirror provides genetics controls
through `test_genetics.py` and `p4ramill_py/run_gene_pipeline.py`.

### Navier–Stokes injection

The carried re-entry construction returns the differential residual at every carrier level:

$$
F_n[u,p]=\partial_tu+(u\cdot\nabla)u-\nu\Delta u+\nabla p.
$$

`NS_Reentry.lean` proves the carrier round trip and injection identity.
`NS_InjectionField.lean` supplies the actual derivatives with zero and
time-linear controls. `NS_ResidualExtension.lean` constructs a smooth
continuation from all-order cancellation and exterior derivative bounds,
preserving interior derivative tensors and spatial support.

[`InjectionConnection.lean`](p4ramill/PublishedProfile/InjectionConnection.lean) imports the
[published construction](https://github.com/openai/NavierStokesAndEuler) under
its pinned Lean 4.34.0-rc2 toolchain. Its operator comparison equates the local
coordinate residual with the published Fréchet residual. The actual-profile
theorem identifies the published candidate's globally smooth force with the
carried injection at every level for $0<t<1$, continuing through $t=1$ while
retaining velocity blowup, compact force support, incompressibility, and finite energy.

## Run the native checks

The native tests check carrier states, lattice laws, declaration payloads, and
mode controls. Run them from the repository root using the built fork:

```sh
LEAN_PATH=build/stage1/lib/lean build/stage1/bin/lean -j1 tests/lean/run/sixteen3.lean
LEAN_PATH=build/stage1/lib/lean build/stage1/bin/lean -j1 tests/lean/run/reentry.lean
LEAN_PATH=build/stage1/lib/lean build/stage1/bin/lean -j1 tests/lean/run/reentryValue.lean
LEAN_PATH=build/stage1/lib/lean build/stage1/bin/lean -j1 tests/lean/run/trilatticeMode.lean
```

The corpus audit modules check ticks, contractions, all six operations,
composition, native solving, fixed-point bounds, and arbitrary-seed cycles. They print theorem
dependencies and check rejection of invalid candidates. The enclosure,
uniqueness, greatest-point program reduction, and feedback-settlement theorems
have no axiom dependencies. The cycle audit checks every native starting state
for the lattice, combinator, and retained-negation families, with controls for
nonclosing and nonprimitive cycle candidates. Periodic continuation, primitive
return, restart, and `Cycle.program_tick` and the fixed/moving cycle theorems
also have no axiom dependencies. Phase-normalized clock agreement, program
reduction, and restart depend on `propext` through the arithmetic normalization.
