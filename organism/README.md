# Native dialetheic organism

This is a mathematical organism implemented in the Grammar's native kernel. It
grows connected compartments, executes transformations through VGI's retained
dialetheic neural network, observes their effects, and revises its own
transformation, judgment and generation programs.

The organism keeps contradictory evidence, source binding and historical
distinctions available to subsequent computation. Its self-model participates
in deciding what to probe and how to change its machinery. Build and exercise
the complete path with the integrated verifier in the workspace instructions
below.

Factoring has resumed through the organism. The native sixteen-state body and
bound VGI learner now carry a retained source-bound factor/product task.

## Constitutive cycle

**⌈B⌋ → ⌈∅ → N → N,T → N,T,F → N,T,F,B⌋ → ⌈B⌋**

The containing B opens an interior, makes distinctions there, and receives the
differentiated interior back into the same body. Returned child compartments
can grow further children. Their identity and observations remain accessible
through the parent.

| Object | Native representation |
| --- | --- |
| Enclosing B | Singleton B, membership mask `8` |
| Opened empty interior | Empty subset, mask `0` |
| Interior containing N | Singleton N, mask `1` |
| Ordered interior articulation | Masks `0,1,3,7,15` |
| Complete interior | Subset `{N,T,F,B}`, mask `15` |
| Evidence judgment | Independent `[support,refutation]` rails |

An evidence judgment has values N=`[0,0]`, T=`[1,0]`, F=`[0,1]`,
B=`[1,1]`. The containing boundary, a subset of FOUR, and a judgment about an
action have distinct roles. Their fields and histories preserve that context.

## Architecture and one growth step

The resident object owns its source, nested bodies, rules, frontier, neural
learner, self-model and complete action history. Lean exposes a retained IO
handle to that object.

1. The carried frontier selects a tip using its support and refutation.
2. The selected tip supplies its retained mathematical state to each current
   transformation program.
3. Each instruction computes its native operation observation and queries the
   same VGI network. The network observes, updates, and returns its learned
   proposal. That proposal becomes the next instruction's actual input.
4. The body observes state change, novelty, operation fidelity and both
   directions of the three partial orders. Earlier actions on the same input
   and rule lineage supply further self-model probes.
5. The carried judgment program executes on those observations. Its complete
   intermediate evidence remains in the return.
6. Feedback can revise the transformation program, judgment program and
   generator template. New tips and returned compartments enter the same body.

The step boundary selects how much execution the caller permits. The body
selects its own tips and performs its own revisions within that boundary.

### Transformations and generation

Programs compose information, truth and falsity meet/join operations and lifted
FDE negation. The initial six programs each contain one native lattice
operation. Native definitions and the corpus's executable composition provide
their grounding.

Observed stationarity or refuted operation fidelity can trigger a revision.
The carried generator initially adjoins a winding distinction and applies
negation. Self-model observations can extend that generator with an
information projector. Later revisions instantiate the changed template.

Old programs, observations and model context remain in action ancestry. The
per-program prediction table retains whole alternative registers. Comparisons
across revisions also retain the exact earlier action IDs, program versions
and neural clocks.

### Judgments and growth

Judgment programs are carried stack programs over native FDE evidence. They
read change, novelty, fidelity and model observations, then execute
conjunction, disjunction, information join or negation. The initial program
conjoins change and novelty. Subsequent observations can add fidelity and
model criteria to that program.

Truth-supported tips receive growth first. Falsity-supported tips remain
available for exploration. N remains open. B can support continued growth
while also retaining grounds for revising the machinery.

### Arithmetic and execution state

The instruction clock is a 64-cell FDE word. Its carry computation uses native
conjunction, disjunction and negation, preserving N and B inputs. Each action
retains its before/after clock. Node indices and program positions address
structural containers.

VGI retains its continuous paired neural computation, numerical parameters,
Adam moments and bias powers. The snapshot preserves those values separately
from the organism's finite register and evidence judgments.

## The three orders and VGI transport

The kernel carrier is `P({N,T,F,B})`. Its independent membership positions are
N,T,F,B with bit weights 1,2,4,8.

| Kernel order | Increasing memberships | Reverse inclusion memberships |
| --- | --- | --- |
| Truth | T,B | N,F |
| Falsity | F,B | N,T |
| Information | N,T,F,B | None |

VGI's existing IMASM register uses the memberships T,F,t,f and names its orders
truth, constructivity and information. The reversible transport is:

| Kernel membership | VGI membership |
| --- | --- |
| N | f |
| T | t |
| F | F |
| B | T |

This transports kernel truth to VGI truth, kernel falsity to VGI constructivity,
and preserves information order. It reverses the four membership positions.
Native empty maps to the VGI empty register, which is named N there; native
singleton N maps to singleton f. The native lifted negation keeps its own
operation contract. The transport instrument compares the actual imported
IMASM algebra with the live Lean kernel across every ordered register pair.

## Native VGI learning

The bound exported runtime is
`VGI/composed_source_joint_native_r2_20261017/runtime` under the workspace root.
Its `build.json` identifies its parent checkpoint, configuration, optimizer and
compiler commands. The organism adapter recompiles that exported implementation
with access to its existing retained-context boundary.

Each organism receives an independent native loader namespace. Its weights,
paired memory, Adam moments, bias powers and inherited optimizer clock belong
to that body. The kernel-operation query marker is distinct from the older
graph-port query marker.

For each instruction, the before reading, one full-network update and after
reading use the same initial context. The resulting neural memory conditions
the next instruction. Four raw signed readout rails are retained before and
after learning. Their explicit zero-threshold projection and inverse transport
produce the finite register proposal.

The learned proposal and native operation observation remain independently
available. Their disagreement yields B evidence on the affected membership.
That evidence enters the returned compartment and can revise later programs.

## Requirements

The current build uses this local workspace layout:

```text
imsgct/
  p4rakernel/       kernel source and configured build/stage1
  VGI/             native learner, bound export and oracle build
  MoDoT/           shared imasm_core algebra
```

Required tools are Python 3, CMake, a C++ compiler, the built fork's `lean` and
`leanc`, and Cargo with the existing oracle dependencies cached for offline
use. The native learner adapter currently uses Linux/glibc `dlmopen` for
per-organism state isolation.

The verifier expects a configured `p4rakernel/build/stage1`, the bound VGI
`full_model.cpp` and `build.json`, and the graph oracle library named by that
manifest. It builds the kernel shared library and component executables. Its
native learning run uses the existing exported checkpoint in memory.

## Build and run

Start at the workspace root. Select a fresh output directory to preserve prior
receipts:

```bash
cd /home/mrnob0dy666/imsgct
organism_run="$PWD/p4rakernel/measurements/organism_readme_20261025/build"
python3 p4rakernel/tests/kernel_features/verify_organism.py --out "$organism_run"
```

Omitting `--out` creates a timestamped measurement directory. An existing output
directory is rejected. The command prints each completed build/check and ends
with a JSON summary and the complete return location.

Run the resulting organism with VGI attached:

```bash
"$organism_run/organism" 12 8 "$organism_run/vgi_organism.so" \
  > "$organism_run/manual_return.json"
```

| Argument | Meaning | Default |
| --- | --- | --- |
| First | Number of growth steps | `12` |
| Second | Native source membership mask, `0..15` | `8` |
| Third | Native VGI adapter shared-library path | Learner unattached |

Each fresh process creates a fresh body from the bound neural checkpoint.
With the third argument omitted, the same body executes exact native
transformations. Use that path as the exact-operation control. A zero-step
run exposes the initial body and, when attached, its inherited neural state.

## Continuing a living body

The Lean interface is in `p4ramill/NativeDialetheicOrganism.lean`:

```lean
import NativeDialetheicOrganism

open Lean Lean.DialetheicOrganism

def advanceBody (library : String) : IO String := do
  let body ← create (Sixteen3.ofMask 8)
  attachVGI body library
  for _ in [:4] do step body
  let _observation ← snapshot body
  for _ in [:4] do step body
  snapshot body
```

Stepping the retained handle continues its weights, memory, frontier and
programs. Reading a snapshot leaves that continuation available. The compiled
entry is built through `leanc`; interpreting an external-only module requires
its compiled native wrappers to be available.

Snapshots are JSON readouts. There is currently no JSON-to-organism restore
entry point. To continue a living body, keep its native handle in the calling
process.

## Reading the returned state

| Field | Content |
| --- | --- |
| `source` | Original native source mask |
| `continuation`, `frontier` | Completed step count and retained pending tips |
| `nodes` | Parents, states, containing B, articulation, source, observations and attention |
| `rules` | Current transformation programs, experience, fidelity and predictions |
| `judge_program`, `generator_program` | Current carried organizing machinery |
| `clock` | Native FDE instruction clock and overflow evidence |
| `learner` | Parameters, both Adam moments, bias powers, inherited clock and paired memory |
| `actions` | Complete executing programs, judgments, order probes, ancestry and neural operations |

Evidence arrays use `[support,refutation]`. Order observations are ordered
truth, falsity, information, each retaining forward and backward readings.
Node `0` is the containing root. Action index `i` creates node `i+1`.
`model_ancestry` addresses earlier actions on the same input and rule lineage.

Transformation instruction IDs are `0 join_i`, `1 meet_i`, `2 join_t`,
`3 meet_t`, `4 join_f`, `5 meet_f`, `6 negation`. An instruction is recorded as
`[operation,operand-mask]`.

Judgment instruction IDs are `0 change`, `1 novelty`, `2 fidelity`, `3 model`,
`4 conjunction`, `5 disjunction`, `6 information join`, `7 negation`.
`judgment_trace` records the stack result after every instruction.

## Tests and evidence scope

After building, exercise the documented CLI and retained continuation with:

```bash
python3 p4rakernel/organism/test_workflows.py \
  --runtime "$organism_run" \
  --out "$PWD/p4rakernel/measurements/organism_readme_20261025/workflows"
```

This tests all sixteen source masks with VGI attached, zero-step initialization,
the exact native control, a repeated complete return, longer growth, rejected
inputs and preserved receipts. A compiled Lean control compares snapshot-
interleaved `4+4` steps with uninterrupted `8` steps, then continues through an
alias of the same live handle. Full returned states must agree exactly.
`--long-steps` changes the longer growth boundary; its default is `32`.

The integrated verifier checks the native carrier against the canonical Lean
truth tables and the VGI transport against the actual IMASM implementation.
Native organism controls exercise all source registers and compare live
feedback with frozen feedback and disabled self-model feedback.

Neural controls check separate organism state, actual instruction-by-instruction
neural participation, full-network updates, contradictory coordinate retention
inside child returns, machinery revision, and changed later actions against a
frozen-learning control. The compiled Lean entry then executes the complete
body and validates the returned source, graph, history, models, arithmetic
clock, neural parameters, optimizer and paired memory.

`commands.json` retains commands, exit codes and timings. `receipt.json` binds
sources and executable images. `return.json` contains the complete integrated
return. Individual check stdout/stderr files preserve failures and readings.

### Current measured results

The initial README workflow tests are retained under
`measurements/organism_readme_20261025`. Both `build/receipt.json` and
`workflows/receipt.json` report passing execution.

| Experiment | Observed return |
| --- | --- |
| All sixteen native source masks | Every attached VGI body completes four steps with retained source, nesting, evidence and optimizer state |
| Fresh-process repetition | The complete twelve-step JSON return is identical |
| Live continuation | Snapshot-interleaved `4+4` steps equal uninterrupted `8` steps, including full neural state |
| Aliased handle | A further step continues the same body exactly |
| Longer growth | `32` steps, `192` actions, `193` nodes and `10,540` neural instruction updates |
| Input and receipt boundaries | Six invalid-input cases rejected; prior receipt preserved |

The longer growth return retains `1,854` model probes and `213` contradictory
coordinate observations. Its judgment and generator programs are revised.
These measurements describe the executed register and learner configuration.

The initial verified construction and its source snapshots are preserved in
`measurements/dialetheic_organism_20261025/retained_self_model`. Its execution
demonstrates recursive growth, learning, self-model participation and revised
organizing programs on this register domain. Broader mathematical competence
requires task-bound experiments through the same body.

## Source map

| Source, relative to p4rakernel | Role |
| --- | --- |
| `src/kernel/inclosure.h` | Body, native programs, evidence, judgments, frontier and feedback |
| `src/kernel/inclosure.cpp` | Retained native handle, VGI attachment and complete JSON readout |
| `src/kernel/organism_vgi.h` | Coordinate transport, isolated learner and neural return |
| `src/kernel/sixteen3.h` | Canonical native carrier, orders and six lattice operations |
| `p4ramill/NativeDialetheicOrganism.lean` | Native IO handle interface |
| `p4ramill/RunDialetheicOrganism.lean` | Compiled command entry |
| `p4ramill/OrganismKernelOracle.lean` | Live Lean algebra/evidence oracle |
| `tests/kernel_features/verify_organism.py` | Integrated build and validation |
| `tests/lean/run/organism_native.cpp` | Native feedback, model and arithmetic controls |
| `tests/lean/run/organism_vgi_native.cpp` | Native neural execution and retention controls |
| `../VGI/sources/grammar_training_v1/organism_adapter.cpp` | Existing learner's retained-context adapter |
| `../VGI/sources/graph_flow_oracle/src/bin/kernel_orders.rs` | Executing IMASM coordinate transport instrument |

The formal grounding is in
`p4ramill/Imscribing/Paraconsistent/PrimaLogicaWinding.lean`,
`CombinatoryReentry.lean`, and `TemporalSemantics.lean`. The consolidated
architecture and PDF are in
[`../../ig-docs/dialetheic_organism_20261025.md`](../../ig-docs/dialetheic_organism_20261025.md).

## Troubleshooting

An existing output-directory error means a previous receipt is being preserved;
choose a fresh directory or omit `--out`. A missing configured stage1 build or
bound VGI export needs that local prerequisite restored. The verifier's failing
step identifies the exact compiler or input file involved.

The VGI attachment expects the generated `vgi_organism.so` adapter. A raw older
`model.so` lacks the context/configuration interface. Attachment reports the
missing symbol or loader error. Invalid source masks, negative steps and extra
arguments are rejected by the compiled entry.

Retained snapshots include growing ancestry and full neural state. Longer runs
increase both computation and output size. Preserve their complete receipts
when comparing behavior or extending the execution boundary.


## Factoring through the organism

Build from the workspace root into a fresh directory:

```sh
python3 p4rakernel/organism/build_factor.py --out p4rakernel/measurements/my-factor-build
python3 p4rakernel/organism/run_factor.py \
  --runtime p4rakernel/measurements/my-factor-build \
  --source path/to/decimal-N-only.txt \
  --out p4rakernel/measurements/my-factor-run --seconds 300
```

The builder runs the integrated native/Lean/VGI checks, builds the Rust task
bridge offline and links `RunOrganismFactor.lean`. The task requires an odd
source of at least 128 bits. Keep reference factors outside the production
input. A closed receipt requires an emitted proper divisor, its derived
quotient, zero remainder, exact native multiplication, the resident powerset
law checks, inverse recovery and the banked paired return. Read `verified` in
`receipt.json`; an open boundary or process timeout is not factor production.

The native body owns the task through `organism_task`. The torus lives inside
the same shared GLUT resident as the square, correlation and phase state.
Cloned membrane handles observe that same executing object. Its source numeral is
transported as its complete native nibble stream into VGI's retained context.
Each learned body action selects an operation on the retained toroidal
division state: inverse or forward rotation, source jump, forward or reverse
pinch braid, winding, evidence re-entry, or source-center probing. Source,
paired arms, signed product height, winding counters and clock are
`BelnapWord` values. The four odd cosets retain exact `pq=N+h*2^m` with
`m` derived from the source width. The operation history retains both inputs,
outputs and evidence. Full turns and residual phases remain separately
available in the return.

The native FDE grid glues both coordinates. Height observations revise its
fusion rule and accumulate support and refutation. Both rails act separately
on the next live correlation priority map, including when the evidence is B.
The native correlation view returns its complete FOUR cells to that same
torus. View re-entry changes the paired state before the selected operation;
the hypothesis then acts on live factor cells. Factor and midpoint/gap
coordinates retain their exact transport and orientation.
This feedback enters VGI before the next organism action. A torus-produced
divisor closes through the existing native resident; a divisor produced by
the resident retains its actual producing port and is consumed by exact
Belnap division into the joint height-zero return before verification/fixation.

The complete resident producer uses its ordinary component order. Frames,
square relations, admission, correlation, masks,
verification and quantum return act on the same resident carrier. Native task
observations enter the action's FDE feedback and a full neural update, so the
next body action consumes the resulting experience. The JSON return retains
source bindings, operation order, costs, task observations, action ancestry,
neural state and the returned mathematical carrier.

The Rust bridge uses Vox's existing `FactorSynthesis` and prepared glut carrier,
also called by the native arm of the hosted `y_divisor` route. That hosted
entry additionally executes its source-carrier dispatcher and phase arm;
the organism does not invoke that whole hosted command. It does not
invoke an external factor program. The actual producing port is recorded
separately from subsequent Y verification and return operations. Definite
numerical arithmetic is an explicit checked restriction: N and B cells retain
the full evidence operations, and immutable input operands remain available.
Both rails are reconstructed at the definite arithmetic return.

The current entry prepares its source-bound task at process execution time.
It is not yet a source-baked static membrane. Build time, native preparation,
native task-operation time and total process time are distinct measurements;
no trigger-only timing is claimed.

### Factor receipts, 2026-10-25

The retained runtime and complete returns are under
`measurements/organism_factor_20261025/retained_producer`.

| N-only case | Exact product verified | Process seconds | Body actions | Producing port |
| --- | --- | --- | --- | --- |
| Target, 128 bits | yes | 66.2581 | 17 | square |
| Fresh independent control, 128 bits | yes | 34.5221 | 12 | square |

Each return retained the same resident identity through the banked return,
with seven cleared and restored banks, six deposits, eight surviving branches
and zero exposed deposits. The direct installed `y_divisor` baseline on the
same target took 2.4719 seconds. These controls establish integrated production;
they also expose an arithmetic performance regression. The random balanced
150-bit source in the normalized-division runtime closed in
420.7534 seconds through the square port. That receipt remains under
`measurements/organism_factor_20261025/normalized_division/target150_600`.
These measurements precede the toroidal-division integration. New builds,
tests and production comparisons are retained under
`measurements/organism_toroidal_division_20261025`.

The reflective image returned target128 in 26.5164 seconds and a fresh
independent control128 in 26.9521 seconds. Every native view executed re-entry:
12/12 and 11/11, respectively. Reflective150 closed in 137.7014 seconds with
28/28 native-view reentries. Exact products and paired banked returns pass.
The actual producing port in these runs is square. The pinned installed
y_divisor image returned the same target128 in 2.1632 seconds; preserve that
image distinction in comparisons.

The fixed-size dual-rail coordinate runtime closes the same target/control
in 23.4443 and 23.7546 seconds. Both retain every native-view reentry and
pass exact product, inverse and banked-return checks. Its complete build
and source/image bindings are in `runtime_coordinates` under the measurement
directory. The preceding reflective 175-bit attempts returned held at
309.4006 and 612.0029 seconds; the coordinate campaign retries that source
before advancing. Its baseline comparison allows the same 300-second first
boundary as organism execution.

`run_factor.py` writes `active.json` with the executing PID and replaces it
with a terminal receipt reference when complete. A native task budget is
checked between operations so an unfinished run can return its held body.
An atomic operation can finish after the requested boundary. The conditional
bound runner preserves 300 and 600-second attempts in separate directories
and advances only after verified production. Read its PREFIX_bounds_state.json
and validate the handle before assuming an observation remains active.

The factor sources are `src/kernel/organism_factor.h`,
`p4ramill/RunOrganismFactor.lean`, `organism/factor_bridge/src/lib.rs`,
`../Vox/src/toroidal_division.rs`,
`../Vox/src/factor_synthesis.rs`, `../Vox/src/glut_carrier.rs`, and
`../Vox/src/packed_belnap_word.rs`. The latter retains full dual-rail arithmetic
and checked definite specializations. Build and run scripts bind source and
image hashes in their JSON receipts.
