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

Factoring remains on hiatus. The current execution domain is the native
sixteen-state register with recursively growing compartments and the bound VGI
learner.

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
