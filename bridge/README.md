# Hosted Lean kernel bridge

G-mOMonadOS and Vox's primary hosted commands call this bridge before payload
work. Admission elaborates a real `reentry` declaration in the fork, checks that
SIXTEEN_3 is active, and executes the certified combinatory Y reducer with the
native least/greatest solvers. Failed admission exits with status 2. There is no
Rust replacement solver or mode-off fallback. The check is cached per process.

Both executables expose the same `reentry` and `lean-kernel` commands.
G's REPL also accepts `vox reentry`. Its result stays inside the existing command
vessel until the terminal frame releases it.

```
vox reentry Y 6
vox reentry orbit 2 1000000000001 negation
vox reentry join_t 5
vox reentry retain-after-inject 7 10
vox reentry program Y K K data:6 @ @ @
vox reentry word '⊢∈≻⋈⊙⊤≻⋈⊥≺⋈⊞∋⊡⋈⊙⊣' 0 1000000000000
g-momonados reentry help
```

Masks use the kernel's N=1, T=2, F=4, B=8 order. Runtime register lanes T,F,t,f
convert to native B,F,T,N. `phase_word::native_transition_table` executes the
existing interpreter from every register seed; seeds add no observation
deposits. Payload execution retains its existing zero seed. Each feedback step
runs the word with fresh frames. Persistent payload/frame feedback requires a
larger state model.

Named and postfix programs use `tabulate`, `solveBounds`, `findCycle`, and
`Cycle.clock.read`. Their returned certificates retain Lean reduction proofs,
monotonicity, leastness, greatestness, and primitive cycle evidence. All six
native lattice operations are supported. Arbitrary postfix S/K/I/Y programs
must reduce to data at every carrier input within 4096 steps.

The word and raw-table routes send all sixteen runtime outputs to the native
solver, validate fixedness and extremality in Lean, and compute finite feedback
closure. Those checks concern the supplied transition table. They do not prove
that Rust payload arithmetic or an external binary implements that map. A
nonmonotone table can have a valid cycle while lacking a native monotone fixed
point certificate; the report states that explicitly.

The primary CLI admission is shared by all its command branches, including
direct routes. Standalone Cargo binaries and the no_std libraries do not spawn
Lean. Existing FOUR verdicts, GPU execution and factoring arithmetic keep their
own execution semantics; their payload proofs have not been replaced by the
admission certificate.

The sibling checkout is located relative to `CARGO_MANIFEST_DIR`; an alternate
checkout can be selected with `P4RAKERNEL_ROOT`. The bridge requires the fork's
`build/stage1/bin/lake` and `lean` and p4ramill's built imported modules. Each
request uses `lake env lean --run KernelBridge.lean`, so source changes are
checked immediately. Primary CLI startup includes that elaboration cost.
