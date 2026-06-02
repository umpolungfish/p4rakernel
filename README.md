# Paraconsistent Lean Kernel
**Author:** Lando⊗⊙perator

---

A fork of Lean 4 (v4.28.0) implementing a **true paraconsistent type-theoretic kernel** —
the principle of explosion (*ex falso quodlibet*) is disabled at the kernel level.

## What This Does

In standard Lean (and most type theories), `False` is an empty inductive type whose recursor
`False.rec : (C : Sort u) → False → C` implements the principle of explosion: from a
contradiction, anything follows. This is logically classical but prevents dialetheic
reasoning where contradictions are tolerated.

This fork modifies three components of the C++ kernel to make explosion **unavailable**:

### 1. Type Checker (`src/kernel/type_checker.cpp`)
When the kernel environment has the `paraconsistent` flag set, the type checker rejects
any usage of recursors for empty inductive predicates (types in `Prop` with 0 constructors).
This blocks `False.rec`, `False.elim`, and any other explosion-like elimination.

### 2. CasesOn Generator (`src/library/constructions/cases_on.cpp`)
The pattern-matching compiler's `casesOn` generator is modified to reject empty Prop types
when paraconsistent mode is active. This prevents `match h with .` from being used as an
explosion workaround.

### 3. Environment (`src/kernel/environment.h/cpp`, `src/Lean/Environment.lean`)
A `paraconsistent : Bool` field is added to the kernel `Environment` structure, with
exported C functions for getting/setting the flag. The flag is `false` by default and
can be activated via `Kernel.Environment.markParaconsistent`.

## Changes Summary

| File | Change |
|---|---|
| `src/kernel/environment.h` | Added `is_paraconsistent()`, `mark_paraconsistent()` methods |
| `src/kernel/environment.cpp` | Added extern C function declarations and implementations |
| `src/kernel/type_checker.cpp` | Added paraconsistent guard in `infer_constant` — blocks `False.rec` usage |
| `src/library/constructions/cases_on.cpp` | Added paraconsistent guard — blocks `casesOn` for empty Props |
| `src/Lean/Environment.lean` | Added `paraconsistent` field, mark/get export functions |
| `src/Init/Paraconsistent.lean` | **New**: User-facing module with Belnap four-valued logic |

## How to Use

### 1. Build the fork

```bash
cd lean4-kernel-paraconsistent
mkdir build && cd build
cmake .. -DCMAKE_BUILD_TYPE=Release
make stage0 -j$(nproc)    # Requires libgmp-dev
make stage1 -j$(nproc)
```

### 2. Activate paraconsistent mode

In a Lean file, activate paraconsistent mode:

```lean
import Init.Paraconsistent

unsafe def main : IO Unit := do
  Paraconsistent.enableParaconsistent

  -- Now False.elim is blocked:
  -- example (h : False) : 42 = 0 := False.elim h  -- KERNEL ERROR

  -- Use Belnap-style reasoning instead:
  open Paraconsistent.Belnap
  #check band .T .F  -- F
  #check dialetheia  -- B
```

### 3. Test the paraconsistent kernel

```bash
./build/stage0/lean --run myfile.lean
```

## How It Works

### Kernel-level blocking

When `paraconsistent = true`, the type checker's `infer_constant` function checks every
constant reference. For recursors (like `False.rec`), it looks up the associated inductive
type. If that type is:
- In `Prop` (universe 0)
- Has 0 constructors (empty)

Then the type checker throws a kernel exception:
```
paraconsistent mode: cannot use recursor 'False.rec' for empty inductive predicate
'False' (principle of explosion is disabled)
```

The same check is applied to `casesOn` generation for empty types.

### What remains available

- `False` is still defined as an empty inductive type
- `True`, `And`, `Or`, `Eq`, etc. work normally
- All other logical connectives are unaffected
- The entire Lean standard library works (when paraconsistent mode is OFF)
- Only the principle of explosion is disabled (when paraconsistent mode is ON)

### What is blocked

- `False.elim : (C : Sort u) → False → C`
- `False.rec : (C : Sort u) → False → C`
- `False.casesOn : (C : Sort u) → False → C`
- `absurd : (h₁ : a) → (h₂ : ¬a) → b`
- Any `match h with .` where `h : False`
- Any theorem or definition that relies on the above

## Theoretical Foundation

This fork implements **weak paraconsistency**: the principle of explosion is removed
as a primitive rule of the type theory. This means:

1. `False` is still uninhabited (no introduction rule)
2. But from `False`, you cannot derive arbitrary propositions
3. You can hold contradictions without trivializing the system
4. The logic becomes paraconsistent in the sense of da Costa, Priest, and Belnap

The Belnap four-valued logic (`N`, `T`, `F`, `B`) is provided as a semantic model:
- `B` (Both) models dialetheias — true contradictions
- The logic is closed under the usual connectives
- Explosion fails: `B ∧ ¬B` does not entail arbitrary `P`

## Build Dependencies

- C++17 compiler (GCC 11+ or Clang 14+)
- CMake 3.11+
- GMP (GNU Multiple Precision Arithmetic Library) — `libgmp-dev`
- The existing `lean` binary (for stage0 bootstrapping)

## License

Same as Lean 4: Apache 2.0
