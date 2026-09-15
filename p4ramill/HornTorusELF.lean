/-
HornTorusELF.lean — the executable kernel of Imscribing.Millennium.HornTorusGeometry
====================================================================================
v3: RUNTIME-ONLY kernel. Compiled to an ELF and audited by V⊙x (the control-flow
closure auditor).

v1 bug (fixed): Lean's codegen constant-folds `if 16*16*16 = 4096 then …` into a
`static uint8_t` closed constant, lazily initialized by `initialize_HornTorusELF`.
dlopen/ctypes never calls that initializer, so every folded check read 0 and
native horn_torus_check returned 7 instead of 20.
v2 (7→9): threading `z n` into the arithmetic RHS helped only the c01–c04 and
c17–c20 checks; checks reading the literal word bindings (lengthOf ns, opAt ns 2,
countDig16 riemann 9) were still closed because the WORDS are compile-time
constants — the codegen folds any closed expression, not just literal ifs.
v3 (this): the seven words are bound as `word + z n` so every downstream check
is runtime — no statics, no initializer required, and every one of the 20
checks is a real branch for V⊙x to lift and pair.

The module's theorems are Prop — erased from code generation. What survives
as machine code is the computable kernel: the (16,3) knot arithmetic, the
seven Clay-structure ob3ect words, their ∈/∋ pairs, their dialetheia, and
the theorem→torus-feature table. This file re-encodes that kernel in pure
UInt64 arithmetic so the exported function is self-contained machine code:
every opcode is a 4-bit digit, every word a UInt64, every check a compare.

Encoding (4 bits per token, little-endian, 0 = empty):
  VINIT=1 TANCH=2 AFWD=3 AREV=4 CLINK=5 IMSCRIB=6 FSPLIT=7 FFUSE=8
  EVALT=9 EVALF=10 ENGAGR=11 IFIX=12

The seven words, exactly as generated (encodings computed from the module
source, not hand-transcribed):
  ns       ⊢⊙∈≻⊤≺⊥⊞⋈⊡∋⊣                0x000028C5BA493761
  ym       ⊢⊣≻⋈⊙∈⊤≻⊥≺⊞⋈∋⊡⊙⊣             0x26C85B4A39765321
  bsd      ⊢⊙∈≻⊤⋈≺⊥∋⊞⊡⊣                0x00002CB8A4593761
  hodge    ⊢≻∈⊤≺⊥⋈⊙⊞∋⊡⊣                0x00002C8B65A49731
  riemann  ⊢⊣∈≻⊤≺⊥⊞∋⊙⋈⊡⊣               0x0002C568BA493721
  pvsnp    ⊢⊙∈≻⊤⋈≺⊥⊞⊡⋈⊙∋⊣⊡              0x0C2865CBA4593761
  dyn      ⊢≻∈⊤⊥⊞⋈≺∋⊙⊡⊣                0x00002C6845BA9731

Author: Quantum⊙perator (Lando⊗⊙perator team) · 2026-08-24
-/

-- self-contained: no imports (Init only) — the exported kernel must be
-- link-clean so the ELF has no unresolved initializer or Mathlib symbols.

namespace HornTorusELF

-- op at 4-bit position i (i = 0 is the least significant digit)
def opAt (w i : UInt64) : UInt64 := (w >>> (4 * i)) &&& 15

-- count of digit d over the 16 positions of the window (unrolled: no recursion)
def countDig16 (w d : UInt64) : UInt64 :=
  (if opAt w 0 = d then 1 else 0) + (if opAt w 1 = d then 1 else 0) +
  (if opAt w 2 = d then 1 else 0) + (if opAt w 3 = d then 1 else 0) +
  (if opAt w 4 = d then 1 else 0) + (if opAt w 5 = d then 1 else 0) +
  (if opAt w 6 = d then 1 else 0) + (if opAt w 7 = d then 1 else 0) +
  (if opAt w 8 = d then 1 else 0) + (if opAt w 9 = d then 1 else 0) +
  (if opAt w 10 = d then 1 else 0) + (if opAt w 11 = d then 1 else 0) +
  (if opAt w 12 = d then 1 else 0) + (if opAt w 13 = d then 1 else 0) +
  (if opAt w 14 = d then 1 else 0) + (if opAt w 15 = d then 1 else 0)

-- length = number of non-empty positions (positions past the end read 0)
def lengthOf (w : UInt64) : UInt64 := 16 - countDig16 w 0

-- theorem → torus-feature, re-encoded as digits (the context table):
--   NS→Pinch(1) YM→SplitShell(2) BSD→Coupler(3) Hodge→Coupler(3)
--   Riemann→TrineEngagr(6) PvsNP→KnotWinding(7) Dynamics→TrineTop(4)
def featureOf64 (t : UInt64) : UInt64 :=
  if t = 1 then 1
  else if t = 2 then 2
  else if t = 3 then 3
  else if t = 4 then 3
  else if t = 5 then 6
  else if t = 6 then 7
  else 4

-- runtime zero derived from the audit input: keeps every check non-closed
def z (n : UInt64) : UInt64 := n - n

-- The exported check: the count of invariants that hold (20 = all).
-- Every word is bound as word + z n and every literal comparison carries
-- + z n, so no check is a compile-time constant: the codegen emits pure
-- runtime branches (real forks for V⊙x to pair).
@[export horn_torus_check]
def hornTorusCheck (n : UInt64) : UInt64 :=
  let ns := 0x000028C5BA493761 + z n
  let ym := 0x26C85B4A39765321 + z n
  let bsd := 0x00002CB8A4593761 + z n
  let hodge := 0x00002C8B65A49731 + z n
  let riemann := 0x0002C568BA493721 + z n
  let pvsnp := 0x0C2865CBA4593761 + z n
  let dyn := 0x00002C6845BA9731 + z n
  -- (16,3) knot arithmetic
  let c01 := if 16 * 16 * 16 = 4096 + z n then 1 else 0
  let c02 := if 16 = 2 * 2 * 2 * 2 + z n then 1 else 0
  let c03 := if 2048 = 2 * 2 * 2 * 2 * 2 * 2 * 2 * 2 * 2 * 2 * 2 + z n then 1 else 0
  let c04 := if 16 = 4 * 4 + z n then 1 else 0
  -- periods (scaffold headers)
  let c05 := if lengthOf ns = 12 + z n then 1 else 0
  let c06 := if lengthOf ym = 16 + z n then 1 else 0
  let c07 := if lengthOf riemann = 13 + z n then 1 else 0
  let c08 := if lengthOf pvsnp = 15 + z n then 1 else 0
  let c09 := if lengthOf dyn = 12 + z n then 1 else 0
  -- ∈/∋ pairs at the recorded positions (0-indexed)
  let c10 := if opAt ns 2 = 7 && opAt ns 10 = 8 then 1 else 0
  let c11 := if opAt riemann 2 = 7 && opAt riemann 8 = 8 then 1 else 0
  let c12 := if opAt pvsnp 2 = 7 && opAt pvsnp 12 = 8 then 1 else 0
  -- dialetheia-complete: both arms deposit
  let c13 := if countDig16 riemann 9 > 0 + z n && countDig16 riemann 10 > 0 + z n then 1 else 0
  -- exactly one FSPLIT / one FFUSE per word
  let c14 := if countDig16 ns 7 = 1 + z n && countDig16 ns 8 = 1 + z n then 1 else 0
  let c15 := if countDig16 riemann 7 = 1 + z n && countDig16 riemann 8 = 1 + z n then 1 else 0
  let c16 := if countDig16 pvsnp 7 = 1 + z n && countDig16 pvsnp 8 = 1 + z n then 1 else 0
  -- theorem → torus feature (runtime t so the if-chain is not folded)
  let c17 := if featureOf64 (5 + z n) = 6 + z n then 1 else 0
  let c18 := if featureOf64 (1 + z n) = 1 + z n then 1 else 0
  let c19 := if featureOf64 (6 + z n) = 7 + z n then 1 else 0
  let c20 := if featureOf64 (7 + z n) = 4 + z n && featureOf64 (2 + z n) = 2 + z n then 1 else 0
  c01 + c02 + c03 + c04 + c05 + c06 + c07 + c08 + c09 + c10 +
  c11 + c12 + c13 + c14 + c15 + c16 + c17 + c18 + c19 + c20

end HornTorusELF
