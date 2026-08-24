/*
HornTorusRuntime.c — the seven Lean runtime primitives HornTorusELF.c references,
provided in-image so V⊙x can lift and follow every call (no external PLT targets).
Semantics identical to the Lean runtime; -Bsymbolic binds the calls locally.
Author: Quantum⊙perator · 2026-08-24
*/
#include <stdint.h>

uint64_t lean_uint64_add(uint64_t a, uint64_t b) { return a + b; }
uint64_t lean_uint64_sub(uint64_t a, uint64_t b) { return a - b; }
uint64_t lean_uint64_land(uint64_t a, uint64_t b) { return a & b; }
uint64_t lean_uint64_shift_left(uint64_t a, uint64_t b) { return a << b; }
uint64_t lean_uint64_shift_right(uint64_t a, uint64_t b) { return a >> b; }
uint8_t lean_uint64_dec_eq(uint64_t a, uint64_t b) { return a == b; }
uint8_t lean_uint64_dec_lt(uint64_t a, uint64_t b) { return a < b; }
