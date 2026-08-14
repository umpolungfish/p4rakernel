# Crystal: closure reads a proof — 2026-08-14

A snapshot of the KERNEL AND THE CONDITIONS at the time of proving, not only of
the source. The claim is "under these conditions, this happens", so the
conditions are part of the claim. A checkout of the source alone rebuilds against
whatever the libraries have since become, which is a different reaction.

## Conditions at the time of proving

| condition | value |
|---|---|
| date | 2026-08-14 |
| Lean toolchain | leanprover/lean4:v4.28.0 |
| Lean binary | 4.28.0, x86_64-unknown-linux-gnu, commit 7e01a1bf5c70fc6167d49c345d3bf80596e9a79b |
| Mathlib revision | 8f9d9cff6bd7 |
| Mathlib working tree | 22 files modified, ALL of them README.md, 44 inserted lines, no .lean touched — mathematically stock |
| rustc | 1.93.0-nightly (80d8f292d 2025-11-25) |
| vox revision | b4aa00e |
| vox binary | md5 969d61a14c64 |
| PARI/GP | 2.13.3 (used for the d=128 ray class computation) |
| host kernel | Linux 6.6.87.2-microsoft-standard-WSL2 |

The Mathlib line is the one that matters and the one a replicator will want
checked first. The tree is dirty, and it is dirty only in documentation.

## What was obtained under them

Build: complete, no errors, every module elaborating.

Verdicts, from `vox verdict`:

| object | verdict |
|---|---|
| identity proof (`p → p` by the hypothesis) | N |
| case analysis, both branches discharged | T |
| the same, one branch undischarged | B |
| a development that is one undischarged claim | B |
| `Imscribing.Frobenius.mu_delta_A_id` | T |
| `Imscribing.Frobenius.mu_delta_B_id` | T |

Axiom dependencies of the repaired module:

    three_ap_of_not_threeAPFree : propext, Classical.choice, Quot.sound
    erdos_problem_3_k3          : the same three, plus the named density axiom

Neither carries the axiom of unproved assertion.

## Reproducing

1. `lake build` in the mill. It should complete with no errors.
2. `lake env lean ProofLift.lean` — prints the four calibration words.
3. `lake env lean SelfNest.lean` — prints the word for the closure law's own proof.
4. Pipe any word to `vox verdict -` (the argument form will not carry a word of
   this length; that is why the stdin form exists).

## Known state, recorded rather than hidden

The corpus-wide sweep is NOT complete under these conditions. Loading every
module into one environment still fails on declarations that collide across
modules. The top-level collisions were repaired and are zero; the namespaced ones
remain and block the sweep. Verdicts above are from the modules reachable without
tripping a collision, plus the self-nest.

The instantiation on the bare-metal substrate IS done for the calibration set:
mOMonadOS carries the words and returns N T B B from its own kernel, the same
`check::word_verdict` that gates the vita trunk's speech, matching the host.

One divergence is open and is a finding rather than a nuisance. On the self-nest
word — the closure law's own proof, tens of thousands of tokens — the host auditor
returns T in about eleven milliseconds, and the on-board kernel did not return
inside ten minutes. Two implementations of ONE condition, agreeing on every small
word and differing by orders of magnitude in cost on a large one. The ancestry
pairing is the suspect: the host's is not quadratic in the token count and the
on-board one appears to be. Until that is settled, the metal reproduces the
calibration verdicts and not the nest.

## Verdicts on selected theorems, under these conditions

| theorem | verdict | reading |
|---|---|---|
| three_ap_of_not_threeAPFree | T | the case split is performed here |
| erdos_problem_3_k3 | T | the same |
| erdos_problem_3 | B | the undischarged k >= 4 case, as an open fork |
| dense_has_3ap | N | a thin wrapper over an imported theorem |
| primes_reciprocal_diverges | N | a re-export under a local name |
| Nat.le_antisymm | T | case analysis |
| Nat.add_comm | T | structural recursion with a match |
| List.reverse_reverse | N | NOT an induction: a rewrite chain delegating to a lemma |
| Nat.sub_add_cancel | N | no case analysis in the term |
| Nat.lt_irrefl | N | a single constant |

The `List.reverse_reverse` row is the one that tested the instrument rather than
confirming it. The expectation was T, since the statement is normally proved by
induction. Its proof TERM is `Eq.mpr (congrArg ...) (Eq.refl ...)`, a rewrite that
delegates the induction to a separate lemma, so N is correct and the expectation
was wrong. That is the distinction the verdict claims to draw — performing the case
analysis against delegating it — landing correctly where a reader would have
guessed otherwise.
