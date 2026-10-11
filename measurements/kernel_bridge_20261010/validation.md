# Hosted kernel wiring verification, 2026-10-10

Release builds of Vox and G-mOMonadOS completed successfully.

The bridge regression checks passed on both primary executables: native tables for every lattice operation, certified Y reduction and kernel re-entry, large-tick negation cycles, runtime word-table bounds and closure, nonmonotone seed handling, invalid input rejection, and rejection when the kernel checkout is unavailable.

Supplemental checks passed for both orders of retention/injection composition. Vox payload output remained free of admission diagnostics. The final G release passed the direct REPL, Vox alias and p4ra alias checks; the captured output is in `repl.log`.

The phase interpreter tests passed, including existing deposit/frame behavior and the exhaustive native coordinate test. These checks concern the carrier and bridge scope described in `../../bridge/README.md`.

Reproduce the hosted regression checks with `python3 bridge/check.py` from the p4rakernel checkout, after building both sibling release executables. Reproduce interpreter checks with `cargo test --lib phase_word::tests` in Vox.
