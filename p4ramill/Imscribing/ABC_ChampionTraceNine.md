# Certified champion trace through height 9

`ABC_ChampionTraceNine.lean` constructs `certifiedChampionTraceNine` at
epsilon 1/10. The initial champion is (1,1,2); (1,8,9) displaces it at height 9.
`champion_base_through_eight` establishes the exact maximum at every earlier
window, and `champion_at_nine` establishes attainment at height 9.
`displacement_through_nine_iff` characterizes all strict displacements in this
prefix: the only one is window index 7.

Lean window index N means c <= N+2. `ChampionEvent.heightCutoff` exposes the
Rust convention, and `certifiedChampionTraceNine_height_cutoffs` checks [2,9].
Initialization is retained as the first event, with no predecessor. Later
events record the preceding window maximum and a strict increase. Traces
require ordered events, predecessor links, and constancy between events.
The champion's packet calibrations and exact reading are retained together
by `ChampionEvent.witness`; `certifiedChampionTraceNineWitness` holds the
complete displacement characterization and the cutoff correspondence.

Exact comparisons are supplied by `ABC_ChampionNineBounds.lean`, reproducible
with `python3 scripts/abc_emit_champion_nine.py`. It reuses the rational
logarithm enclosure generator and exhaustively covers the coprime triples
through c=9, using summand-exchange symmetry. Equality cases use reflexivity;
comparisons between different readings use disjoint rational enclosures.
Both summand orders can attain the same maximum; uniqueness is not asserted.

Validation: `lake build Imscribing.ABC_ChampionTraceNine` completed successfully
(8057 jobs). The Rust debug command `abc champions --json 0.1 9` returned the
same cutoffs and triples. Vox audited the compiled trace shared object at
`.lake/build/vox_native/champion_nine/trace.so`: T=9, B=5, N=91, F=0, covering
3053/3053 executable bytes. That is the control-flow audit of this module;
Lean checks the arithmetic proof fields before compilation erases them.

The declaration audit lists only `propext`, `Classical.choice`, and
`Quot.sound`, with no `sorryAx`. Both event Witnesses and the trace Witness
evaluate to `(true, true)`. Audit logs are saved alongside the ELF as
`axioms.txt` and `vox.txt`.
