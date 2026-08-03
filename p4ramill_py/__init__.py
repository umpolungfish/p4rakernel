"""
p4ramill_py — Python mirror of the p4ramill Lean 4 kernel.

Provides Belnap four-valued logic and the paraconsistent machine kernel,
mirroring Imscribing/Paraconsistent/{Belnap,Kernel}.lean.

Restored 2026-08-03. A notation sweep on 2026-07-14 deleted this package
wholesale while retiring the gen-2 glyph-pair spellings; it had been deleted
once before by the same kind of sweep and put back the next day. Nothing was
lost, because the code had been copied on to red-hot_rebis/rhr_p4rky and
carried forward there, and these two modules come from that copy. What the
deletion did break was priests-engine, which imports the Belnap foundation from
here by design and had been unable to load since.

Only belnap and kernel are restored. The rest of what the sweep removed —
machine, the genetic pipeline, and the ob3ects — is still in rhr_p4rky and in
ob3ect/ and is not needed at this seam.
"""
