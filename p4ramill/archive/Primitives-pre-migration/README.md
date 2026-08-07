# Pre-migration `Primitives/` tree

This directory is a duplicate of `Imscribing/Primitives/` that stopped being built
at some point before the alphabet migration and then stopped being updated.

It is not referenced by `lakefile.toml` (every glob there is `Imscribing.*`) and no
`.lean` file in the package imports it. It compiled against an older Grammar and
carries retired notation: its `Core.lean` writes the tier rule table with `⊙^ℂ` and
`Ω_0` where the canonical `Imscribing/Primitives/Core.lean` writes `𐑮` and `𐑷`.

It is archived rather than deleted so the pre-migration spellings stay recoverable.
Nothing here is scripture. The canonical Grammar lives in `Imscribing/Primitives/`
and in `IG_catalog.json`; if these files disagree with those, these files are wrong.
