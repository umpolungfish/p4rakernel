# One Closure Law, Six Substrates — crystal

Everything the paper claims, in a form you can build and run. Nothing here cites
another manuscript.

## Building

```
cargo install --path .
./build_corpus.sh          # 13 functions x 5 optimisation levels x 2 widths
```

## Claim to command

| Paper claim | Command | What it prints |
|---|---|---|
| the lift executes, agreeing with native | `vox run gcd --args 1071,462 corpus_O0.so` | the answer native returns, with the step count in the twelve |
| ...at both widths and every optimisation level | `./build_corpus.sh` then run each | 130 pairs, no disagreement |
| the decoder refuses what it cannot read | `vox <a non-x86 binary>` | the architecture, named, and a refusal |
| six substrates, one law | `vox <elf>` · `vox evm HEX` · `vox wasm HEX` · `vox pyc F.pyc` · `vox rna SEQ` | a word and a verdict from each |
| structure costs ~6%, lossless ~40% | `python3 measure.py /bin/ls` | coverage, structure, operands, lossless, shrink |
| an open fork is exit arithmetic | `vox self` | surplus against exit count, and the residual ranking |
| the instrument reads itself | `vox self` | every function by descent, F = 0 |
| the verdict rule itself | `vox verdict <glyph-word>` | T, B, N or F |

`vox --selftest` runs planted open and closed forks on x86, EVM and WASM.

## What is NOT claimed

No binary round-trips byte-identical, and none is claimed to. The classifier
ends in a catch-all, so the map is many-to-one and has no inverse. What closes is
the word: each leg is a retraction, identity on the image of the section and
nowhere else. The structure column of the measurement is a lossy lift and is not
a compression ratio; the lossless column is the compression claim.
