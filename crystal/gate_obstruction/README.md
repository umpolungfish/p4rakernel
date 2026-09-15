# The S and T Gates Are Not in the Braid Image — crystal

The paper's obstruction is arithmetic and its proof is in Lean; the kernel is
where you watch the obstruction bite. Nothing here refers to another manuscript.

## Booting

The instantiation is part of the mOMonadOS bare-metal kernel
(`https://github.com/umpolungfish/momonad_os`) at the commit in `MANIFEST.txt`.
Build for `x86_64-unknown-none` and run:

```
./run_serial_cmds.sh "fibqc verify"     # the lattice the gates have to land on
./run_serial_cmds.sh "bi 1 2 1"         # a braid word and the winding it carries
./run_serial_cmds.sh "qc H T 8"         # compile a circuit and watch T never close
./run_serial_cmds.sh "qc draw HTSX 10"  # the compiled word, drawn
```

## Claim to verb

| Paper claim | Where it runs | What it prints |
|---|---|---|
| every phase native to the model is a multiple of a tenth of a winding | `fibqc verify` | `Phase lattice = tenths of a winding: PASS` |
| a braid word of exponent sum e has determinant of winding -e/10 | `bi <generators>` | the word's image and its winding |
| Z is realized outright | `bi 1 1 1 1 1` | sigma_1^5, landing on the lattice |
| T and S are not, so compilation is approximation | `qc H T <depth>` | the Solovay-Kitaev word and its residual, stopping rather than closing |
| the residual has a floor, not a tail | `qc H T <depth>` at rising depth | the residual settling instead of falling |

The compile verb stops early rather than refusing, and says which limit it hit:
the net outgrowing the arena, or the recursion outgrowing the next level's word.
That distinction matters here, because the paper's claim is that no finite braid
word lands on T exactly, and a compiler that silently truncated would look the
same as one that had converged.
