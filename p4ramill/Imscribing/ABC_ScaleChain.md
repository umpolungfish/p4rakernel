# Finite scale chains

`ABC_ScaleChain.lean` composes the pairwise scale links into a reusable
`ScaleChain`. The chain records increasing window indices and one certified
enclosure at each index. Its `cross_bound` theorem carries an earlier lower
endpoint into every later upper endpoint, and `scaleLink_trans` makes the
Closure transitive.

`certifiedTwoScale` instantiates the chain at indices 7 and 30, corresponding
to the certified c≤9 and c≤32 readings. `certifiedTwoScaleWitness` packages
the resulting lower reading at the first scale and its later cross-scale
closure as a held Witness, classified B.

Validation: Lake build passed at 8046 jobs. Vox reports T=7, B=5, N=56,
F=0 and 100% coverage of 1,821 code bytes. Report:
`/tmp/abc-scale-chain-vox/audit.txt`.
