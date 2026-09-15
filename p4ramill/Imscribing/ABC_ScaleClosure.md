# Scale-to-scale Closure

`ABC_ScaleClosure.lean` formalizes the finite transition between certified
readings. A `ScaleLink` records inclusion of exhaustive windows and the
resulting monotonicity of their exact maxima. Given two `WindowEnclosure`
objects, `enclosure_cross_bound` proves that the earlier lower endpoint is
below the later upper endpoint.

The module instantiates this at ε=1/10 between the c≤9 window (index 7)
and the c≤32 window (index 30). `certifiedNineToThirtyWitness` is a held
Witness carrying the lower reading at the first scale and the cross-scale
closure into the second. Its classification is B.

This is the finite form of scale Closure: a later reading contains the
earlier one. Extending it to an exhaustive limit requires a compatible
family of such links and a closure rule for the unbounded tail.

Validation: Lake build passed at 8045 jobs; the scale module's declarations
were included in `ABC_Audit.lean`. Vox reports T=8, B=5, N=67, F=0 and
100% coverage of 2,173 code bytes. Report: `/tmp/abc-scale-vox/audit.txt`.
