# Asymptotic Closure

`ABC_AsymptoticClosure.lean` makes the limit reading a first-class object.
`AsymptoticClosure ε` consists of a finite real limit and a convergence field
for the exact exhaustive window maximum at that ε. From it Lean derives a
global discrepancy bound and proves every finite maximum lies below the limit.

`AsymptoticClosure.to_conjecture` consumes one such Closure object for every
positive ε and produces the arithmetic statement. `asymptoticWitness` retains
that arithmetic extraction alongside the equivalent uniform spectral bound,
with a B classification.

The finite scale chain feeds this object through
`asymptotic_lower_contains_finite`: every certified finite lower reading lies
below the asymptotic limit. The limit field is the actual Closure datum; it
is not inferred from finitely many windows.

Validation: Lake build passed at 8047 jobs. Vox reports T=8, B=5, N=62,
F=0 and 100% coverage of 1,974 code bytes. Report:
`/tmp/abc-asymptotic-vox/audit.txt`.
