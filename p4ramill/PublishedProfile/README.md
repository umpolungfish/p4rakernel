# Published-profile injection bridge

These canonical sources are checked from the local upstream checkout at
`/home/mrnob0dy666/imsgct/research/NavierStokesAndEuler`, using its pinned
Lean 4.34.0-rc2 toolchain and dependencies. Lake's relative `srcDir` imports this
directory and the local `Imscribing` sources without copying them.

The reference upstream revision is
`f9e8bc5b38b6e212696e8a30e3e91517af887bbd` from
<https://github.com/openai/NavierStokesAndEuler>.

- `OperatorConnection.lean` identifies the local differential residual with
  the upstream residual, using the Cartesian transport theorem from
  `Imscribing/NS_DifferentialConvention.lean`. This target passes its
  upstream check and reports only `propext`, `Classical.choice`, `Quot.sound`.
- `InjectionConnection.lean` identifies the carried injection with the
  force in a candidate certificate, then selects the published actual
  candidate to obtain an existence theorem with no analytic hypotheses.
- `ProfileAudit.lean` audits the selected cancellation schedule, assembled
  endpoint witness, actual candidate and local bridge together.

From the upstream checkout:

```sh
lake build OperatorConnection InjectionConnection
lake build ProfileAudit
```

The smooth continuation is the force. The candidate certificate retains
the velocity's unbounded speed at time one. The conventional exposition
is `/home/mrnob0dy666/imsgct/ig-docs/ns_reentry_injection.md`.
