# Published smooth-extension proof

Adapted from https://github.com/openai/NavierStokesAndEuler at commit `f9e8bc5b38b6e212696e8a30e3e91517af887bbd`.
Original files: `NavierStokes/{SmoothCutoffs,DiagonalScale,BorelExtension,SpatialBorelExtension,GenericEndpointExtension}.lean`.
License: Apache-2.0, reproduced in LICENSE. Original namespaces are retained.

Local compatibility changes for Lean/Mathlib 4.28:
- Import paths now use `Imscribing.PublishedNS`.
- `Mathlib.Analysis.Real.Sqrt` becomes `Mathlib.Analysis.SpecialFunctions.Sqrt`.
- `ite_eq_left/right` becomes `if_pos/neg`.
- A finite smoothness comparison uses the explicit `nat_le_infty 2` lemma.
- Zero within-derivatives are proved by induction using constant derivatives.

No axiom, sorry, or assumed extension was introduced. These five files prove
the generic analytic extension step. The upstream profile construction and
its cancellation certificates are available in the local research checkout;
they are not dependencies of this adaptation.
