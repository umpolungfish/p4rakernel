# Perron remaining Lean bundle

This bundle adds the final assembly layer to the existing `Imscribing` development.

## Files added

- `PerronPositiveLimit.lean`: convergence of positive-height truncations along dyadic heights from the established block estimate.
- `PerronFiniteInversion.lean`: finite Dirichlet-polynomial Perron inversion from individual normalized-kernel limits.
- `PerronExplicitFormulaAssembly.lean`: integration of a finite pointwise explicit formula and integration-by-parts of each zero term.
- `PerronCompletion.lean`: combines the finite Perron inversion and integrated explicit-formula assembly in one theorem.
- `PerronBuildAll.lean`: umbrella import for the existing and newly added modules.
- `BUILD_PERRON_REMAINING.sh`: installs the files into `Imscribing/` and runs the single umbrella build.

## Run

From the project root, place the bundle files in the project root, then run:

```bash
bash BUILD_PERRON_REMAINING.sh
```

Equivalent direct command after copying the files:

```bash
lake build Imscribing.PerronBuildAll
```

The master theorem is `Imscribing.perron_and_explicit_formula_assembly`. It takes the pointwise normalized Perron-kernel limits and the pointwise truncated contour formula as explicit inputs, then proves the finite-sum Perron limit and the integrated zero-sum identity together.
