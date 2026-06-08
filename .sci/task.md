COMPLETED TASK: Split #227 to the functional period-pairing kernel provider.

Objective: replace the direct reachable PeriodFunctional frontier
`h1_basis_periodMatrix_realKernel_trivial` with the strictly narrower
functional statement:

```lean
h1_basis_periodPairing_realKernel_trivial
```

What changed:
- Added `h1_basis_periodPairing_realKernel_trivial` as the direct Type-0 #227
  provider.
- Proved `h1_basis_periodMatrix_realKernel_trivial` sorry-free by transporting
  a vanishing real linear combination through
  `(holomorphicOneFormDualEquiv ℂ X).restrictScalars ℝ`.
- Kept `h1_basis_periodCoordinate_linearIndependent`,
  `h1_basis_riemannClassicalPeriodBasis`, and
  `riemann_classical_real_LI_input` as sorry-free assemblies from the provider.
- Updated Chapter 06 so the blueprint node points at
  `h1_basis_periodPairing_realKernel_trivial`.
- Refreshed `sorries.jsonl`; the direct blueprint/provider row is now the
  functional kernel, while the period-matrix and period-coordinate theorems are
  dependency rows.

Verification:
- [x] `lake build Jacobian.Periods.PeriodFunctional`
- [x] `lake build Jacobian.Periods.PeriodVectorsLIU`
- [x] `lake build Jacobian.Solution`
- [x] `python3 scripts/list-sorries.py --text`
- [x] `python3 scripts/blueprint_audit.py`
- [x] `bash scripts/build-blueprint.sh`
- [x] `rg -n "\\baxiom\\b|unsafe|sorry" Jacobian/Periods/PeriodFunctional.lean`

Result:
- #227 is not mathematically discharged yet. The remaining root is now the
  minimal functional-kernel provider blocked by the current zero
  `periodPairing` scaffold and the absent chain-level integration /
  classical Stokes-Hodge input.
