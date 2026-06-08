SUGGESTED TASK: Milestone B6 narrow or discharge `h1_basis_riemannClassicalPeriodBasis`.

Objective: address the remaining Type-0 Riemann-bilinear direct provider in
`Jacobian/Periods/PeriodFunctional.lean`, either proving
`h1_basis_riemannClassicalPeriodBasis` from the existing substrate or replacing
it with the narrowest named provider for the actual missing
symplectic-basis/Stokes/Hodge-positivity input.

Context:
- B3 replaced broad #227 `riemann_classical_real_LI_input` with
  `RiemannClassicalPeriodBasis` plus the basis-specific provider
  `h1_basis_riemannClassicalPeriodBasis`.
- B4 ported the split to universe-`u`, and B5 split #240 into narrower H₁
  universe providers.
- `python3 scripts/list-sorries.py --text` still reports
  `h1_basis_riemannClassicalPeriodBasis` as a reachable direct sorry in
  `PeriodFunctional.lean`.
- This provider is now the Type-0 Riemann-bilinear period-coordinate
  nondegeneracy frontier, tied to a concrete `Module.Basis` of
  `IntegralOneCycle X`.

Scope:
- Work primarily in `Jacobian/Periods/PeriodFunctional.lean`.
- Read the local declarations around:
  - `RiemannClassicalPeriodBasis`
  - `h1_basis_riemannClassicalPeriodBasis`
  - `riemann_bilinear_identity`
  - `hodge_form_posDef_on_periods`
  - `RiemannBilinearRefinement.real_linearIndependent_of_quadratic_pos_def`
  - `periodPairing_satisfies_bilinear_identity`
- Do not touch `Jacobian/Challenge.lean`.
- Do not touch jc2/jc3-owned files (`TietzeReduction.lean`,
  `HandleSwapHomeo.lean`, StableChartAt reroute files).
- First attempt a direct assembly if the current Hodge-positivity and
  Riemann-bilinear substrate is sufficient.
- If the provider is still genuinely missing analytic/geometric content,
  replace `h1_basis_riemannClassicalPeriodBasis` with one or more strictly
  narrower named providers that isolate the precise missing statement, then
  prove `h1_basis_riemannClassicalPeriodBasis` from them.
- Preserve downstream APIs where possible, especially
  `riemann_classical_real_LI_input`, `periodVectors_linearIndependent`, and
  the universe-`u` mirror.

Verification:
- Run `lake build Jacobian.Periods.PeriodFunctional`.
- Run `lake build Jacobian.Periods.PeriodVectorsLIU` to verify the universe
  mirror still consumes the Type-0 split cleanly.
- Run `lake build Jacobian.Solution`.
- Run `python3 scripts/list-sorries.py --text` and confirm the direct Type-0
  provider is either discharged or moved to narrower named provider(s).
- Run `bash scripts/build-blueprint.sh` if `sorries.jsonl` needs graph refresh.
- Run `python3 scripts/blueprint_audit.py` if the graph was refreshed.
- Commit the Lean/task/result/sorries updates and set `.sci/status-line` to
  `READY: Chapter 06 B6 classical period basis provider`.

Checklist:
- [x] Inspect the current Type-0 provider and its downstream consumers.
- [x] Decide whether existing substrate proves the provider directly.
- [x] Implement the direct proof or the narrowest provider split in
      `PeriodFunctional.lean`.
- [x] Run `lake build Jacobian.Periods.PeriodFunctional`.
- [x] Run `lake build Jacobian.Periods.PeriodVectorsLIU`.
- [x] Run `lake build Jacobian.Solution`.
- [x] Run `python3 scripts/list-sorries.py --text` and record the reachable
      sorry effect.
- [x] Refresh `sorries.jsonl` with `bash scripts/build-blueprint.sh` if needed.
- [x] Run `python3 scripts/blueprint_audit.py` if the graph was refreshed.
- [x] Commit the changes and set `.sci/status-line` to
      `READY: Chapter 06 B6 classical period basis provider`.
