SUGGESTED TASK: Milestone B5 narrow #240 `h1_basis_of_compact_riemann_surfaceU`.

Objective: address the remaining jc1-owned universe-`u` H₁-basis obligation in
`Jacobian/Periods/H1BasisU.lean` by either discharging
`h1_basis_of_compact_riemann_surfaceU` or replacing its broad direct `sorry`
with the narrowest named provider for the actual universe-`u`
surface-classification / cellular-homology input.

Context:
- `.sci/plan.md` has B3 and B4 accepted. B5 is the next unchecked
  Riemann-bilinear / period-rank milestone.
- #240 currently states that `IntegralOneCycleU X` admits a
  `Module.Basis (Fin (2 * analyticGenus ℂ X)) ℤ`.
- The Type-0 analogue is `h1_basis_of_compact_riemann_surface` in
  `Jacobian/Periods/PeriodFunctional.lean`, proved by assembling the
  surface-classification / polygonal H₁ basis chain.
- `H1BasisU.lean` documents why the universe-`u` object is not a cheap reuse of
  the Type-0 basis: `IntegralOneCycleU X` uses the universe-`u`
  singular-homology functor with `ULift.{u} ℤ` coefficients.

Scope:
- Work primarily in `Jacobian/Periods/H1BasisU.lean`.
- Read the Type-0 proof in `Jacobian/Periods/PeriodFunctional.lean` and the
  underlying declarations in `Jacobian/Periods/SurfaceClassification.lean`,
  `Jacobian/Periods/Polygon4gCellular.lean`, and
  `Jacobian/Periods/IntegralOneCycleU.lean`.
- Do not touch `Jacobian/Challenge.lean`.
- Do not touch jc2/jc3-owned files (`TietzeReduction.lean`,
  `HandleSwapHomeo.lean`, StableChartAt reroute files).
- First attempt a direct universe-`u` assembly if existing local substrate is
  enough.
- If the universe-`u` surface-classification/cellular bridge is still genuinely
  missing, replace the single broad #240 `sorry` with a strictly narrower,
  named provider tied to that precise missing bridge, then prove
  `h1_basis_of_compact_riemann_surfaceU` from the provider.
- Preserve downstream APIs where possible, especially callers in
  `PeriodVectorsLIU.lean` and period lattice `U` files.

Verification:
- Run `lake build Jacobian.Periods.H1BasisU`.
- Run `lake build Jacobian.Periods.PeriodVectorsLIU` to verify the B4 consumers.
- Run `lake build Jacobian.Solution`.
- Run `python3 scripts/list-sorries.py --text` and confirm #240 is either
  discharged or moved to a narrower named provider.
- Run `bash scripts/build-blueprint.sh` if `sorries.jsonl` needs graph refresh.
- Run `python3 scripts/blueprint_audit.py` if the blueprint/sorry graph is
  refreshed.
- Commit the Lean/task/result/sorries updates and set `.sci/status-line` to
  `READY: Chapter 06 B5 universe H1 basis split`.

Checklist:
- [x] Inspect #240, its consumers, and the Type-0 H₁-basis proof chain.
- [x] Decide whether existing universe-`u` substrate can prove #240 directly.
- [x] Implement the direct proof or the narrowest provider split in
      `H1BasisU.lean`.
- [x] Run `lake build Jacobian.Periods.H1BasisU`.
- [x] Run `lake build Jacobian.Periods.PeriodVectorsLIU`.
- [x] Run `lake build Jacobian.Solution`.
- [x] Run `python3 scripts/list-sorries.py --text` and record the reachable
      sorry effect.
- [x] Refresh `sorries.jsonl` with `bash scripts/build-blueprint.sh` if needed.
- [x] Run `python3 scripts/blueprint_audit.py` if the graph was refreshed.
- [x] Commit the changes and set `.sci/status-line` to
      `READY: Chapter 06 B5 universe H1 basis split`.
