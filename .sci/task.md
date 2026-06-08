SUGGESTED TASK: Milestone B4 port the #227 Riemann-bilinear split to #241 `riemann_classical_real_LI_inputU`.

Objective: make the universe-`u` period-rank theorem #241 mirror the accepted
Type-0 #227 split, so `riemann_classical_real_LI_inputU` is no longer a broad
direct arbitrary-injective `sorry`.

Context:
- `.sci/plan.md` now has Phase 2 Milestone B4 as the next unchecked jc1-owned
  step.
- B3 introduced `RiemannClassicalPeriodBasis` and the basis-specific provider
  `h1_basis_riemannClassicalPeriodBasis` in
  `Jacobian/Periods/PeriodFunctional.lean`.
- `Jacobian/Periods/PeriodVectorsLIU.lean` still has #241
  `riemann_classical_real_LI_inputU` as a direct `sorry` with only
  arbitrary-injective hypotheses.

Scope:
- Work primarily in `Jacobian/Periods/PeriodVectorsLIU.lean`.
- If needed, add only tiny local universe-`u` helper declarations in the
  `Jacobian/Periods/` ownership area.
- Do not touch `Jacobian/Challenge.lean`.
- Do not touch jc2/jc3-owned files.
- Mirror the accepted Type-0 shape:
  - introduce a universe-`u` classical period-basis predicate or provider,
    tied to the `h1_basis_of_compact_riemann_surfaceU` / `symplectic_basis_of_cyclesU`
    basis witness rather than arbitrary injectivity;
  - make `riemann_classical_real_LI_inputU` consume that explicit witness and
    become a sorry-free transport/assembly;
  - thread the witness through `period_functionals_ℝ_linearIndependentU`,
    `period_vectors_linearIndependent_of_symplecticU`, and
    `periodVectors_linearIndependentU`.
- Preserve public downstream APIs where possible; any remaining placeholder must
  be strictly narrower than #241 and named for the precise universe-`u`
  basis/nondegeneracy input.

Verification:
- Run `lake build Jacobian.Periods.PeriodVectorsLIU`.
- Run `lake build Jacobian.Solution`.
- Run `python3 scripts/list-sorries.py --text` and confirm #241 has moved from
  a direct broad sorry to the narrower universe-`u` provider.
- Run `bash scripts/build-blueprint.sh` if `sorries.jsonl` needs graph refresh.
- Commit the Lean/task/result/sorries updates and set `.sci/status-line` to
  `READY: Chapter 06 B4 universe Riemann bilinear port`.

Checklist:
- [x] Inspect #241, its consumers, and the Type-0 B3 provider split.
- [x] Add the universe-`u` classical period-basis predicate/provider.
- [x] Thread the explicit witness through the universe-`u` period-rank chain.
- [x] Run `lake build Jacobian.Periods.PeriodVectorsLIU`.
- [x] Run `lake build Jacobian.Solution`.
- [x] Run `python3 scripts/list-sorries.py --text` and record the reachable
      sorry effect.
- [x] Refresh `sorries.jsonl` with `bash scripts/build-blueprint.sh` if needed.
- [x] Commit the changes and set `.sci/status-line` to
      `READY: Chapter 06 B4 universe Riemann bilinear port`.
