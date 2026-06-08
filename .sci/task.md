SUGGESTED TASK: Milestone B3 start execution Phase 2 with #227 `riemann_classical_real_LI_input`.

Objective: make the first commit-sized proof step on the jc1-owned Riemann
bilinear / period-rank cluster by narrowing or discharging the keystone theorem
`riemann_classical_real_LI_input` in
`Jacobian/Periods/PeriodFunctional.lean`.

Context:
- `.sci/plan.md` now has Phase 2 Milestone B3 for this commit-sized #227 step.
- Phase 1 planning is complete. The final split in `.sci/result.md` assigns
  jc1 #227, #241, and #240, with #227 strictly before #241.
- #227 currently states real linear independence of the period functionals for
  an arbitrary injective family `σ : Fin (2 * analyticGenus ℂ X) →
  IntegralOneCycle X`.
- The existing comment in `PeriodFunctional.lean` says the statement needs
  `σ` to be a canonical/symplectic homology basis and needs Stokes on the
  fundamental polygon to identify the period sum with the positive Hodge form.

Scope:
- Work only in `Jacobian/Periods/PeriodFunctional.lean` unless a tiny local
  helper in the same `Jacobian/Periods/` ownership area is unavoidable.
- Do not touch `Jacobian/Challenge.lean`.
- Do not touch files assigned to jc2 or jc3.
- Inspect the already-mapped substrate:
  - `periodPairing_satisfies_bilinear_identity`
  - `hodge_form_posDef_on_periods`
  - `RiemannBilinearRefinement.real_linearIndependent_of_quadratic_pos_def`
  - the exact statement and consumers of `riemann_classical_real_LI_input`
- Determine whether #227 can be proved from the current hypotheses. If the
  current arbitrary-injective `σ` statement is too strong, replace the single
  broad `sorry` with the narrowest honest local provider(s) needed for the
  canonical/symplectic-basis and Stokes/Hodge-positivity inputs, preserving the
  public theorem's API where possible.
- Do not introduce new broad axioms or unrelated theory. Any new placeholder
  must be strictly narrower than #227 and named for the precise missing input.

Verification:
- Run `lake build Jacobian.Periods.PeriodFunctional`.
- Run `lake build Jacobian.Solution`.
- Confirm `scripts/list-sorries.py --text` shows #227 has either been proved or
  replaced by strictly narrower named provider(s), without increasing unrelated
  reachable sorries.
- Commit the Lean/task updates and set `.sci/status-line` to
  `READY: Chapter 06 #227 Riemann bilinear keystone step`.

Checklist:
- [x] Inspect #227, its consumers, and the mapped substrate declarations.
- [x] Decide whether the current #227 statement is provable as stated or needs
      a narrower provider split.
- [x] Implement the smallest proof or provider split in the assigned file.
- [x] Run `lake build Jacobian.Periods.PeriodFunctional`.
- [x] Run `lake build Jacobian.Solution`.
- [x] Run `python3 scripts/list-sorries.py --text` and record the reachable
      sorry effect.
- [x] Commit the changes and set `.sci/status-line` to
      `READY: Chapter 06 #227 Riemann bilinear keystone step`.
