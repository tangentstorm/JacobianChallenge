SUGGESTED TASK: Milestone P0 audit the current #227 provider boundary.

Objective: start the issue #227 execution assignment by auditing the current
reachable Type-0 provider in `Jacobian/Periods/PeriodFunctional.lean`:

```lean
h1_basis_periodCoordinate_linearIndependent
```

The original `riemann_classical_real_LI_input` issue has already been made
honest by requiring `RiemannClassicalPeriodBasis`; the remaining root is the
basis-specific period-coordinate nondegeneracy provider. This first step should
decide whether the current scaffold can prove that provider directly, or name
the exact smaller classical input still missing.

Scope:
- Work primarily in `Jacobian/Periods/PeriodFunctional.lean`.
- Read the local declarations around:
  - `RiemannClassicalPeriodBasis`
  - `h1_basis_periodCoordinate_linearIndependent`
  - `h1_basis_riemannClassicalPeriodBasis`
  - `riemann_classical_real_LI_input`
  - `riemann_bilinear_identity`
  - `periodPairing_satisfies_bilinear_identity`
  - `hodge_form_posDef_on_periods`
  - `RiemannBilinearRefinement.real_linearIndependent_of_quadratic_pos_def`
- Do not edit `Jacobian/Challenge.lean`.
- Do not edit jc2/jc3/jc4/jc5 active files.
- Do not try to solve the entire Riemann-bilinear theorem in this first commit.
- If the exact missing statement is clear, add only a narrowly scoped provider
  name/comment or tiny structural split, then prove any surrounding assembly
  sorry-free.
- Preserve downstream APIs where possible, especially
  `riemann_classical_real_LI_input`, `periodVectors_linearIndependent`, and
  the universe-`u` mirror.

Verification:
- Run `lake build Jacobian.Periods.PeriodFunctional`.
- Run `lake build Jacobian.Periods.PeriodVectorsLIU`.
- Run `lake build Jacobian.Solution`.
- Run `python3 scripts/list-sorries.py --text` and record whether #227 is still
  rooted at `h1_basis_periodCoordinate_linearIndependent` or a narrower provider.
- Run `rg -n "\\baxiom\\b|unsafe|sorry" Jacobian/Periods/PeriodFunctional.lean`
  and confirm no new axiom/unsafe declarations and no accidental new broad
  sorry.
- Commit exactly the scoped SCI/Lean edit with normalized author/committer
  metadata and `Co-authored-by: Codex <codex@openai.com>`.

Checklist:
- [ ] Inspect the current Type-0 provider and downstream consumers.
- [ ] Decide whether existing substrate proves the provider directly.
- [ ] If not direct, identify the narrowest missing classical provider.
- [ ] Make only the scoped P0 edit needed to record or isolate that boundary.
- [ ] Run `lake build Jacobian.Periods.PeriodFunctional`.
- [ ] Run `lake build Jacobian.Periods.PeriodVectorsLIU`.
- [ ] Run `lake build Jacobian.Solution`.
- [ ] Run `python3 scripts/list-sorries.py --text`.
- [ ] Run the PeriodFunctional axiom/unsafe/sorry scan.
- [ ] Commit the scoped edit and set `.sci/status-line` to
      `READY: Chapter 06 P0 #227 provider boundary audit`.
