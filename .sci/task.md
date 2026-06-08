SUGGESTED TASK: Milestone P1 split #227 through a period-matrix kernel provider.

Objective: refine the current Type-0 #227 root in
`Jacobian/Periods/PeriodFunctional.lean` by replacing the direct `sorry` in

```lean
h1_basis_periodCoordinate_linearIndependent
```

with a sorry-free linear-algebra assembly from a strictly narrower classical
provider: triviality of the real kernel of the H₁-basis period matrix.

Current P0 audit result: the local scaffold cannot prove the current provider
directly. `periodPairing` is still backed by the zero chain-integration
placeholder, and the missing geometric input is the basis-aligned
Stokes/Hodge-positive period-matrix nondegeneracy for the selected integral H₁
basis. The next step should isolate that input in coefficient/kernel form and
prove the existing linear-independence theorem from it.

Scope:
- Work primarily in `Jacobian/Periods/PeriodFunctional.lean`.
- Add one narrowly named provider near
  `h1_basis_periodCoordinate_linearIndependent`, with a statement equivalent to
  the classical period-matrix real-kernel fact:
  for a concrete
  `B : Module.Basis (Fin (2 * analyticGenus ℂ X)) ℤ (IntegralOneCycle X)`,
  if real coefficients `c : Fin (2 * analyticGenus ℂ X) → ℝ` satisfy
  ```lean
  ∀ j : Fin (analyticGenus ℂ X),
    ∑ i, (c i : ℂ) *
      (holomorphicOneFormDualEquiv ℂ X ((periodPairing ℂ X) (B i))) j = 0
  ```
  then `∀ i, c i = 0`.
- Prove `h1_basis_periodCoordinate_linearIndependent` sorry-free from that
  provider using `Fintype.linearIndependent_iff`, `Finset.sum_apply`, and
  `Complex.real_smul`/basis-coordinate simplification.
- Keep `h1_basis_riemannClassicalPeriodBasis`,
  `riemann_classical_real_LI_input`, `periodVectors_linearIndependent`, and the
  universe-`u` mirror APIs unchanged.
- Do not edit `Jacobian/Challenge.lean`.
- Do not edit jc2/jc3/jc4/jc5 active files.
- Do not introduce `axiom`, `unsafe`, or a broader provider parallel to the
  current one.

Verification:
- Run `lake build Jacobian.Periods.PeriodFunctional`.
- Run `lake build Jacobian.Periods.PeriodVectorsLIU`.
- Run `lake build Jacobian.Solution`.
- Run `python3 scripts/list-sorries.py --text` and confirm #227 is rooted at
  the new period-matrix kernel provider, while
  `h1_basis_periodCoordinate_linearIndependent` is only `sorry-dep` or absent
  from the direct reachable-sorry list.
- Run `rg -n "\\baxiom\\b|unsafe|sorry" Jacobian/Periods/PeriodFunctional.lean`
  and confirm the only intended PeriodFunctional `sorry` is the new narrow
  kernel provider.
- Commit exactly the scoped SCI/Lean edit with normalized author/committer
  metadata and `Co-authored-by: Codex <codex@openai.com>`.

Checklist:
- [x] Introduce the narrow H₁-basis period-matrix real-kernel provider.
- [x] Prove `h1_basis_periodCoordinate_linearIndependent` from the provider
      without `sorry`.
- [x] Confirm downstream Type-0 API declarations remain unchanged.
- [x] Run `lake build Jacobian.Periods.PeriodFunctional`.
- [x] Run `lake build Jacobian.Periods.PeriodVectorsLIU`.
- [x] Run `lake build Jacobian.Solution`.
- [x] Run `python3 scripts/list-sorries.py --text`.
- [x] Run the PeriodFunctional axiom/unsafe/sorry scan.
- [x] Commit the scoped edit and set `.sci/status-line` to
      `READY: Chapter 06 P1 #227 period-matrix kernel split`.
