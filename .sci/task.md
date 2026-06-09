SUGGESTED TASK: Milestone P6 audit/prove the free-module chain-integration bridge.

Objective: make one upstream source-level move exposed by the accepted
blueprint map: attack

```lean
JacobianChallenge.Blueprint.Sec03.singularChain_integration_from_simplex
```

in `Jacobian/Blueprint/Sec03/PeriodHomologyInvariance.lean`.

Current state: Chapter 06 now maps #227 through the nonzero chain-level period
functional provider. In Lean, sub-leaf A.1 already constructs a per-simplex
functional using `pathIntegralViaCover`, but sub-leaf A.2
`singularChain_integration_from_simplex` still returns `0` while its comment says
it should extend the per-simplex functional to singular 1-chains by the
free-module universal property. This is the first precise upstream placeholder
to attack before replacing the zero `periodPairing`.

Scope:
- Edit `Jacobian/Blueprint/Sec03/PeriodHomologyInvariance.lean`.
- Read Mathlib singular-chain/free-abelian APIs and nearby path-integral files
  as needed.
- Update `tex/sections/06-periods-and-riemann-bilinear.tex` and
  `sorries.jsonl` only if the provider boundary or blueprint wording changes.
- Do not edit `Jacobian/Challenge.lean`.
- Do not edit the final #227 theorem in `Jacobian/Periods/PeriodFunctional.lean`
  unless a small import/comment adjustment is strictly required.
- Do not claim #227 is discharged.

Implementation target:
- Inspect the concrete representation/API of `SingularOneChain X`.
- If Mathlib exposes the needed generator/free-module extension API, prove a
  chain-level integration map extending the per-simplex functional, replacing
  the zero witness in `singularChain_integration_from_simplex`.
- If the API is not locally available, introduce the narrowest named
  generator-agreement/free-module-extension provider and prove
  `singularChain_integration_from_simplex` sorry-free from it.
- Keep the task limited to A.2. Do not attempt Stokes boundary killing,
  nonzero period-pairing descent, or the final period-pairing kernel provider.
- Do not introduce `axiom`, `unsafe`, or a broad replacement `sorry`.

Verification:
- Run `lake build Jacobian.Blueprint.Sec03.PeriodHomologyInvariance`.
- Run `lake build Jacobian.Periods.PeriodFunctional`.
- Run `lake build Jacobian.Solution`.
- Run `python3 scripts/list-sorries.py --text`.
- If blueprint or root tracking changes, run `python3 scripts/blueprint_audit.py`
  and `bash scripts/build-blueprint.sh`.

Checklist:
- [x] Inspect the `SingularOneChain` representation and available Mathlib
      extension API.
- [x] Prove A.2 directly, or add the exact missing A.2 provider and prove the
      old wrapper from it.
- [x] Keep the final #227 API and downstream assemblies unchanged.
- [x] Run the required Lean builds and sorry scan.
- [x] Refresh blueprint/ledger only if the provider boundary changes.
- [x] Commit the scoped edit and set `.sci/status-line` to
      `READY: Chapter 06 P6 chain-integration free-module bridge`.
