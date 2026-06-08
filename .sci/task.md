SUGGESTED TASK: Milestone C1 map the de Rham/Hodge exactness frontier #242/#243.

Objective: complete the Chapter-06 Cluster C blueprint map by refining
`input:hodge-deRham` so it exposes exactly the two genuine remaining
exactness frontiers:

- #242 `deRhamComparisonMap1_zero_period_primitiveExists_provider`, the
  zero-period closed-form primitive-existence input.
- #243 `hodgeRemainder_periodPayload_exact`, the Hodge remainder period-payload
  exactness input.

Scope:
- Re-read `tex/sections/06-periods-and-riemann-bilinear.tex` around
  `input:hodge-deRham` and the two Cluster C open nodes.
- Re-read the relevant Lean declarations in:
  - `Jacobian/HolomorphicForms/DeRhamComparisonMap.lean`, especially the
    zero-period kernel, primitive-to-exact, comparison-kernel, and
    path-integral primitive assembly declarations around
    `deRhamComparisonMap1_zero_period_primitiveExists_provider`.
  - `Jacobian/HolomorphicForms/HodgeProjection.lean`, especially
    `hodgeRemainder_periodPayload_exact`,
    `harmonicProjection1_hodgeDecomposition`, and
    `harmonicProjection1_kernel_subset_exact`.
- Add compact blueprint nodes for the surrounding sorry-free assemblies already
  present in Lean, such as:
  - zero period `=>` comparison-kernel membership and back,
  - primitive existence `=>` exactness,
  - comparison-kernel exactness/vanishing wrappers,
  - path-integral primitive packaging,
  - harmonic projection embedding/decomposition wrappers,
  - zero harmonic projection `=>` exactness assembly.
- Wire `input:hodge-deRham` through these assemblies so the graph bottoms out in
  #242 and #243 plus named green project substrate nodes or honest
  classical/Mathlib citations.
- Keep #242 and #243 unmarked by proof-level `\\leanok`; do not mark any direct
  `sorry` declaration green.
- Do not edit Lean proof files and do not touch `Jacobian/Challenge.lean`.

Verification:
- Confirm every new `\\lean{}` declaration exists.
- Confirm every new green node is absent from `sorries.jsonl` as a `c:"sorry"`
  row, or otherwise justified as sorry-free by the refreshed graph.
- Run `python3 scripts/blueprint_audit.py`.
- Run `bash scripts/build-blueprint.sh` and include any generated
  `sorries.jsonl` update if the build changes it.
- Update `.sci/result.md` with the final C1 frontier map and the next V1/V2/V3
  recommendation.

Checklist:
- [x] Inspect the current C nodes in Chapter 06 and the relevant Lean
      declarations.
- [x] Add green blueprint nodes for the de Rham zero-period assembly substrate.
- [x] Add green blueprint nodes for the Hodge projection/exactness assembly
      substrate.
- [x] Wire `input:hodge-deRham`, #242, and #243 so only the genuine frontier
      leaves remain open.
- [x] Verify new declarations and green/open status.
- [x] Run `python3 scripts/blueprint_audit.py`.
- [x] Run `bash scripts/build-blueprint.sh`.
- [x] Stage any generated `sorries.jsonl` update from the build.
- [x] Update `.sci/result.md` with C1 findings and V-milestone recommendation.
- [x] Commit the tex/result/task/sorries updates and set `.sci/status-line` to
      `READY: Chapter 06 C1 de Rham/Hodge frontier wiring`.
