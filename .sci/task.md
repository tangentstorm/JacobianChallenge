# Worker jc0 — Milestone B1: isolate analytic-genus-zero homeomorphism provider

## Assignment

Execute the next B1 step from `.sci/plan.md`: replace the broad #233 `sorry`
in `exists_biholomorph_onePoint_of_analyticGenus_zero` with a narrower
topological-homeomorphism provider, then feed that provider to the now-upstream
#232 theorem `exists_biholomorph_onePoint_of_genus_zero`.

Introduce a named provider in
`Jacobian/HolomorphicForms/MeromorphicToBranchedCover.lean`, for example
`genusZeroHomeomorphOnePoint_of_analyticGenus_zero`, returning
`Nonempty (X ≃ₜ OnePoint ℂ)` from `analyticGenus ℂ X = 0`. Then prove
`exists_biholomorph_onePoint_of_analyticGenus_zero` by obtaining this
topological homeomorphism and applying
`exists_biholomorph_onePoint_of_genus_zero`.

This is a Lean-code commit. It should not solve the analytic-genus-zero
topological classification yet; it should make the remaining #233 frontier
strictly narrower and keep all public theorem names/signatures unchanged.

## Scope

- Edit `Jacobian/HolomorphicForms/MeromorphicToBranchedCover.lean`.
- Edit `.sci/task.md` and local ignored `.sci/plan.md` state.
- Do not edit `Jacobian/Challenge.lean`.
- Do not edit `Jacobian/HolomorphicForms/GenusZeroClassification.lean` unless a
  minimal import cleanup is forced by the build.
- Do not add more than one new `sorry`; the new topological-homeomorphism
  provider must replace the existing #233 `sorry`, not add a second reachable
  gap.
- Preserve the public theorem name and signature of
  `exists_biholomorph_onePoint_of_analyticGenus_zero`.
- Do not use the circular fixed-pole/Riemann--Roch route through
  `genusZero_pointRRSection_outside_constants_exists` or its downstream
  fixed-pole RR-section chain.

## Checklist

- [x] Confirm `.sci/plan.md` marks B1.0 complete and lists B1 as the next
      unchecked milestone.
- [x] Inspect `exists_biholomorph_onePoint_of_analyticGenus_zero` and confirm
      `MeromorphicToBranchedCover.lean` can see
      `exists_biholomorph_onePoint_of_genus_zero` through
      `GenusZeroUniformization.lean`.
- [x] Add `genusZeroHomeomorphOnePoint_of_analyticGenus_zero` with exactly one
      `sorry`, documenting it as the remaining topological classification
      provider from analytic genus zero to `X ≃ₜ OnePoint ℂ`.
- [x] Replace the body of `exists_biholomorph_onePoint_of_analyticGenus_zero`
      with sorry-free assembly from that provider and
      `exists_biholomorph_onePoint_of_genus_zero`.
- [x] Keep downstream
      `genusZero_singlePoleMeromorphicAnalyticData_nonempty` assembling through
      `exists_biholomorph_onePoint_of_analyticGenus_zero` unchanged.
- [x] Run `lake build Jacobian.HolomorphicForms.MeromorphicToBranchedCover`.
- [x] Run `lake build Jacobian.Solution`.
- [x] Run `scripts/list-sorries.py --text` and confirm the reachable #233 root
      moved from `exists_biholomorph_onePoint_of_analyticGenus_zero` to the new
      topological-homeomorphism provider, with no net new reachable sorries.
- [x] Commit exactly the scoped Lean/SCI edit with normalized author/committer
      metadata and `Co-authored-by: Codex <codex@openai.com>`.

## Verification

- `lake build Jacobian.HolomorphicForms.MeromorphicToBranchedCover`: succeeds;
  this file now has warnings at `complexSimplePolePrincipalPart_of_biholomorph_onePoint`
  and the new `genusZeroHomeomorphOnePoint_of_analyticGenus_zero` provider.
- `lake build Jacobian.Solution`: succeeds with existing `uses sorry` warnings.
- `scripts/list-sorries.py --text`: still 20 reachable sorries total; the #233
  root moved from `exists_biholomorph_onePoint_of_analyticGenus_zero` to
  `genusZeroHomeomorphOnePoint_of_analyticGenus_zero`.
