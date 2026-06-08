# Worker jc0 — Milestone C1.1: tighten biholomorphic pullback provider shape

## Assignment

Execute C1.1 from `.sci/plan.md`: tighten the #234 pullback provider so the
source lift is definitionally `targetLift ∘ e`, rather than an arbitrary
`sourceLift` plus a separate equality proof.

Introduce a narrower local facts structure in
`Jacobian/HolomorphicForms/MeromorphicToBranchedCover.lean`, for example
`BiholomorphOnePointSimplePolePullbackFacts`, carrying:

```lean
targetLift : OnePoint ℂ → ℂ
targetPrincipalPart : HasComplexSimplePolePrincipalPart targetLift (e P)
sourcePrincipalPart :
  HasComplexSimplePolePrincipalPart (targetLift ∘ (e : X → OnePoint ℂ)) P
```

Then add a named provider returning `Nonempty` of this facts structure with the
single remaining `sorry`. Prove
`biholomorphOnePointSimplePolePullbackData_of_biholomorph_onePoint` by obtaining
the facts and assembling `BiholomorphOnePointSimplePolePullbackData` with
`sourceLift := targetLift ∘ e` and `sourceLift_eq := rfl`.

This is a Lean-code commit. It should not solve the arbitrary-pole standard
coordinate or transport proof yet; it should make the remaining #234 frontier
strictly narrower by removing the arbitrary source-lift choice.

## Scope

- Edit `Jacobian/HolomorphicForms/MeromorphicToBranchedCover.lean`.
- Edit `.sci/task.md` and local ignored `.sci/plan.md` state.
- Do not edit `Jacobian/Challenge.lean`.
- Do not edit `Jacobian/HolomorphicForms/GenusZeroClassification.lean`.
- Preserve public theorem names and signatures, especially
  `complexSimplePolePrincipalPart_of_biholomorph_onePoint`.
- Do not add more than one new `sorry`; the new facts provider must replace the
  existing `biholomorphOnePointSimplePolePullbackData_of_biholomorph_onePoint`
  `sorry`, not add a second reachable gap.
- Do not use the circular fixed-pole/Riemann--Roch route through
  `genusZero_pointRRSection_meromorphic_getD_exists`,
  `genusZero_fixedPole_analyticRRWitness_nonempty`,
  `genusZero_fixedPole_simplePoleRRSection_nonempty`,
  `genusZero_fixedPole_rrSection_nonempty`, or
  `genusZero_pointRRSection_outside_constants_exists`.

## Checklist

- [x] Confirm `.sci/plan.md` marks C1.0 complete and lists C1.1 as the next
      unchecked milestone.
- [x] Inspect `BiholomorphOnePointSimplePolePullbackData` and the current
      `biholomorphOnePointSimplePolePullbackData_of_biholomorph_onePoint`
      provider.
- [x] Add the narrower facts structure whose source principal part is stated
      for `targetLift ∘ (e : X → OnePoint ℂ)`.
- [x] Add the named facts provider with exactly one `sorry`, documenting it as
      the remaining target-coordinate plus biholomorphic-transport frontier.
- [x] Replace the body of
      `biholomorphOnePointSimplePolePullbackData_of_biholomorph_onePoint` with
      sorry-free assembly from the facts provider and `sourceLift_eq := rfl`.
- [x] Keep `complexSimplePolePrincipalPart_of_biholomorph_onePoint` and
      downstream `singlePoleAnalyticData_of_biholomorph_onePoint` unchanged
      except for any name drift forced by the provider replacement.
- [x] Run `lake build Jacobian.HolomorphicForms.MeromorphicToBranchedCover`.
- [x] Run `lake build Jacobian.Solution`.
- [x] Run `scripts/list-sorries.py --text` and confirm the reachable #234 root
      moved from `biholomorphOnePointSimplePolePullbackData_of_biholomorph_onePoint`
      to the new facts provider, with no net new reachable sorries.
- [x] Commit exactly the scoped Lean/SCI edit with normalized author/committer
      metadata and `Co-authored-by: Codex <codex@openai.com>`.

## Verification

- `lake build Jacobian.HolomorphicForms.MeromorphicToBranchedCover`: succeeds;
  this file now has warnings at
  `biholomorphOnePointSimplePolePullbackFacts_of_biholomorph_onePoint` and the
  existing `genusZeroHomeomorphOnePoint_of_analyticGenus_zero` provider.
- `lake build Jacobian.Solution`: succeeds with existing `uses sorry`
  warnings.
- `scripts/list-sorries.py --text`: still 20 reachable sorries total; the #234
  root moved from
  `biholomorphOnePointSimplePolePullbackData_of_biholomorph_onePoint` to
  `biholomorphOnePointSimplePolePullbackFacts_of_biholomorph_onePoint`.
