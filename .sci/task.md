# Worker jc0 — Milestone C1.0: isolate biholomorphic pullback principal-part provider

## Assignment

Execute C1.0 from `.sci/plan.md`: replace the broad #234 `sorry` in
`complexSimplePolePrincipalPart_of_biholomorph_onePoint` with a narrower
explicit pullback-data provider for a target `OnePoint ℂ` simple-pole coordinate
at `e P` and its biholomorphic pullback along `e`.

Introduce a small local data structure in
`Jacobian/HolomorphicForms/MeromorphicToBranchedCover.lean` recording the
target lift on `OnePoint ℂ`, its target principal-part facts at `e P`, the
source lift on `X`, the equality saying the source lift is the target lift
composed with `e`, and the pulled-back source principal-part facts at `P`.
Then add a named provider returning `Nonempty` of this structure and prove
`complexSimplePolePrincipalPart_of_biholomorph_onePoint` by projecting the
source lift and source principal part from the provider.

This is a Lean-code commit. It should not solve the full simple-pole coordinate
construction yet; it should make the remaining #234 frontier strictly narrower
and keep all public theorem names/signatures unchanged.

## Scope

- Edit `Jacobian/HolomorphicForms/MeromorphicToBranchedCover.lean`.
- Edit `.sci/task.md` and local ignored `.sci/plan.md` state as needed.
- Do not edit `Jacobian/Challenge.lean`.
- Do not edit `Jacobian/HolomorphicForms/GenusZeroClassification.lean`.
- Preserve the public theorem name and signature of
  `complexSimplePolePrincipalPart_of_biholomorph_onePoint`.
- Do not add more than one new `sorry`; the new explicit pullback-data provider
  must replace the existing #234 `sorry`, not add a second reachable gap.
- Do not use the circular fixed-pole/Riemann--Roch route through
  `genusZero_pointRRSection_meromorphic_getD_exists`,
  `genusZero_fixedPole_analyticRRWitness_nonempty`,
  `genusZero_fixedPole_simplePoleRRSection_nonempty`,
  `genusZero_fixedPole_rrSection_nonempty`, or
  `genusZero_pointRRSection_outside_constants_exists`.

## Suggested Shape

One acceptable shape is:

```lean
structure BiholomorphOnePointSimplePolePullbackData
    (X : Type*) ... (P : X) (e : X ≃ₜ OnePoint ℂ) where
  targetLift : OnePoint ℂ → ℂ
  targetPrincipalPart : HasComplexSimplePolePrincipalPart targetLift (e P)
  sourceLift : X → ℂ
  sourceLift_eq : sourceLift = targetLift ∘ (e : X → OnePoint ℂ)
  sourcePrincipalPart : HasComplexSimplePolePrincipalPart sourceLift P

theorem biholomorphOnePointSimplePolePullbackData_of_biholomorph_onePoint
    ... (P : X) (e : X ≃ₜ OnePoint ℂ) (he : ...) (he_symm : ...) :
    Nonempty (BiholomorphOnePointSimplePolePullbackData X P e) := by
  sorry
```

Adjust binder lists and names to match local style and compile cleanly.

## Checklist

- [x] Confirm `.sci/plan.md` marks B1.0 and B1 complete and lists C1.0 as the
      next unchecked milestone.
- [x] Inspect `HasComplexSimplePolePrincipalPart` and
      `complexSimplePolePrincipalPart_of_biholomorph_onePoint`.
- [x] Add the pullback-data structure exposing target lift, source pullback,
      and source principal-part data.
- [x] Add the named pullback-data provider with exactly one `sorry`,
      documenting it as the remaining explicit `OnePoint ℂ` coordinate
      pullback construction.
- [x] Replace the body of
      `complexSimplePolePrincipalPart_of_biholomorph_onePoint` with sorry-free
      assembly from the provider.
- [x] Keep downstream `singlePoleAnalyticData_of_biholomorph_onePoint`
      unchanged.
- [x] Run `lake build Jacobian.HolomorphicForms.MeromorphicToBranchedCover`.
- [x] Run `lake build Jacobian.Solution`.
- [x] Run `scripts/list-sorries.py --text` and confirm the reachable #234 root
      moved from `complexSimplePolePrincipalPart_of_biholomorph_onePoint` to
      the new pullback-data provider, with no net new reachable sorries.
- [x] Commit exactly the scoped Lean/SCI edit with normalized author/committer
      metadata and `Co-authored-by: Codex <codex@openai.com>`.

## Verification

- `lake build Jacobian.HolomorphicForms.MeromorphicToBranchedCover`: succeeds;
  this file now has warnings at
  `biholomorphOnePointSimplePolePullbackData_of_biholomorph_onePoint` and the
  existing `genusZeroHomeomorphOnePoint_of_analyticGenus_zero` provider.
- `lake build Jacobian.Solution`: succeeds with existing `uses sorry`
  warnings.
- `scripts/list-sorries.py --text`: still 20 reachable sorries total; the #234
  root moved from `complexSimplePolePrincipalPart_of_biholomorph_onePoint` to
  `biholomorphOnePointSimplePolePullbackData_of_biholomorph_onePoint`.
