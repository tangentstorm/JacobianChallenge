# Worker jc0 — Milestone C1.3: name pulled-back simple-pole coordinate

## Assignment

Execute C1.3 from `.sci/plan.md`: name the source pullback coordinate used in
the #234 route, rather than repeating
`onePointSimplePoleCoordinate (e P) ∘ (e : X → OnePoint ℂ)` throughout the
facts and data providers.

Add a local noncomputable definition in
`Jacobian/HolomorphicForms/MeromorphicToBranchedCover.lean`, for example:

```lean
biholomorphPulledBackSimplePoleCoordinate
    (P : X) (e : X ≃ₜ OnePoint ℂ) : X → ℂ :=
  onePointSimplePoleCoordinate (e P) ∘ (e : X → OnePoint ℂ)
```

Then tighten `BiholomorphOnePointSimplePolePullbackFacts` so its source
principal-part field refers directly to this named coordinate, and rebuild
`BiholomorphOnePointSimplePolePullbackData` with
`sourceLift := biholomorphPulledBackSimplePoleCoordinate P e` and
`sourceLift_eq := rfl` or a definitional proof after unfolding if Lean requires
it.

This is a Lean-code commit. It should not prove the analytic target-coordinate
or transport facts yet; it should make the remaining #234 frontier easier to
attack by giving the source coordinate a stable local name.

## Scope

- Edit `Jacobian/HolomorphicForms/MeromorphicToBranchedCover.lean`.
- Edit `.sci/task.md` and local ignored `.sci/plan.md` state.
- Do not edit `Jacobian/Challenge.lean`.
- Do not edit `Jacobian/HolomorphicForms/GenusZeroClassification.lean`.
- Preserve public theorem names and signatures, especially
  `complexSimplePolePrincipalPart_of_biholomorph_onePoint`.
- Do not add more than one new `sorry`; the existing
  `biholomorphOnePointSimplePolePullbackFacts_of_biholomorph_onePoint` provider
  must remain the single #234 frontier.
- Do not use the circular fixed-pole/Riemann--Roch route through
  `genusZero_pointRRSection_meromorphic_getD_exists`,
  `genusZero_fixedPole_analyticRRWitness_nonempty`,
  `genusZero_fixedPole_simplePoleRRSection_nonempty`,
  `genusZero_fixedPole_rrSection_nonempty`, or
  `genusZero_pointRRSection_outside_constants_exists`.

## Checklist

- [x] Confirm `.sci/plan.md` marks C1.2 complete and lists C1.3 as the next
      unchecked milestone.
- [x] Inspect `onePointSimplePoleCoordinate`,
      `BiholomorphOnePointSimplePolePullbackFacts`, and
      `BiholomorphOnePointSimplePolePullbackData`.
- [x] Add `biholomorphPulledBackSimplePoleCoordinate (P : X) (e : X ≃ₜ OnePoint ℂ) :
      X → ℂ` as a local explicit source-coordinate definition.
- [x] Tighten `BiholomorphOnePointSimplePolePullbackFacts` so
      `sourcePrincipalPart` mentions `biholomorphPulledBackSimplePoleCoordinate P e`.
- [x] Rebuild `BiholomorphOnePointSimplePolePullbackData` using the named source
      coordinate and preserve the relation to the target coordinate.
- [x] Keep exactly one `sorry`, in
      `biholomorphOnePointSimplePolePullbackFacts_of_biholomorph_onePoint`.
- [x] Keep `complexSimplePolePrincipalPart_of_biholomorph_onePoint` and
      downstream `singlePoleAnalyticData_of_biholomorph_onePoint` unchanged
      except for any name drift forced by the provider replacement.
- [x] Run `lake build Jacobian.HolomorphicForms.MeromorphicToBranchedCover`.
- [x] Run `lake build Jacobian.Solution`.
- [x] Run `scripts/list-sorries.py --text` and confirm the reachable #234 root
      remains the facts provider, with no net new reachable sorries.
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
  root remains `biholomorphOnePointSimplePolePullbackFacts_of_biholomorph_onePoint`.
