# Worker jc0 — Milestone C1.2: make target simple-pole coordinate explicit

## Assignment

Execute C1.2 from `.sci/plan.md`: make the target `OnePoint ℂ` simple-pole
coordinate explicit inside the #234 pullback provider, rather than leaving
`targetLift` as an arbitrary function chosen by the provider.

Add a local noncomputable definition in
`Jacobian/HolomorphicForms/MeromorphicToBranchedCover.lean`, for example:

```lean
onePointSimplePoleCoordinate (Q : OnePoint ℂ) : OnePoint ℂ → ℂ
```

The intended function is a concrete Möbius-style coordinate with pole at `Q`.
For this commit it is acceptable to choose a pragmatic explicit shape using
the existing `OnePoint` constructors/charts, such as:

- if `Q = ∞`, use the finite coordinate `x.getD 0`;
- if `Q = ↑a`, use `(x.getD 0 - a)⁻¹` away from the pole, with an arbitrary
  value at the pole since the complex lift value at the pole is irrelevant.

Then tighten `BiholomorphOnePointSimplePolePullbackFacts` so it no longer has a
free `targetLift` field. Its target and source fields should refer directly to
`onePointSimplePoleCoordinate (e P)` and
`onePointSimplePoleCoordinate (e P) ∘ (e : X → OnePoint ℂ)`. Prove
`biholomorphOnePointSimplePolePullbackData_of_biholomorph_onePoint` by assembling
the existing data record with that explicit coordinate and `sourceLift_eq := rfl`.

This is a Lean-code commit. It should not prove the analytic target-coordinate
or transport facts yet; it should make the remaining #234 frontier strictly
narrower by naming the concrete target coordinate.

## Scope

- Edit `Jacobian/HolomorphicForms/MeromorphicToBranchedCover.lean`.
- Edit `.sci/task.md` and local ignored `.sci/plan.md` state.
- Do not edit `Jacobian/Challenge.lean`.
- Do not edit `Jacobian/HolomorphicForms/GenusZeroClassification.lean`.
- Preserve public theorem names and signatures, especially
  `complexSimplePolePrincipalPart_of_biholomorph_onePoint`.
- Do not add more than one new `sorry`; the tightened facts provider must
  replace the existing
  `biholomorphOnePointSimplePolePullbackFacts_of_biholomorph_onePoint` `sorry`,
  not add a second reachable gap.
- Do not use the circular fixed-pole/Riemann--Roch route through
  `genusZero_pointRRSection_meromorphic_getD_exists`,
  `genusZero_fixedPole_analyticRRWitness_nonempty`,
  `genusZero_fixedPole_simplePoleRRSection_nonempty`,
  `genusZero_fixedPole_rrSection_nonempty`, or
  `genusZero_pointRRSection_outside_constants_exists`.

## Checklist

- [x] Confirm `.sci/plan.md` marks C1.1 complete and lists C1.2 as the next
      unchecked milestone.
- [x] Inspect `BiholomorphOnePointSimplePolePullbackFacts` and the current
      `biholomorphOnePointSimplePolePullbackFacts_of_biholomorph_onePoint`
      provider.
- [x] Add `onePointSimplePoleCoordinate (Q : OnePoint ℂ) : OnePoint ℂ → ℂ`
      as a local explicit target-coordinate definition.
- [x] Tighten `BiholomorphOnePointSimplePolePullbackFacts` so its principal-part
      fields mention `onePointSimplePoleCoordinate (e P)` directly.
- [x] Keep exactly one `sorry` in the tightened facts provider, documenting it
      as the remaining explicit-coordinate plus biholomorphic-transport frontier.
- [x] Rebuild `BiholomorphOnePointSimplePolePullbackData` using
      `targetLift := onePointSimplePoleCoordinate (e P)`,
      `sourceLift := onePointSimplePoleCoordinate (e P) ∘ e`, and
      `sourceLift_eq := rfl`.
- [x] Keep `complexSimplePolePrincipalPart_of_biholomorph_onePoint` and
      downstream `singlePoleAnalyticData_of_biholomorph_onePoint` unchanged
      except for any name drift forced by the provider replacement.
- [x] Run `lake build Jacobian.HolomorphicForms.MeromorphicToBranchedCover`.
- [x] Run `lake build Jacobian.Solution`.
- [x] Run `scripts/list-sorries.py --text` and confirm the reachable #234 root
      remains the tightened facts provider, with no net new reachable sorries.
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
