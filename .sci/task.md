# Worker jc0 — Milestone B1.0: split #232 uniformization interface upstream

## Assignment

Prepare Milestone B1 by making the #232 uniformization theorem available to
`Jacobian/HolomorphicForms/MeromorphicToBranchedCover.lean` without creating an
import cycle.

Currently `exists_biholomorph_onePoint_of_analyticGenus_zero` (#233) is in
`MeromorphicToBranchedCover.lean`, but the theorem it should consume,
`exists_biholomorph_onePoint_of_genus_zero` (#232), is in
`GenusZeroClassification.lean`, which already imports
`MeromorphicToBranchedCover.lean`. This task should extract the minimal
topological-homeomorphism-to-biholomorphism interface from
`GenusZeroClassification.lean` into a new upstream helper file under
`Jacobian/HolomorphicForms/`, then import that helper from both files.

This is a refactor-only commit. It should preserve all public theorem names and
signatures, introduce no new `sorry`s, and leave #232’s single reachable root at
`genusZeroNormalizedMontelPatchSelector_of_homeomorph_onePoint`.

## Scope

- Edit `Jacobian/HolomorphicForms/GenusZeroClassification.lean`.
- Add one new helper file under `Jacobian/HolomorphicForms/`, for example
  `GenusZeroUniformization.lean`, containing the existing #232 uniformization
  interface and its local support structures/lemmas.
- Edit `Jacobian/HolomorphicForms/MeromorphicToBranchedCover.lean` only to add
  the new import if the split succeeds; do not change #233’s body in this step.
- Edit `.sci/task.md` and local ignored `.sci/plan.md` state.
- Do not edit `Jacobian/Challenge.lean`.
- Do not prove or alter `exists_biholomorph_onePoint_of_analyticGenus_zero` yet.
- Do not use the circular fixed-pole/Riemann--Roch route.
- Do not add new Lean declarations with `sorry`; move the existing isolated
  selector provider only if needed for the import split.

## Checklist

- [x] Confirm `.sci/plan.md` marks A1.1, A1.2, and A2 complete, and now lists
      B1.0 as the next unchecked planned milestone before B1.
- [x] Identify the minimal contiguous #232 block in
      `GenusZeroClassification.lean`: `GenusZeroGlobalGluingData`,
      `GenusZeroNormalizedMontelPatchSelector`,
      `genusZeroNormalizedMontelPatchSelector_of_homeomorph_onePoint`,
      `genusZeroGlobalGluingData_of_homeomorph_onePoint`,
      `exists_biholomorph_onePoint_of_genus_zero`, and the helper lemmas they
      require.
- [x] Move that minimal block into the new upstream helper file, preserving the
      namespace, theorem names, signatures, comments, and the single existing
      selector-provider `sorry`.
- [x] Update imports so `GenusZeroClassification.lean` still builds and
      `MeromorphicToBranchedCover.lean` can see
      `exists_biholomorph_onePoint_of_genus_zero` without importing
      `GenusZeroClassification.lean`.
- [x] Run `lake build Jacobian.HolomorphicForms.GenusZeroUniformization` or the
      chosen new module name.
- [x] Run `lake build Jacobian.HolomorphicForms.GenusZeroClassification`.
- [x] Run `lake build Jacobian.HolomorphicForms.MeromorphicToBranchedCover`.
- [x] Run `lake build Jacobian.Solution`.
- [x] Run `scripts/list-sorries.py --text` and confirm there is no net new
      reachable sorry and the GenusZero root remains
      `genusZeroNormalizedMontelPatchSelector_of_homeomorph_onePoint`.
- [x] Commit exactly the scoped refactor with normalized author/committer
      metadata and `Co-authored-by: Codex <codex@openai.com>`.

## Verification

- `lake build Jacobian.HolomorphicForms.GenusZeroUniformization`: succeeds;
  the module has the moved selector-provider warning.
- `lake build Jacobian.HolomorphicForms.MeromorphicToBranchedCover`: succeeds
  and can import `GenusZeroUniformization` without an import cycle.
- `lake build Jacobian.HolomorphicForms.GenusZeroClassification`: succeeds
  after consuming the moved declarations from `GenusZeroUniformization`.
- `lake build Jacobian.Solution`: succeeds with existing `uses sorry` warnings.
- `scripts/list-sorries.py --text`: still 20 reachable sorries total; the
  GenusZero root moved files but remains the same declaration,
  `genusZeroNormalizedMontelPatchSelector_of_homeomorph_onePoint`.
