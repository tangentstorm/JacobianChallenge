# Worker jc0 — Milestone A2: audit #232 uniformization boundary

## Assignment

Execute Milestone A2 from `.sci/plan.md`: verify that the #232 uniformization
route is clean above the deliberately isolated provider
`genusZeroNormalizedMontelPatchSelector_of_homeomorph_onePoint`.

This is an audit/verification commit-sized step. It should not try to prove the
normalized selector provider yet. Instead, refresh the local axiom-check file
used for this worker, run the relevant `#print axioms` checks, and confirm that
`exists_biholomorph_onePoint_of_genus_zero` has no unexpected `sorryAx`
dependencies beyond the named selector provider.

## Scope

- Edit `.sci/task.md` and, if useful for the audit, ignored local scratch files
  under `.sci/` such as `.sci/axiom-check.lean`.
- Do not edit `Jacobian/Challenge.lean`.
- Do not edit `Jacobian/HolomorphicForms/MeromorphicToBranchedCover.lean`.
- Do not change the public name or signature of
  `exists_biholomorph_onePoint_of_genus_zero`.
- Do not add new Lean declarations, new imports, or new `sorry`s.
- Do not use the circular fixed-pole/Riemann--Roch route.

## Checklist

- [x] Confirm `.sci/plan.md` marks A1.1 and A1.2 complete and lists A2 as the
      next Milestone A item.
- [x] Inspect the current #232 route around
      `exists_biholomorph_onePoint_of_genus_zero`,
      `genusZeroGlobalGluingData_of_homeomorph_onePoint`, and
      `genusZeroNormalizedMontelPatchSelector_of_homeomorph_onePoint`.
- [x] Refresh a local `.sci/axiom-check.lean` or equivalent scratch command so
      it prints axioms for `exists_biholomorph_onePoint_of_genus_zero`,
      `genusZeroGlobalGluingData_of_homeomorph_onePoint`,
      `GenusZeroGlobalGluingData.exists_contMDiff_homeomorph`, and the nearby
      gluing helpers.
- [x] Run the axiom check with `lake env lean .sci/axiom-check.lean` or an
      equivalent command, and record the relevant output in this task file.
- [x] Run `lake build Jacobian.HolomorphicForms.GenusZeroClassification`.
- [x] Run `lake build Jacobian.Solution`.
- [x] Run `scripts/list-sorries.py --text` and confirm the reachable genus-zero
      root remains `genusZeroNormalizedMontelPatchSelector_of_homeomorph_onePoint`
      with 20 reachable sorries total.
- [x] If no Lean code changes are needed, commit only the updated tracked
      `.sci/task.md` with normalized author/committer metadata and
      `Co-authored-by: Codex <codex@openai.com>`.

## Verification

- `lake env lean .sci/axiom-check.lean`: succeeds. The gluing helpers
  `genusZeroGlobalGluing_coord_mem_target_on_patch`,
  `genusZeroGlobalGluing_overlap_compatible`,
  `genusZeroGlobalGluing_invMap_exists`,
  `genusZeroGlobalGluing_local_left_inverse_on_patch`,
  `genusZeroGlobalGluing_local_right_inverse_on_target_chart`,
  `genusZeroGlobalGluing_contMDiff_toMap`,
  `genusZeroGlobalGluing_contMDiff_invMap`,
  `GenusZeroGlobalGluingData.toHomeomorph`, and
  `GenusZeroGlobalGluingData.exists_contMDiff_homeomorph` have axiom sets
  `[propext, Classical.choice, Quot.sound]`.
- The only checked #232 route declarations whose axiom sets include `sorryAx`
  are `genusZeroNormalizedMontelPatchSelector_of_homeomorph_onePoint`,
  `genusZeroGlobalGluingData_of_homeomorph_onePoint`, and
  `exists_biholomorph_onePoint_of_genus_zero`, so the public theorem has no
  unexpected `sorryAx` dependency beyond the named selector provider.
- `lake build Jacobian.HolomorphicForms.GenusZeroClassification`: succeeds;
  the only warning in this file is the selector provider.
- `lake build Jacobian.Solution`: succeeds with existing `uses sorry` warnings.
- `scripts/list-sorries.py --text`: still 20 reachable sorries total; the
  GenusZeroClassification root remains
  `genusZeroNormalizedMontelPatchSelector_of_homeomorph_onePoint`.
