# Chapter 06 Baseline Blueprint Audit

Status: baseline inventory complete for Milestone 0.

## Scope

This audit records the current Chapter-06 blueprint state before adding new
proof-tree nodes. No Lean proofs were edited and no blueprint dependency wiring
was changed.

## Current Chapter-06 Nodes

Physical nodes in `tex/sections/06-periods-and-riemann-bilinear.tex`:

- `def:path-integral-in-chart`: has `\lean{JacobianChallenge.Periods.pathIntegralInChartCorrect}` and `\leanok`.
- `lem:path-integral-in-chart-linearity`: uses `def:path-integral-in-chart`; has three Lean decls and `\leanok`.
- `def:path-integral-via-cover`: uses the chart-local definition and linearity lemma; has two Lean decls and `\leanok`.
- `lem:path-integral-cover-independent`: uses `def:path-integral-via-cover`; has Lean decl and `\leanok`.
- `thm:period-pairing-from-path-integral`: uses the cover construction, cover independence, and homology invariance; has Lean decl and `\leanok`.
- `lem:period-homology-invariance`: uses Stokes and closedness of holomorphic forms; has Lean decl and `\leanok`.
- `lem:holomorphic-form-is-closed`: has Lean decl and `\leanok`.
- `thm:stokes-on-rs-with-boundary`: has Lean decl and `\leanok`; text records the manifold-with-boundary Stokes gap.
- `thm:period-vectors-full-real-rank`: uses `lem:riemann-classical-real-li-input`; has Lean decl and `\leanok`.
- `lem:riemann-classical-real-li-input`: open issue #227; has Lean decl and no `\leanok`.
- `input:riemann-bilinear`: uses `thm:period-vectors-full-real-rank`; has Lean decl and `\leanok`.
- `input:hodge-deRham`: uses the two exactness frontier nodes; no `\lean{}` currently attached.
- `lem:de-rham-comparison-map1-zero-period-primitive-exists-provider`: open issue #242; has Lean decl and no `\leanok`.
- `lem:hodge-remainder-period-payload-exact`: open issue #243; has Lean decl and no `\leanok`.

Additional Chapter-06 frontier/dependency nodes outside the physical Section 06
file:

- `tex/sections/05-polygonal-model.tex`
  - `lem:polygon4g-quotient-path-finite-lift-subdivision`: open issue #228; has Lean decl and no `\leanok`.
  - `lem:polygon4g-partial-side-arc-homologous-to-edge-chain`: open issue #229; has Lean decl and no `\leanok`.
  - `lem:edge-chain-sum-singular-boundary-scalar-coefficient-zero`: open issue #230; has Lean decl and no `\leanok`.
- `tex/statements/statement-bank.tex`
  - `lem:h1-basis-of-compact-riemann-surface-u`: open issue #240; has Lean decl and no `\leanok`.
  - `lem:riemann-classical-real-li-input-u`: open issue #241; has Lean decl and no `\leanok`.

## Frontier Summary

The 8 requested Chapter-06 sorries are all visible as uncolored/open blueprint
nodes with existing Lean declarations:

1. #227 `lem:riemann-classical-real-li-input`
2. #228 `lem:polygon4g-quotient-path-finite-lift-subdivision`
3. #229 `lem:polygon4g-partial-side-arc-homologous-to-edge-chain`
4. #230 `lem:edge-chain-sum-singular-boundary-scalar-coefficient-zero`
5. #240 `lem:h1-basis-of-compact-riemann-surface-u`
6. #241 `lem:riemann-classical-real-li-input-u`
7. #242 `lem:de-rham-comparison-map1-zero-period-primitive-exists-provider`
8. #243 `lem:hodge-remainder-period-payload-exact`

Current wiring is still coarse:

- Cluster B: `thm:period-vectors-full-real-rank` points directly to #227; the
  universe-`u` companions #240/#241 are only exposed from the statement bank via
  `thm:period-lattice`.
- Cluster A: the three Hurewicz nodes are wired through
  `thm:analytic-eq-topological-genus` in Section 05, not under the physical
  Section 06 file.
- Cluster C: `input:hodge-deRham` points directly to #242 and #243 and has no
  Lean declaration of its own.
- The prose mentions green substrates for the bilinear and positivity stand-ins,
  but these are not yet decomposed into `\lean{}`-tracked blueprint nodes with
  `\uses` edges.

## Verification

- `lake exe cache get`: succeeded; no files needed downloading.
- `scripts/blueprint_audit.py`: succeeded with exit code 0.
  - Summary: 94 statement-style environment blocks; 93 with `\lean{...}`; 1
    marked `\notready`; 77 clean; 15 `B:decls-exist-but-no-env-leanok`.
  - The 15 uncolored nodes include the expected open Chapter-06 frontier nodes
    listed above, plus unrelated open nodes in Chapters 04 and 08 and the
    Section 05 handle/surface-classification frontier.
- `bash scripts/build-blueprint.sh`: the web-generation phase completed and
  regenerated `blueprint/web/index.html`; the log reached
  `==> [2/4] Refreshing sorries.jsonl + node states`.
  - No unresolved-label message appeared during the captured web-generation
    output.
  - A direct search for unresolved-label wording in `blueprint/web` and `tex`
    returned no matches.
  - The command did not return a final exit status from the
    `lake build Jacobian.Solution` substep in this environment. A standalone
    `lake build Jacobian.Solution` invocation later emitted normal replay output
    and existing `declaration uses sorry` warnings, including the expected
    Chapter-06 frontier declarations in `HodgeProjection.lean`, `Hurewicz.lean`,
    and `H1BasisU.lean`, but likewise did not return a final exit status while
    no matching Lean child process was visible in `ps`.

## Next Mapping Recommendation

Begin Milestone B-map with #227. Add explicit blueprint nodes for the green
Riemann-bilinear algebra and Hermitian-positivity stand-ins already mentioned in
the Section 06 prose, then wire `lem:riemann-classical-real-li-input` so its
remaining frontier is the actual manifold-level bilinear/positivity gap. After
that, map the mechanical universe-`u` mirrors #241 and #240 from the statement
bank into the same dependency story.

# B1 Riemann-Bilinear Substrate Blueprint Map

Status: B1 complete.

## Added Blueprint Nodes

In `tex/sections/06-periods-and-riemann-bilinear.tex`, #227 now uses four
explicit substrate nodes instead of floating as a single undecomposed input:

- `lem:riemann-bilinear-algebra-skeleton`
  - Lean declarations:
    `Q_skeleton_antisym`, `Q_skeleton_diag_zero`, `Q_skeleton_smul_left`,
    `Q_skeleton_smul_right`, `handleTerm_antisym`, `handleTerm_diag_zero`,
    `riemann_bilinear_identity_skeleton`.
  - Role: the finite symplectic handle-sum algebra over `Fin (2*g)`.
- `lem:quadratic-positivity-linear-independent-skeleton`
  - Lean declarations:
    `quadraticSkeleton_nonneg`, `quadraticSkeleton_eq_zero_iff`,
    `sum_nonneg_eq_zero_iff_pointwise`,
    `real_linearIndependent_of_quadratic_pos_def`,
    `quadratic_pos_def_of_real_linearIndependent`.
  - Role: the finite-dimensional positive-quadratic-form to real-linear
    independence bridge.
- `lem:period-pairing-satisfies-bilinear-identity`
  - Lean declarations:
    `riemann_bilinear_identity`,
    `periodPairing_satisfies_bilinear_identity`.
  - Role: the current project-side period-pairing wrapper for the algebraic
    bilinear identity stand-in.
- `lem:hodge-form-pos-def-on-periods`
  - Lean declarations:
    `hodge_form_posDef`,
    `hodge_form_posDef_on_periods`.
  - Role: the coordinate Hodge-positivity wrapper used by the period-functional
    stack.

The open #227 node `lem:riemann-classical-real-li-input` now has `\uses` edges
to these four substrate nodes and remains intentionally unmarked by `\leanok`.
This preserves the genuine remaining frontier: upgrading the algebraic
stand-ins to the actual symplectic/canonical homology basis plus
manifold-level Stokes/Hodge positivity needed by
`riemann_classical_real_LI_input`.

## Green-Ness Evidence

- `rg '\bsorry\b|axiom|opaque'` over
  `Jacobian/Periods/PeriodFunctional.lean` and
  `Jacobian/Periods/RiemannBilinearRefinement.lean` found only the existing
  #227 `sorry` in `riemann_classical_real_LI_input` (plus an explanatory
  `opaque` mention in prose).
- `#print axioms` for representative new green declarations showed only
  ordinary Lean axioms (`propext`, `Classical.choice`, `Quot.sound`) and no
  `sorryAx`.
- `scripts/blueprint_audit.py` succeeded with exit code 0:
  98 statement-style environments, 97 with `\lean{...}`, 1 `\notready`,
  81 clean, and the same 15 expected open/uncolored frontier nodes.
- `bash scripts/build-blueprint.sh` succeeded. It refreshed `sorries.jsonl`
  with 279 graph-coloured records and verified the web post-processing
  injections.
- `sorries.jsonl` records all 16 new B1 Lean declarations as `c:"done"`.

## Next Recommended Step

Proceed to B2: wire the universe-`u` companions #241
(`riemann_classical_real_LI_inputU`) and #240
(`h1_basis_of_compact_riemann_surfaceU`) into the same dependency story from
the statement bank. The B2 task should make the #241 dependency on #227 explicit
and separate the #240 surface-classification/H1-basis frontier from the
Riemann-bilinear analytic frontier.

# B2 Universe-u Period-Rank Blueprint Map

Status: B2 complete.

## Added Blueprint Nodes

In `tex/statements/statement-bank.tex`, the two universe-`u` frontier nodes now
have an explicit substrate:

- `lem:universe-u-singular-homology-period-pairing-shape`
  - Lean declarations:
    `singularChainComplexZU`, `SingularOneChainU`, `SingularTwoChainU`,
    `IntegralOneCycleU`, `periodPairing_descent_auxU`,
    `periodPairingComplexU`, `basisAlignedPeriodSubgroupConcreteU`.
  - Role: the shape-level universe-`u` singular-chain, homology, period-pairing,
    and basis-aligned period-subgroup transport layer.
- `lem:type-zero-h1-basis-symplectic-cycle-substrate`
  - Lean declarations:
    `h1_basis_of_compact_riemann_surface`, `symplectic_basis_of_cycles`.
  - Role: the Type-0 H1-basis/symplectic-cycle substrate that the universe-`u`
    H1-basis obligation mirrors.

## Frontier Wiring

- #240 `lem:h1-basis-of-compact-riemann-surface-u` now uses the universe-`u`
  homology/pairing shape node plus the Type-0 H1-basis substrate. Its prose now
  identifies the genuine remaining gap as the universe-`u`
  surface-classification/cellular-homology rank-`2g` rerun, not a
  Riemann-bilinear analytic gap.
- #241 `lem:riemann-classical-real-li-input-u` now uses the Type-0 #227 node
  `lem:riemann-classical-real-li-input` plus the universe-`u`
  homology/pairing shape node. Its prose now identifies the genuine remaining
  gap as the same Riemann-bilinear/Hodge-positivity frontier as #227, stated for
  `IntegralOneCycleU` and `periodPairingComplexU`.
- `thm:period-lattice` still consumes the public #240/#241 nodes, but those
  nodes no longer float without a proof skeleton.

## Verification So Far

- `scripts/blueprint_audit.py` succeeded with exit code 0:
  100 statement-style environments, 99 with `\lean{...}`, 1 `\notready`,
  83 clean, and the same 15 expected open/uncolored frontier nodes.
- `sorries.jsonl` still marks #240 and #241 as `c:"sorry"` before the pending
  `build-blueprint.sh` refresh, as expected.
- `bash scripts/build-blueprint.sh` rendered the web pages and reached the
  Lake-backed state-refresh step. That refresh did not return a final status in
  this environment while concurrent sibling-worker Lake builds were active; no
  `jc1` Lean child was visible in `ps` during the no-output interval.

# A1 Hurewicz Substrate Blueprint Map

Status: A1 complete.

## Added Blueprint Nodes

In `tex/sections/05-polygonal-model.tex`, the three Hurewicz frontier nodes
now have explicit substrate immediately underneath them:

- `lem:polygon4g-quotient-local-lift-substrate`
  - Lean declarations:
    `Polygon4gQuotientPathFiniteLiftSubdivision`,
    `polygon4g_sideRel_eq_of_norm_lt_one`,
    `polygon4g_mk_eq_of_norm_lt_one`.
  - Role: records the finite local-lift package expected by #228 and the
    already-proved interior singleton-fibre facts for the side-pairing quotient.
- `lem:polygon4g-endpoint-repair-bookkeeping-substrate`
  - Lean declarations:
    `Polygon4gEndpointRepairData`,
    `polygon4gBoundaryArcStep_projected_eq_chainMap`,
    `polygon4gBoundaryArcSteps_projected_eq_chainMap`,
    `polygon4gEndpointRepair_projected_eq_chainMap`,
    `polygon4g_endpoint_pair_repaired_refl`,
    `polygon4g_aPair_edgeIndex`, `polygon4g_bPair_edgeIndex`,
    `edgeArcIdx_aPair_edgeIndex`, `edgeArcIdx_bPair_edgeIndex`.
  - Role: isolates the side-arc endpoint-repair data and chain-map/index
    bookkeeping that are already formalized before the primitive #229
    side-strip geometry.
- `lem:edge-chain-finite-coefficient-substrate`
  - Lean declarations:
    `EdgeBoundarySignedFaceCoefficientComparison`,
    `signedFaceTargetEdgeCoefficient_eq_of_edgeSimplex_sum`,
    `edgeChain_sum_singular_boundary_signed_face_terms_edgeSimplex_coefficient_comparison`,
    `edgeChain_sum_singular_boundary_signed_face_terms_edgeSimplex_scalar_coefficient_zero`,
    `edgeChain_sum_singular_boundary_face_terms_edgeSimplex_scalar_coefficient_zero`,
    `edgeChain_sum_singular_boundary_faces_edgeSimplex_scalar_coefficient_zero`,
    `edgeChain_sum_singular_boundary_faces_scalar_coefficient_zero`,
    `edgeChain_sum_singular_boundary_decomposition_scalar_coefficient_zero`.
  - Role: exposes the finite signed-face coefficient algebra below #230, up to
    but not including the remaining homological edge-independence frontier.

## Frontier Wiring

- #228 `lem:polygon4g-quotient-path-finite-lift-subdivision` now uses
  `lem:polygon4g-quotient-local-lift-substrate` and remains unmarked by
  `\leanok`.
- #229 `lem:polygon4g-partial-side-arc-homologous-to-edge-chain` now uses
  `lem:polygon4g-endpoint-repair-bookkeeping-substrate` and remains unmarked by
  `\leanok`.
- #230 `lem:edge-chain-sum-singular-boundary-scalar-coefficient-zero` now uses
  `lem:edge-chain-finite-coefficient-substrate` and remains unmarked by
  `\leanok`.

The survey also confirmed that
`singular_one_simplex_subdivision_prism_homologous` is itself a direct
`sorry` in `sorries.jsonl`, so it was intentionally not used as a green A1
substrate node.

## Verification

- `rg` over `Jacobian/Periods/Hurewicz.lean` found direct `sorry` bodies only
  at #228, #229, #230, and the separate
  `singular_one_simplex_subdivision_prism_homologous` subdivision-prism leaf.
  The new green substrate declarations are outside those direct sorry bodies.
- `scripts/blueprint_audit.py` succeeded with exit code 0:
  103 statement-style environments, 102 with `\lean{...}`, 1 `\notready`,
  86 clean, and the same 15 expected open/uncolored frontier nodes.
- A targeted `lake env lean` `#print axioms` probe for representative new
  substrate declarations was attempted, but it remained silent while unrelated
  sibling-worker Lake builds were active. The stale probe was terminated and the
  verification is therefore recorded through `rg`, `sorries.jsonl`, and the
  blueprint audit.
- `lake exe cache get` was attempted before `build-blueprint.sh`, but it also
  remained silent behind concurrent unrelated Lake builds and was terminated
  after repeated no-output intervals. Per the task instructions, the
  `bash scripts/build-blueprint.sh` verification is caveated rather than run
  without the prerequisite cache step.
- Rejection adjustment: added the missing
  `lem:polygon4g-eq-standard-word-quotient` blueprint label as a green node
  for `EdgeWord.polygon4g_eq_standard_word_quotient`. A rerun of
  `bash scripts/build-blueprint.sh` completed successfully: web generation,
  `sorries.jsonl`/node-state refresh, post-processing injection, and injection
  verification all passed. The generated `sorries.jsonl` update is included in
  the amended fix commit.

## Next Recommended Step

Proceed to A2: wire #228/#229/#230 to their genuine frontier leaves only.
In particular, separate #228 into quotient-chart finite-lift topology versus
the already-isolated subdivision-prism leaf; keep #229 focused on primitive
side-strip geometry; and keep #230 focused on the homological edge-chain
independence theorem after the finite coefficient algebra already mapped here.

# A2 Hurewicz Frontier Wiring

Status: A2 complete.

## Added / Refined Frontier Node

In `tex/sections/05-polygonal-model.tex`, the Cluster-A Hurewicz wiring now
separates the quotient-lift and singular-subdivision frontiers:

- `lem:polygon4g-singular-simplex-subdivision-lifts-to-disk`
  - Lean declaration:
    `polygon4g_singularSimplex_subdivision_lifts_to_disk`.
  - Role: records the downstream lift package that depends on #228
    quotient-chart finite-lift data and, in the prose, the singular-chain
    subdivision-prism frontier. The prism frontier is intentionally not a
    separate `\lean{}` node because the graph-state generator attaches a stale
    green blueprint row to that declaration while the Lean declaration row
    remains `c:"sorry"`.

## Frontier Wiring

- `thm:analytic-eq-topological-genus` now uses the full polygon quotient simplex
  lift package rather than pointing directly to #228. The package node then
  exposes the genuine #228 quotient-chart finite-lift frontier and the
  independent singular-chain subdivision-prism frontier in prose.
- #229 remains focused on primitive side-strip geometry after the A1 endpoint
  repair/bookkeeping substrate.
- #230 remains focused on homological edge-chain independence after the A1
  finite signed-face coefficient algebra.

The direct frontier nodes #228, #229, #230, and the downstream lift-package node
remain unmarked by proof-level `\leanok`; the subdivision-prism frontier is
also left ungreen.

## Verification

- Confirmed the new `\lean{}` declarations exist in
  `Jacobian/Periods/Hurewicz.lean`.
- `python3 scripts/blueprint_audit.py` succeeded with exit code 0:
  105 statement-style environments, 104 with `\lean{...}`, 1 `\notready`,
  87 clean, and 16 expected declaration-only open nodes.
- `bash scripts/build-blueprint.sh` succeeded end-to-end. It refreshed
  `sorries.jsonl` with 310 graph-coloured records, pruned the stale prism
  blueprint row, injected the blueprint web extras, and verified the
  post-processing hooks.

## Next Recommended Step

Proceed to C1: refine `input:hodge-deRham` so #242 is the unique de Rham
primitive-existence frontier and #243 is the unique Hodge closed =
harmonic + exact frontier, with green surrounding assembly nodes for
zero-period-to-kernel, primitive-to-exact, and harmonic-projection
kernel/exact bookkeeping.

# C1 de Rham / Hodge Exactness Frontier Wiring

Status: C1 complete.

## Added Blueprint Nodes

In `tex/sections/06-periods-and-riemann-bilinear.tex`, `input:hodge-deRham`
now factors through two exactness packages instead of pointing directly at the
two open providers.

De Rham zero-period substrate:

- `lem:de-rham-zero-period-kernel-bookkeeping`
  - Lean declarations:
    `deRhamComparisonMap1_zero_period_mem_kernel_frontier`,
    `deRhamComparisonMap1_comparison_kernel_zero_period_frontier`.
  - Role: the definitional `LinearMap.mem_ker` transport between zero periods
    and comparison-kernel membership.
- `lem:de-rham-primitive-to-exact-assembly`
  - Lean declaration:
    `deRhamComparisonMap1_zero_period_primitiveExists_exact_assembly`.
  - Role: converts a primitive witness `dθ = ω` into exact-form membership via
    the project definition of `ExactForm`.
- `lem:de-rham-zero-period-exactness-assembly`
  - Lean declarations:
    `deRhamComparisonMap1_zero_period_exact_axiom_frontier`,
    `deRhamComparisonMap1_zero_period_mem_exact_frontier`,
    `deRhamComparisonMap1_comparison_kernel_mem_exact_of_zero_period_frontier`,
    `deRhamComparisonMap1_comparison_kernel_mem_exact_frontier`.
  - Role: the ungreen `sorry-dep` package that consumes #242 and the green
    bookkeeping above.

Hodge exactness substrate:

- `lem:hodge-harmonic-embed-bookkeeping`
  - Lean declarations:
    `harmonicEmbed`, `harmonicProjection1_harmonicEmbed`.
  - Role: the definitional embedding/projection bookkeeping for harmonic
    coefficient data.
- `lem:hodge-zero-projection-exactness-assembly`
  - Lean declarations:
    `harmonicProjection1_hodgeDecomposition`,
    `harmonicProjection1_kernel_subset_exact`,
    `harmonicProjection1_kernel_eq_exact`.
  - Role: the ungreen `sorry-dep` package that consumes #243 and the harmonic
    embedding bookkeeping.

## Frontier Wiring

- `input:hodge-deRham` now uses
  `lem:de-rham-zero-period-exactness-assembly` and
  `lem:hodge-zero-projection-exactness-assembly`.
- #242 `lem:de-rham-comparison-map1-zero-period-primitive-exists-provider`
  remains the unique direct de Rham primitive-existence frontier and is not
  marked with `\leanok`.
- #243 `lem:hodge-remainder-period-payload-exact` remains the unique direct
  Hodge period-payload exactness frontier and is not marked with `\leanok`.
- The package nodes depending on #242/#243 are intentionally unmarked by
  proof-level `\leanok`; the refreshed graph colors them `sorry-dep`, not
  `done`.

## Verification

- `python3 scripts/blueprint_audit.py` succeeded with exit code 0:
  110 statement-style environments, 109 with `\lean{...}`, 1 `\notready`,
  90 clean, and 18 expected declaration-only open/sorry-dependent nodes.
- `bash scripts/build-blueprint.sh` succeeded end-to-end. It refreshed
  `sorries.jsonl` with 322 graph-coloured records, injected the blueprint web
  extras, and verified the post-processing hooks.
- The refreshed `sorries.jsonl` records the new independent bookkeeping nodes
  as `c:"done"`, the #242/#243 providers as `c:"sorry"`, and the package nodes
  consuming them as `c:"sorry-dep"`.

## Next Recommended Step

Proceed to the V milestone as one commit-sized planning/verification step:
audit the full Chapter-06 blueprint-to-Mathlib map, run the final verification
commands, and write `.sci/result.md` with the jc1/jc4/jc5 execution split. The
split should keep #227 before #241, schedule Cluster-A lift/side-arc work before
#230 coefficient independence, and assign #242/#243 separately by de Rham
primitive existence versus Hodge period-payload exactness.

# V Final Verification and Execution Split

Status: Phase 1 complete.

## Final Graph Audit

The eight Chapter-06 frontier declarations remain open and unmarked by
proof-level `\leanok`:

- #227 `riemann_classical_real_LI_input`:
  `sorries.jsonl` has the Lean row and blueprint row as `c:"sorry"`.
- #228 `polygon4g_quotient_path_finite_lift_subdivision`:
  Lean row and blueprint row are `c:"sorry"`.
- #229 `polygon4g_partial_side_arc_homologous_to_edge_chain`:
  Lean row and blueprint row are `c:"sorry"`.
- #230 `edgeChain_sum_singular_boundary_scalar_coefficient_zero`:
  Lean row and blueprint row are `c:"sorry"`.
- #240 `h1_basis_of_compact_riemann_surfaceU`:
  Lean row and blueprint row are `c:"sorry"`.
- #241 `riemann_classical_real_LI_inputU`:
  Lean row and blueprint row are `c:"sorry"`.
- #242 `deRhamComparisonMap1_zero_period_primitiveExists_provider`:
  Lean row and blueprint row are `c:"sorry"`.
- #243 `hodgeRemainder_periodPayload_exact`:
  Lean row and blueprint row are `c:"sorry"`.

The mapped substrate nodes introduced in B1/B2/A1/A2/C1 are either
graph-coloured `done`, or intentionally `sorry-dep` package nodes whose only
open dependency is one of the frontier providers above. No direct frontier node
was marked green.

## Verification

- `python3 scripts/blueprint_audit.py` succeeded with exit code 0:
  110 statement-style environments, 109 with `\lean{...}`, 1 `\notready`,
  90 clean, and 18 expected declaration-only open/sorry-dependent nodes.
- `python3 scripts/list-sorries.py --text` succeeded and reported 20 reachable
  sorries total, including exactly the 8 Chapter-06 frontiers listed above.
- `bash scripts/build-blueprint.sh` succeeded end-to-end. It rebuilt the web
  blueprint, refreshed `sorries.jsonl` with 322 graph-coloured records, and
  verified the post-processing injections.
- `lake build Jacobian.Solution` succeeded with the existing `declaration uses
  sorry` warnings only; no new build errors were introduced.

## Execution Split

### jc1: Riemann bilinear / period-rank cluster

Own #227, #241, and #240:

- First discharge #227 `riemann_classical_real_LI_input` in
  `Jacobian/Periods/PeriodFunctional.lean`. This is the keystone analytic
  input: upgrade the algebraic bilinear and Hodge-positivity substrate to the
  classical Riemann bilinear/positivity statement over the chosen period basis.
- Then discharge #241 `riemann_classical_real_LI_inputU` in
  `Jacobian/Periods/PeriodVectorsLIU.lean` as the universe-`u` transport of
  #227. Do not start #241 before #227 is stable.
- Discharge #240 `h1_basis_of_compact_riemann_surfaceU` in
  `Jacobian/Periods/H1BasisU.lean` alongside the period-rank work. It is the
  universe-`u` H1 basis/surface-classification port needed by the period
  lattice node; coordinate with jc4 on any shared cellular-homology substrate.

### jc4: Hurewicz / singular-homology cluster

Own #228, #229, and #230:

- First discharge #228 `polygon4g_quotient_path_finite_lift_subdivision` in
  `Jacobian/Periods/Hurewicz.lean`, using the quotient local-lift substrate and
  the downstream polygon-simplex lift package.
- In parallel or next, discharge #229
  `polygon4g_partial_side_arc_homologous_to_edge_chain`, after the endpoint
  repair bookkeeping substrate is stable.
- Discharge #230 `edgeChain_sum_singular_boundary_scalar_coefficient_zero`
  only after the lift/side-arc inputs are stable. Its finite signed-face
  coefficient algebra is already mapped; the remaining work is homological
  edge-chain independence.

### jc5: de Rham / Hodge exactness cluster

Own #242 and #243:

- Discharge #242
  `deRhamComparisonMap1_zero_period_primitiveExists_provider` in
  `Jacobian/HolomorphicForms/DeRhamComparisonMap.lean`. The surrounding
  zero-period/kernel and primitive-to-exact assemblies are already mapped; the
  remaining frontier is period-vanishing implies global primitive.
- Discharge #243 `hodgeRemainder_periodPayload_exact` in
  `Jacobian/HolomorphicForms/HodgeProjection.lean`. The harmonic embedding and
  kernel/exact wrappers are already mapped; the remaining frontier is exactness
  of the period-payload remainder.

## Coordination Notes

- #227 is upstream of #241. Treat #241 as a port, not as an independent analytic
  proof.
- #240 can progress independently of #227, but its H1 basis/cellular-homology
  interpretation should stay compatible with jc4's Hurewicz model.
- #230 should not be attempted as a standalone finite-algebra proof; it consumes
  the finite coefficient substrate plus the topological edge-chain independence
  supplied after #228/#229.
- #242 and #243 both depend on giving `SmoothDiffForm`/`exteriorDerivative`
  real chartwise content. Keep the providers separate: #242 is the de Rham
  zero-period primitive theorem; #243 is the Hodge period-payload exactness
  theorem.

# B3 #227 Riemann Bilinear Keystone Split

Status: B3 complete.

## Result

The broad arbitrary-injective direct `sorry` in
`Jacobian/Periods/PeriodFunctional.lean` at
`riemann_classical_real_LI_input` has been replaced by an explicit
classical-basis predicate plus a basis-specific provider:

- `RiemannClassicalPeriodBasis`
- `h1_basis_riemannClassicalPeriodBasis`

The predicate packages the basis-aligned period-coordinate nondegeneracy input
only for cycle families carrying the missing canonical/symplectic
Stokes/Hodge-positive structure. The remaining direct provider is tied to a
concrete `Module.Basis` of `IntegralOneCycle X`; it no longer asserts
nondegeneracy for every arbitrary injective family of cycles. The public #227
theorem now takes an explicit `RiemannClassicalPeriodBasis X σ` witness and
transports its coordinate nondegeneracy back through
`holomorphicOneFormDualEquiv`.

The current arbitrary-injective `σ` statement is not directly provable from the
local scaffold alone: `periodPairing` is still implemented as the zero descent
placeholder, so nondegeneracy must come from the missing classical
canonical/symplectic-basis plus Stokes/Hodge-positivity input.

## Verification

- `lake build Jacobian.Periods.PeriodFunctional` succeeded.
- `lake build Jacobian.Solution` succeeded with existing `declaration uses
  sorry` warnings only.
- `python3 scripts/list-sorries.py --text` succeeded and now reports
  `h1_basis_riemannClassicalPeriodBasis` as the reachable PeriodFunctional
  sorry instead of `riemann_classical_real_LI_input`.
- `bash scripts/build-blueprint.sh` succeeded and refreshed `sorries.jsonl`
  with 324 graph-coloured records. The graph now includes
  `h1_basis_riemannClassicalPeriodBasis` as the direct `c:"sorry"` row; a stale
  ledger row for the rejected coordinate provider was removed.

## Next Recommended Step

Proceed to B4 only after this narrower provider is accepted: port the stable
#227 public theorem to #241 `riemann_classical_real_LI_inputU` in
`Jacobian/Periods/PeriodVectorsLIU.lean`, keeping the universe-`u` work as a
transport layer rather than a second analytic proof.

## Phase 2 B4 Result: #241 Universe-`u` Riemann-Bilinear Split

`Jacobian/Periods/PeriodVectorsLIU.lean` now mirrors the accepted Type-0 split:

- `RiemannClassicalPeriodBasisU` packages the universe-`u` basis-aligned
  period-coordinate nondegeneracy input.
- `h1_basis_riemannClassicalPeriodBasisU` is the narrow remaining provider,
  tied to a concrete `Module.Basis` of `IntegralOneCycleU X`.
- `riemann_classical_real_LI_inputU` is no longer a direct broad `sorry`; it
  consumes the explicit classical-basis witness and transports linear
  independence back through `holomorphicOneFormDualEquiv`.
- The witness is threaded through
  `period_functionals_ℝ_linearIndependentU`,
  `period_vectors_linearIndependent_of_symplecticU`, and
  `periodVectors_linearIndependentU` via
  `symplectic_basis_of_cycles_riemannClassicalPeriodBasisU`.

## Verification

- `lake build Jacobian.Periods.PeriodVectorsLIU` succeeded.
- `lake build Jacobian.Solution` succeeded with existing/expected
  `declaration uses sorry` warnings.
- `python3 scripts/list-sorries.py --text` succeeded and now reports
  `h1_basis_riemannClassicalPeriodBasisU` as the reachable
  `PeriodVectorsLIU.lean` sorry instead of
  `riemann_classical_real_LI_inputU`.
- `bash scripts/build-blueprint.sh` succeeded and refreshed `sorries.jsonl`
  with 323 graph-coloured records. A stale direct Lean row for the old broad
  `riemann_classical_real_LI_inputU` sorry was removed; the blueprint row for
  #241 remains `done`, and the direct provider row for
  `h1_basis_riemannClassicalPeriodBasisU` remains `c:"sorry"`.
- `python3 scripts/blueprint_audit.py` succeeded with the known existing
  `B:decls-exist-but-no-env-leanok` frontier-node report.

## Next Recommended Step

Proceed to B5: address #240 `h1_basis_of_compact_riemann_surfaceU` in
`Jacobian/Periods/H1BasisU.lean`, either discharging it or splitting it into the
narrowest universe-`u` H₁-basis provider coordinated with the Hurewicz/cellular
substrate.

## Phase 2 B5 Result: #240 Universe-`u` H₁ Basis Split

`Jacobian/Periods/H1BasisU.lean` now mirrors the Type-0 H₁-basis proof shape
instead of keeping #240 as one broad direct `sorry`.

- `topologicalGenusU` records the universe-`u` topological genus measured from
  `IntegralOneCycleU X`.
- `stageA_surface_CW_basisU` is the narrow Stage-A provider for the missing
  universe-`u` surface-classification / cellular-homology / singular-vs-cellular
  comparison, producing a `topologicalGenusU`-indexed H₁ basis.
- `stageB_analytic_eq_topologicalGenusU` is the narrow Stage-B provider for the
  universe-`u` analytic/topological genus comparison.
- `h1_basis_of_compact_riemann_surfaceU` is now a sorry-free assembly that
  reindexes the Stage-A basis along the Stage-B equality.

The existing local substrate is not enough to discharge #240 outright:
`IntegralOneCycleU X` is built from `singularHomologyFunctor.{u}` with
`ULift.{u} ℤ` coefficients, while the Type-0 cellular/surface-classification
basis targets `IntegralOneCycle X`.

## Verification

- `lake build Jacobian.Periods.H1BasisU` succeeded.
- `lake build Jacobian.Periods.PeriodVectorsLIU` succeeded.
- `lake build Jacobian.Solution` succeeded with existing/expected
  `declaration uses sorry` warnings.
- `python3 scripts/list-sorries.py --text` succeeded and now reports
  `stageA_surface_CW_basisU` and `stageB_analytic_eq_topologicalGenusU` as the
  reachable `H1BasisU.lean` sorries instead of a direct
  `h1_basis_of_compact_riemann_surfaceU` sorry.
- `bash scripts/build-blueprint.sh` succeeded and refreshed `sorries.jsonl`
  with 324 graph-coloured records. The #240 Lean row is now `c:"sorry-dep"`;
  the two Stage providers are direct `c:"sorry"` rows.
- `python3 scripts/blueprint_audit.py` succeeded with the known existing
  `B:decls-exist-but-no-env-leanok` frontier-node report.

## Phase 2 B6 Result: Type-0 Classical Period-Basis Provider Split

`Jacobian/Periods/PeriodFunctional.lean` now splits the Type-0
`RiemannClassicalPeriodBasis` provider one step further:

- `h1_basis_periodCoordinate_linearIndependent` is the direct remaining
  provider for the exact basis-aligned period-coordinate nondegeneracy field.
- `h1_basis_riemannClassicalPeriodBasis` is now a sorry-free structure assembly
  from that coordinate-linear-independence provider.

The current Hodge and Riemann-bilinear scaffold does not yet prove this
coordinate-row independence directly: it still lacks the actual geometric
bridge from the concrete H₁ basis to the Stokes/Hodge-positive period matrix.
This split preserves all downstream APIs while making the remaining direct
obligation the precise field consumed by the local linear-algebra assembly.

## Verification

- `lake build Jacobian.Periods.PeriodFunctional` succeeded.
- `lake build Jacobian.Periods.PeriodVectorsLIU` succeeded.
- `lake build Jacobian.Solution` succeeded with existing/expected
  `declaration uses sorry` warnings.
- `python3 scripts/list-sorries.py --text` succeeded and now reports
  `h1_basis_periodCoordinate_linearIndependent` as the reachable
  `PeriodFunctional.lean` sorry instead of
  `h1_basis_riemannClassicalPeriodBasis`.
- `bash scripts/build-blueprint.sh` succeeded and refreshed `sorries.jsonl`
  with 325 graph-coloured records. The
  `h1_basis_riemannClassicalPeriodBasis` row is now `c:"sorry-dep"`, and
  `h1_basis_periodCoordinate_linearIndependent` is the direct `c:"sorry"` row.
- `python3 scripts/blueprint_audit.py` succeeded with the known existing
  `B:decls-exist-but-no-env-leanok` frontier-node report.
