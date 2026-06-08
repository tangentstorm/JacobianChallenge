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

## Next Recommended Step

Proceed to Cluster A mapping: survey `Jacobian/Periods/Hurewicz.lean` and the
Section 05 polygonal-model nodes for #228/#229/#230, then add green substrate
nodes for the quotient-path subdivision, partial-side-arc, and edge-chain
independence skeletons. The #228 and #229 lift/side-arc frontiers should be
mapped before #230, since #230 is the downstream coefficient-independence leaf.
