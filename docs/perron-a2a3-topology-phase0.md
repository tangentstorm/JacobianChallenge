# Perron A2/A3 Topology Phase 0 Plan

Tracking: GitHub issue #232, Path A.

This note prices the topological stage-construction work behind the Perron
engine interfaces in `Jacobian.HolomorphicForms.StageExhaustion`.  It is a
planning document only: it does not add Lean declarations, change theorem
statements, or claim that the A2/A3 frontier obligations are already solved.

## Scope

The current Perron engine needs two topological inputs before the harmonic
Dirichlet/conjugate tasks can run:

- A2, `exists_stageBorderedExhaustion`: construct an increasing bordered or
  chart-polygon exhaustion whose frontiers have finite chart control and which
  eventually contains every selected compact set.
- A3, `exists_stageCutSystem`: for a fixed exhaustion, construct cut domains
  inside the stages, keep the selected compacta eventually inside the cut
  domains and away from the cut sets, and make each cut domain simply connected
  enough for single-valued harmonic conjugates.

The document is intentionally topology-facing.  It stops before Perron
existence, harmonic boundary estimates, Cauchy estimates, Montel extraction, or
global gluing.

## Current Interfaces

`StageSelectedCompactFamily` packages the compact sets later consumed by
eventual-containment arguments.  It supplies an index type, a set-valued compact
family, and `isCompact_compact` for every index.

`StageBoundaryChartData` is the finite frontier-control payload for one stage:
the boundary chart index is finite, each boundary piece lies in the source of
its assigned chart, and `frontier stage` is covered by the union of the boundary
pieces.

`StageBorderedExhaustion X selected` is exactly the A2 output.  It asks for:

- `stage : Nat -> Set X`;
- `IsOpen (stage n)`;
- monotonicity `stage m subset stage n` for `m <= n`;
- eventual containment of every selected compactum;
- finite boundary-chart data for every stage.

`StageConjugateReady X cutDomain` is the A3 predicate consumed by harmonic
conjugate work.  It requires `IsOpen cutDomain` and
`IsSimplyConnected cutDomain`.

`StageCutSystem X selected exhaustion` is exactly the A3 output.  It asks for:

- `cutDomain n` and `cutSet n`;
- `cutDomain n subset exhaustion.stage n` and
  `cutSet n subset exhaustion.stage n`;
- disjointness of each cut domain from its cut set;
- eventual containment of selected compacta in cut domains;
- eventual avoidance of selected compacta by cut sets;
- `StageConjugateReady` for every cut domain.

The two frontier obligations are deliberately narrow:
`exists_stageBorderedExhaustion` constructs A2 from `_e : X ~= OnePoint C` and
the selected compact family, while `exists_stageCutSystem` constructs A3 after
an A2 exhaustion has already been fixed.

## Construction Plan

### A2: bordered/chart-polygon exhaustion

The planned construction should use `_e : X ~= OnePoint C` only as topological
control data.  It should not pull analytic maps back along `_e`; `_e` is a
homeomorphism, not a conformal chart.  The role of `_e` is to transfer simple
nested compact/open sets from the sphere model to `X`, choose marked points and
coarse collars, and arrange eventual containment of the selected compacta.

The preferred A2 route is:

1. Choose a nested sequence of compact cores in `OnePoint C`, away from small
   model neighborhoods of the two marked ends and with collars between
   successive cores.
2. Pull the resulting open stage neighborhoods back along `_e`.  This gives
   open stages and monotonicity by `Homeomorph` preimage/image transport.
3. Use compactness of each selected compactum and the fact that the stages
   exhaust the model surface to prove eventual containment.  The expected Lean
   shape is a compact finite-subcover argument, not a pointwise choice left
   unbounded in `n`.
4. Replace the coarse model-boundary description with a finite chart cover of
   `frontier (stage n)`.  For each frontier point, choose a source chart of
   `X`; compactness/closedness of the frontier should reduce the cover to
   finitely many charts.  This is exactly the content of
   `StageBoundaryChartData`.
5. If the exact boundary geometry is not formalized yet, keep the first A2
   proof slices limited to the finite frontier chart-cover and eventual
   containment primitives.  Avoid smuggling smooth boundary regularity into
   `StageBoundaryChartData`; the current interface only asks for finite
   topological chart control.

The hard part is not proving that compact sets have finite chart subcovers.
The hard part is choosing a stage sequence whose frontiers are sufficiently
controlled, nested, and compatible with later cuts while living in the
topology of a compact Riemann surface rather than a fixed planar domain.

### A3: cut systems

The planned A3 construction starts with a fixed `StageBorderedExhaustion`.
For each stage, choose a finite cut set inside the stage so that removing it
leaves an open cut domain that is simply connected enough for conjugate
construction.

The preferred A3 route is:

1. Work stage-by-stage from the finite boundary-chart data and the topological
   sphere input.  The cut set should be a finite union of chart arcs or
   polygonal chords connecting the relevant boundary/marked pieces.
2. Define `cutDomain n` as the stage with those cut arcs removed, or as an
   explicitly open side of that removal if the raw complement is not open in
   the desired topology.
3. Prove `cutDomain_subset_stage`, `cutSet_subset_stage`, and
   `cutDomain_disjoint_cutSet` directly from the construction.
4. Arrange cuts in collars outside each selected compactum once `n` is large.
   This gives both eventual containment in `cutDomain n` and eventual
   disjointness from `cutSet n`.
5. Prove `StageConjugateReady` by reducing the cut domain to a disk-like or
   contractible model.  In Lean, `IsSimplyConnected s` is just
   `SimplyConnectedSpace s`, and `SimplyConnectedSpace.ofContractible` is the
   clean target if the cut domain is shown contractible or homeomorphic to a
   contractible planar polygon/disk.

The hard part is the disk-like reduction.  The existing polygonal-model
development already records the classical theme that cutting along enough
non-tree edges unfolds a surface into a disk, but those declarations are in the
Periods layer and are not currently an A3-ready theorem about arbitrary
Perron stages.  A3 should reuse the ideas and any clean lemmas that fit, but it
should not cite a Periods statement as if it already provides
`StageCutSystem`.

## Mathlib/Project Substrate

Verified in this checkout:

- `StageSelectedCompactFamily`, `StageBoundaryChartData`,
  `StageBorderedExhaustion`, `StageConjugateReady`, `StageCutSystem`,
  `exists_stageBorderedExhaustion`, and `exists_stageCutSystem` live in
  `Jacobian/HolomorphicForms/StageExhaustion.lean`.
- `IsSimplyConnected` is defined in
  `Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected` as
  `SimplyConnectedSpace s`.  The same file provides
  `IsSimplyConnected.simplyConnectedSpace`,
  `IsSimplyConnected.isPathConnected`,
  `Homeomorph.isSimplyConnected_image`,
  `Homeomorph.isSimplyConnected_preimage`, and
  `SimplyConnectedSpace.ofContractible`.
- Compact finite-subcover tools are present in
  `Mathlib.Topology.Compactness.Compact`, including
  `IsCompact.elim_finite_subcover`,
  `IsCompact.elim_nhds_subcover`,
  `IsCompact.elim_nhdsWithin_subcover`, and
  `CompactSpace.elim_nhds_subcover`.
- Frontier tools are present in Mathlib topology files:
  `frontier` is defined in `Mathlib.Topology.Defs.Basic`, and
  `Mathlib.Topology.Closure` provides `frontier_eq_closure_inter_closure`,
  `frontier_subset_closure`, `IsOpen.frontier_eq`,
  `isClosed_frontier`, `frontier_inter_subset`,
  `frontier_union_subset`, and related identities.
- Hausdorff/regular separation tools are available in
  `Mathlib.Topology.Separation.Hausdorff` and
  `Mathlib.Topology.Separation.Regular`, including compact closedness
  (`IsCompact.isClosed`) and neighborhood-disjointness lemmas such as
  `IsCompact.disjoint_nhdsSet_nhds` and
  `disjoint_nhdsSet_nhdsSet` under the appropriate separation hypotheses.
- `Mathlib.Topology.Connected.LocPathConnected` provides
  `IsOpen.locPathConnectedSpace`, useful if later conjugate or branch-lifting
  tools require local path connectedness of open cut domains.
- Project polygon/cut guidance is present in `Jacobian/Periods` and
  `tex/sections/05-polygonal-model.tex`: `DualGraphCut.lean` names
  `cut_along_nonTree_yields_unfoldedDisk`,
  `EdgeWord.lean` records standard side-pairing relations, and
  `Polygon4gCellular.lean` includes `polygon4g_zero_contractibleSpace`.
  These are guidance/substrate, not a completed A3 proof for the Perron
  stage interface.

## Hard vs Routine Work

Routine or medium-sized:

- Transporting open sets, compact containment, and frontier statements along
  the fixed homeomorphism `_e`.
- Turning local chart neighborhoods along a compact frontier into a finite
  `StageBoundaryChartData` index using compact finite-subcover lemmas.
- Proving monotonicity and eventual containment once a concrete nested stage
  sequence has been chosen.
- Proving the structural fields of `StageCutSystem` after the cut set and cut
  domain are defined explicitly.

Hard own-subtree:

- Choosing a concrete nested bordered/chart-polygon exhaustion in the Lean
  topology that has the right frontier-control behavior and is stable under
  later cut insertion.
- Formalizing enough chart-arc or polygonal cut geometry inside each stage to
  state and prove that the cut domain is disk-like.
- Bridging the classical "cut surface to polygon/disk" material from the
  Periods/polygonal-model development into the local `StageCutSystem`
  interface without importing inappropriate homology-period assumptions.
- Producing `IsSimplyConnected cutDomain` in the exact Mathlib form required by
  `StageConjugateReady`.

## Proposed Commit Slices

1. A2 compact-frontier chart-cover helper layer: for a compact frontier covered
   by chart sources, materialize a finite `StageBoundaryChartData`-style index.
2. A2 model-stage sequence: define the chosen nested model stages on
   `OnePoint C`, pull them back by `_e`, and prove openness/monotonicity.
3. A2 selected-compact containment: prove every `selected.compact i` is
   eventually inside the pulled-back stages.
4. A2 assembly: combine the stage sequence, containment, and finite boundary
   chart data into `Nonempty (StageBorderedExhaustion X selected)`, or isolate
   the narrowest remaining frontier if the bordered-stage geometry is still
   missing.
5. A3 cut geometry interface: define a local data structure or helper theorem
   for a finite chart-arc cut set in one stage, with subset/disjointness fields.
6. A3 selected-compact avoidance: arrange the cut collars away from each
   selected compactum eventually.
7. A3 simply-connected reduction: prove the cut domain is homeomorphic or
   homotopy equivalent to a contractible disk/polygon model, then discharge
   `IsSimplyConnected`.
8. A3 assembly: produce `Nonempty (StageCutSystem X selected exhaustion)`, or
   replace the current frontier with exactly one narrower cut-domain
   simply-connectedness provider.

## Risks

- The current `StageBorderedExhaustion` interface has finite chart coverage of
  `frontier stage`, but it does not record smooth boundary regularity.  That is
  intentional for A2; later analytic tasks must not assume more regularity than
  the interface provides.
- `IsSimplyConnected` is a typeclass-style predicate on the subtype
  `cutDomain`.  Showing a set is visually "a disk with cuts" is not enough; the
  proof must either build a contractibility instance or transport simple
  connectedness through a homeomorphism/homotopy equivalence.
- The Periods polygonal-model files are not drop-in Perron-stage topology.
  They can guide the cut proof and may supply reusable local lemmas, but A3
  likely needs its own stage-relative formulation.
- A topological pullback along `_e` is valid for stage control only.  It must
  not be used to create holomorphic maps or analytic coordinates.

## Conclusion

A2 and A3 are not one-line theorem applications.  The likely successful route
is a staged local topology development: first finite frontier chart control and
eventual compact containment, then explicit cut geometry, then a disk-like
simple-connectedness proof in Mathlib's `IsSimplyConnected` form.  The next
Lean work should keep the existing frontier obligations as the public
interfaces, prove routine assembly around them, and isolate at most one narrow
topological provider if the disk-like cut-domain construction is the remaining
hard leaf.
