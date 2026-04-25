# Plan for the Jacobian Challenge

This project should be treated as a Mathlib infrastructure project, not as a
single-file proof exercise. The target API in `Jacobian/Challenge.lean` is small,
but honest definitions require substantial missing theory around compact Riemann
surfaces, complex tori, holomorphic forms, integration, and degree theory.

## Current Target

The challenge asks for:

- `genus X` for a compact Riemann surface `X`;
- `Jacobian X` as a compact complex Lie additive group of dimension `genus X`;
- the Abel-Jacobi map `Jacobian.ofCurve`;
- pushforward and pullback maps on Jacobians induced by holomorphic maps;
- the degree of a holomorphic map of compact Riemann surfaces;
- functoriality and the identity `pushforward f (pullback f P) = degree f • P`.

The important constraint is that the definitions should be mathematically real,
not an abstract axiom layer that merely makes the file compile.

This repository tracks v0.3 of the challenge: the surface assumptions no longer
include separate `[Nonempty X]` hypotheses, since `[ConnectedSpace X]` already
provides nonemptiness in the intended Mathlib setting.

## Recommended Construction

Use the analytic period-lattice construction:

```text
Jacobian X = H0(X, Omega1)^dual / H1(X, Z)
```

where a homology class maps into the dual of holomorphic 1-forms by integrating
forms over cycles.

This is the most natural route for the requested API:

- `genus X` can be `finrank C H0(X, Omega1)`;
- the Jacobian is visibly a complex torus;
- the Abel-Jacobi map is defined by integrating from a base point;
- pullback is induced by pullback of holomorphic forms;
- pushforward is induced by homology pushforward or trace;
- `pushforward_pullback` follows from the trace/pullback degree identity.

This recommendation should still be validated against the pinned Mathlib
commit before committing months of work to it. If quotient manifolds,
differential forms, or integration infrastructure are much stronger or weaker
than expected, the construction choice may need to be revisited.

## Phase 0: Project Hygiene

1. Keep `Jacobian/Challenge.lean` as the public target file. Treat it as the
   specification, not as a place to weaken statements while infrastructure is
   being developed.
2. Keep `Jacobian.lean` as the root export module.
3. Pin Lean and Mathlib through `lean-toolchain`, `lakefile.toml`, and
   `lake-manifest.json`.
4. Add new files only when they correspond to reusable theory, for example:

```text
Jacobian/ComplexTorus.lean
Jacobian/RiemannSurface.lean
Jacobian/HolomorphicForms.lean
Jacobian/Periods.lean
Jacobian/AbelJacobi.lean
Jacobian/Degree.lean
```

## Phase 0.5: Inventory the Pinned Mathlib Commit

Before committing to any construction, audit the pinned Mathlib commit for the
specific infrastructure that the period-lattice route needs.

Concrete yes/no checks:

- quotient manifolds by discrete group actions;
- charted-space and manifold instances for quotients;
- topological group quotients by additive subgroups;
- finite-dimensional real and complex lattices;
- smooth differential forms on manifolds;
- holomorphic differential forms on complex manifolds;
- exterior derivative and closedness of holomorphic 1-forms;
- integration of 1-forms along paths;
- integration over chains or homology classes;
- singular homology or a usable cycle theory;
- local power-series or normal-form theory for holomorphic maps between
  one-dimensional complex manifolds;
- local multiplicity, ramification, and finite-fiber results.

This phase should produce an inventory file with exact Mathlib names, missing
lemmas, and candidate files to extend. The period-lattice construction remains
the default, but the inventory determines the order of attack.

## Phase 1: Complex Tori

Build the reusable theory of quotients of finite-dimensional complex vector
spaces by full lattices.

Needed API:

- lattices in finite-dimensional real or complex vector spaces;
- quotient additive groups by discrete subgroups;
- topological group structure on `V / Lambda`;
- compactness for full-rank lattices;
- complex manifold structure on the quotient;
- Lie additive group structure;
- maps induced by continuous linear maps preserving lattices.

This phase supports the group, topology, compactness, manifold, and Lie group
instances for `Jacobian X`.

### Phase 1 — Sub-status (2026-04-25)

The lower (group + topology) layer of Phase 1 is mostly done; the higher
(manifold + Lie group) layer is intentionally untouched pending closure of
the lower layer.

Stable in `Jacobian/ComplexTorus/`:

- `Basic.lean`            — `mk_continuous`, `mk_isOpenQuotientMap`, `mk_isOpenMap`, `map_continuous`
- `Mk.lean`               — `mk_zero`, `mk_eq_iff`, `mk_eq_zero_iff`
- `MapMk.lean`            — `map_zero`, `map_mk_add`
- `Surjective.lean`       — `map_surjective`
- `MapInjective.lean`     — `map_injective_of_preimage_subset`
- `NhdsZero.lean`         — `nhds_zero_eq`
- `IsClosedSubgroup.lean` — `t2Space_quotient_of_isClosed` (now
  load-bearing: the `FullComplexLattice.quotient_t2` field has been
  dropped and the structure-level instance derives T2 from `isClosed`)
- `Compact.lean` — `compactSpace_quotient_of_cover` (the
  `FullComplexLattice.quotient_compact` field has now also been
  dropped; `quotient_compactSpace` is derived inline in StatementBank
  from the new `fundamentalDomain` + `fundamentalDomain_isCompact` +
  `fundamentalDomain_covers` fields)
- `Neg.lean`              — `mk_neg`, `continuous_neg`
- `Add.lean`              — `mk_add`, `continuous_add`
- `Smul.lean`             — `mk_zsmul`, `mk_nsmul`
- `OfClm.lean`            — `mapClm`, `mapClm_continuous`

### Phase 1.5 — manifold layer (recon results, 2026-04-25)

Aristotle's `ManifoldRecon.lean` packet (`bbdcb3f4`) returned a concrete
survey of the Mathlib API surface. Headline findings:

1. **Quotient-manifold machinery does NOT exist in Mathlib.** No
   "discrete properly-discontinuous group action → manifold quotient"
   result anywhere under `Mathlib/Geometry/Manifold/`. Hand-rolled
   construction required.
2. `ProperlyDiscontinuousVAdd` exists but is not wired to manifolds.
3. Building blocks for a hand-rolled `ChartedSpace`: `ChartedSpace.mk`,
   `OpenPartialHomeomorph.mk`, `QuotientAddGroup.isOpenMap_coe`,
   `QuotientAddGroup.continuous_mk`, `QuotientAddGroup.mk_surjective`,
   `chartedSpaceSelf`. These are the pieces we need to assemble.
4. `LieAddGroup` infrastructure (`instNormedSpaceLieAddGroup`) is
   present for `V` but no quotient version exists.
5. Standard chart-transport plan: pick `r > 0` with
   `Metric.ball 0 r ∩ Λ.subgroup = {0}`; for each `v : V`, build
   `chart_v` whose target is `Metric.ball v (r/2)` and source is
   `mk '' Metric.ball v (r/2)`. Open by `isOpenMap_coe`, injective on
   small enough balls thanks to discreteness of `Λ.subgroup`.
6. `IsManifold` will follow from `HasGroupoid` + the fact that chart
   transitions are translations (smooth in `V`).
7. `ZLattice` infrastructure provides
   `ZLattice.isAddFundamentalDomain` and `comap_discreteTopology`,
   useful if/when `FullComplexLattice` is refactored to a `ZLattice`
   variant.

The full recon notes live in `Jacobian/ComplexTorus/ManifoldRecon.lean`.

Missing pieces flagged by Aristotle (need to be built):
- discreteness of a closed additive subgroup in a finite-dimensional
  normed space (`Λ.isClosed → DiscreteTopology Λ.subgroup`);
- injectivity of `mk` on small balls;
- continuous local section of `mk` over a small ball.

Once those small lemmas exist, the construction outline can be turned
into a real proof packet.

### Phase 1.5b — ZLattice bridge feasibility (recon results, 2026-04-25)

Aristotle's `ZLatticeRecon.lean` packet (`a68d37f4`, returned
COMPLETE_WITH_ERRORS) found that bridging `IsZLattice ℝ L` to
`FullComplexLattice V` is **feasible**:

- `IsZLattice K L` is parametric in `K`. Our `NormedSpace ℂ V` upgrades
  to `NormedSpace ℝ V` via the scalar tower, and `IsZLattice ℝ L` works
  on the resulting space.
- `FiniteDimensional ℝ V` follows from `FiniteDimensional ℂ V` via
  `Module.Finite.trans`, and `ProperSpace V` from
  `FiniteDimensional.proper_real`.

Of the five `FullComplexLattice` fields:

| Field | Status |
|-------|--------|
| `subgroup` | trivial (`L.toAddSubgroup`) |
| `isClosed` | proved (via a small `discreteTopology_toAddSubgroup` bridge) |
| `fundamentalDomain` | proved (`closure (ZSpan.fundamentalDomain bR)`) |
| `fundamentalDomain_isCompact` | proved (`fundamentalDomain_isBounded.isCompact_closure`) |
| `fundamentalDomain_covers` | sketched, sorry pending packaging helper |

The remaining gap is a small bounded packaging lemma
`ZLattice.exists_sub_mem_closure_fundamentalDomain`: convert
`ZSpan.exist_unique_vadd_mem_fundamentalDomain` from `vadd` form to
subtraction form, transport membership via
`Module.Basis.ofZLatticeBasis_span`, and weaken `∈ fundamentalDomain`
to `∈ closure fundamentalDomain`. Aristotle's first attempt used
`grind` and failed; replaced with a clean `sorry` carrying the proof
sketch.

This is the natural next bounded packet at this layer: prove that
single helper, then `fullComplexLatticeOfZLattice` is sorry-free.

## Phase 2: Compact Riemann Surfaces and Holomorphic Forms

Define the vector space of holomorphic 1-forms on a compact Riemann surface.

Needed API:

- cotangent spaces and smooth differential 1-forms on complex manifolds;
- holomorphicity condition for 1-forms;
- vector space structure over `C`;
- finite dimensionality for compact Riemann surfaces;
- definition of genus as the dimension of this space.

Finite-dimensionality is not a small linear-algebra lemma after the definitions
are in place. It likely needs serious compact Riemann surface theory, for
example Riemann-Roch, Hodge/de Rham machinery, or an equivalent analytic route.

The theorem `genus_eq_zero_iff_homeo` is especially deep with this definition.
It likely depends on uniformization or the classification of genus-zero compact
Riemann surfaces, not just local complex analysis.

## Phase 3: Integration and Periods

Develop integration of differential forms over paths and cycles on manifolds.

Needed API:

- integration of 1-forms along smooth paths;
- chain-level or homology-level integration;
- closedness of holomorphic 1-forms;
- invariance of integrals under homology;
- the period pairing

```text
H1(X, Z) -> H0(X, Omega1)^dual
```

- proof that the image is a full lattice.

This is probably the central technical bottleneck.

The full-lattice statement is not a minor final check. It is essentially the
nondegeneracy of the period pairing, normally proved using Riemann bilinear
relations or equivalent Hodge-theoretic input. This may be one of the largest
single mathematical results needed before the Jacobian can be made compact.

## Phase 4: Define the Jacobian

Once phases 1-3 exist:

```text
Jacobian X := H0(X, Omega1)^dual / periodLattice X
```

Then prove:

- additive commutative group instance;
- topological space, Hausdorff, compact space instances;
- complex charted-space and manifold instances;
- Lie additive group instance;
- dimension equals `genus X`.

There is a universe issue to handle explicitly. The challenge asks for
`Jacobian (X : Type u) : Type u`, while a concrete period quotient may naturally
land in a small universe, for example as a quotient of a finite-dimensional
space such as `Fin (genus X) -> C`. The implementation needs a deliberate bridge
such as `ULift` or a universe-polymorphic construction, not an accidental
universe mismatch.

## Phase 5: Abel-Jacobi Map

For a base point `P : X`, define:

```text
ofCurve P Q = class of (omega |-> integral from P to Q of omega)
```

The key proof obligation is path-independence modulo periods.

Then prove:

- `ofCurve_self`;
- holomorphicity of `ofCurve P`;
- injectivity when `0 < genus X`.

The injectivity theorem is not a small local calculation. It is a substantial
classical theorem about Abel-Jacobi maps. For genus at least one, it is one of
the facts that prevents degenerate fake Jacobian definitions from satisfying
the challenge API.

## Phase 5.5: Abel-Jacobi Injectivity and Point Separation

Treat `ofCurve_inj` as its own theorem-level project.

Likely prerequisites:

- enough holomorphic 1-forms or meromorphic functions to separate points;
- Riemann-Roch or an equivalent compact Riemann surface theorem;
- compatibility between the separation theorem and the Abel-Jacobi integral
  definition;
- special handling of genus one versus genus at least two if the proof naturally
  splits.

This theorem is one of the challenge's anti-hack checks. A fake zero Jacobian or
constant Abel-Jacobi map cannot satisfy it when `0 < genus X`.

## Phase 6: Trace, Pushforward, and Degree

Define the degree of a holomorphic map of compact Riemann surfaces.

The intended behavior:

- constant maps have degree `0`;
- nonconstant maps have positive finite degree;
- degree is computed by generic fiber cardinality with ramification
  multiplicity.

Needed API:

- local normal form for nonconstant holomorphic maps between Riemann surfaces;
- isolated zeros and local multiplicity;
- finite fibers for nonconstant maps between compact Riemann surfaces;
- branched covering behavior;
- functoriality of degree under composition.

For `f : X -> Y` holomorphic:

- pullback of forms gives `H0(Y, Omega1) -> H0(X, Omega1)`;
- dualizing gives a linear map in the opposite direction;
- compatibility with period lattices gives `Jacobian Y -> Jacobian X`;
- pushforward should be defined using the trace map on forms, or from an
  equivalent construction proved compatible with trace.

The trace-of-forms route is preferred because it makes the final identity
structural:

```text
trace_f (pullback_f omega) = degree(f) * omega
```

This also constrains the degree definition. It may be cleaner to first define
the trace map and the scalar appearing in `trace_f (pullback_f omega)`, then
prove that this scalar agrees with the geometric branched-cover degree.

## Phase 7: Pushforward and Pullback API

Then prove:

- `pushforward_id_apply`;
- `pushforward_comp_apply`;
- `pullback_id_apply`;
- `pullback_comp_apply`;
- holomorphicity of both maps;
- `pushforward_pullback`.

The final identity is a serious classical compatibility theorem, not a formal
consequence of the map definitions alone. It should be proved from the
trace-pullback theorem:

```text
trace_f (pullback_f omega) = degree(f) * omega
```

or the equivalent statement on homology/period pairings.

## Phase 7.5: Genus-Zero Classification

Treat `genus_eq_zero_iff_homeo` as its own theorem-level project.

With `genus X := finrank C H0(X, Omega1)`, this theorem is essentially a
classification statement for compact genus-zero Riemann surfaces. Plausible
routes include:

- uniformization;
- Riemann-Roch plus the construction of a degree-one meromorphic function;
- classification of compact connected oriented surfaces plus compatibility
  between topological and analytic genus.

This is another anti-hack theorem: it prevents defining `genus` to be constantly
zero or otherwise disconnected from the topology of the surface.

## Phase 8: Mathlib Integration Strategy

Do not try to PR the entire challenge as one contribution. Split into reusable
layers:

1. quotient complex tori;
2. differential forms and holomorphic 1-forms on complex manifolds;
3. path and cycle integration for 1-forms;
4. compact Riemann surface facts;
5. period lattices;
6. Jacobian definition and basic API;
7. Abel-Jacobi map;
8. pushforward, pullback, and degree.

Each layer should have independent examples and tests before being used in the
challenge file.

## Anti-Hack Audit

The challenge deliberately includes API that rules out easy fake definitions.
The implementation should keep an explicit audit trail showing where the chosen
construction satisfies these checks:

- `genus_eq_zero_iff_homeo` ties `genus` to the topology of the surface, so
  `genus X := 0` cannot work.
- `ofCurve_inj` forces the Abel-Jacobi map to be nonconstant and injective for
  positive genus, so `Jacobian X := PUnit` cannot work.
- compact complex Lie group instances force `Jacobian X` to have the expected
  torus-like analytic structure.
- `pushforward_pullback` forces pushforward, pullback, and degree to interact
  through the classical trace/pullback relation, not arbitrary homomorphisms.

This audit is not just rhetoric. Each item should point to the corresponding
construction theorem once the project has real files.

## Rough Size

The phases are not comparable in size.

- Project setup and inventory: days.
- Complex tori: weeks for an expert if quotient-manifold infrastructure is
  close; longer if quotient manifolds must be built first.
- Holomorphic forms and finite-dimensionality: months, depending on existing
  differential-form and compactness theory.
- Integration, periods, and full-lattice theorem: likely the largest part;
  potentially multi-person-months or more.
- Abel-Jacobi injectivity and genus-zero classification: each a serious compact
  Riemann surface theorem, likely months unless strong prerequisites already
  exist.
- Trace, degree, and push-pull compatibility: months, because they require
  local holomorphic map theory and global compatibility.

The expected output is many reusable Mathlib layers, not a short local patch.

## Delegation Strategy for Aristotle

This plan is a roadmap, not yet a good unit of work for a cloud formalizer.
Claude should manage the project and use Aristotle for small, file-scoped Lean
tasks after definitions and theorem statements have been chosen.

Claude-owned responsibilities:

- inventory the pinned Mathlib commit;
- decide which construction route to pursue;
- create the module skeleton;
- state intermediate definitions and lemmas;
- keep theorem names and public APIs stable;
- split work into bounded Aristotle jobs;
- review returned patches before integration;
- repair imports and resolve conflicts between jobs;
- maintain a local log of Aristotle prompts, job ids, target files, and status.

Aristotle-owned responsibilities:

- prove named lemmas in one target file;
- fill a tightly scoped theorem family;
- formalize a bounded construction from already-stated definitions;
- improve or simplify proofs without changing public statements;
- report blockers when a statement needs a missing prerequisite.

Do not ask Aristotle to "solve the Jacobian challenge" or choose the global
definition of the Jacobian. Ask it to complete precise local proof tasks.

Suggested job queues:

```text
Queue A: Mathlib inventory and name discovery
Queue B: complex torus infrastructure
Queue C: differential forms and holomorphic forms
Queue D: path integration, chains, and periods
Queue E: Jacobian definition and basic instances
Queue F: Abel-Jacobi map and path-independence
Queue G: trace, degree, pushforward, and pullback
Queue H: anti-hack theorems
```

Each Aristotle job should specify:

- working directory;
- target file path;
- exact theorem or definition names;
- allowed write scope;
- files that must not change;
- whether imports may be adjusted;
- expected build command;
- proof style constraints;
- fallback behavior if the statement is too strong.

Example job shape:

```text
Working directory: C:\ver\JacobianChallenge
Target file: Jacobian/ComplexTorus/Basic.lean
Allowed writes: only Jacobian/ComplexTorus/Basic.lean
Task: prove the listed quotient-additive-group lemmas for a lattice quotient.
Do not change public theorem statements.
Do not edit Jacobian/Challenge.lean.
Expected verification: lake build Jacobian.ComplexTorus.Basic
If blocked, add a short comment listing the missing prerequisite theorem names.
```

Claude should prefer many small jobs with disjoint write scopes over one large
job. If Aristotle fails on a theorem, Claude should split the theorem into
smaller helper lemmas, add those statements locally, and resubmit only the
smallest blocked part.

Good Aristotle tasks:

- "Fill the proofs of these three quotient-map continuity lemmas."
- "Prove this map descends to the quotient under the stated lattice-preserving
  hypothesis."
- "Show these two definitions of the induced homomorphism are extensionally
  equal."
- "Prove the local finite-dimensional linear algebra lemmas used by
  `ComplexTorus.Basic`."

Bad Aristotle tasks:

- "Build the Jacobian of a Riemann surface."
- "Formalize Riemann surface theory."
- "Fix all sorries in this project."
- "Choose the best definition of pushforward."

The practical workflow should be:

1. Claude writes or reviews the target theorem statements.
2. Claude submits one Aristotle job per file or theorem cluster.
3. Claude records the prompt and job id in a local task log.
4. Claude retrieves the result and reviews the patch.
5. Claude either integrates it, splits the task smaller, or marks the missing
   prerequisite as a new infrastructure item.

## Main Risks

- The quotient manifold theory for lattices may not be complete enough in
  Mathlib yet.
- Integration of forms on manifolds may require a large amount of foundational
  work.
- Finite-dimensionality of holomorphic 1-forms is a serious theorem.
- The genus-zero classification theorem is not just an API lemma.
- Abel-Jacobi injectivity and `pushforward_pullback` depend on deep classical
  Riemann surface theory.

## First Concrete Milestone

The first useful milestone is not to solve any sorry in `Challenge.lean`.

Instead, build a standalone file proving that a finite-dimensional complex
vector space modulo a full lattice is a compact complex Lie additive group, with
maps induced by lattice-preserving continuous linear maps. That result is
reusable, reviewable, and directly needed for the eventual Jacobian definition.

The bridge back to the challenge is:

```text
period pairing gives periodLattice X in H0(X, Omega1)^dual
complex torus infrastructure gives Jacobian X
complex torus instances discharge the group/topology/compact/manifold/Lie API
period integration gives ofCurve
trace and pullback compatibility give pushforward, pullback, and degree
```
