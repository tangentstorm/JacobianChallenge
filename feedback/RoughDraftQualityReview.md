# Mathlib-Style Rough-Draft Review: Current Codebase

Review date: 2026-04-25.

Scope: current Lean source under `Jacobian/`, with special attention to the
README claims that the complex-torus quotient, projection smoothness, and
`LieAddGroup` layers are at 100%. I am taking buildability as given.

Framing: this is not a literal mathlib submission plan. The project goal is a
rigorous rough draft of the Jacobian construction, and mathlib is being used as
the quality reference: canonical abstractions, stable APIs, minimal
assumptions, and mathematically faithful definitions.

## Executive Summary

The complex-torus Queue B layer is now much stronger than the older feedback
files describe. Core quotient declarations have moved out of
`StatementBank`, the umbrella no longer re-exports reconnaissance modules, the
`StatementBank` witness statements now ask for real `IsManifold` and
`LieAddGroup` instances, and the `mk`/addition/negation smoothness files are
actually wired into `Jacobian.ComplexTorus`.

So the README's "100%" lines are defensible if they mean:

- the project-local `FullComplexLattice` quotient API builds;
- a project-local charted-space/manifold instance exists;
- `mk`, addition, and negation are proved `ContMDiff`;
- the final `LieAddGroup` instance is registered.

They should not be read as "fully polished to mathlib style." The code is still
a research scaffold with project-local abstractions, global instances that
would need review, an opaque period pairing, and a chart-local integration
definition that is not yet the mathematical pullback of a differential 1-form.

## Major Rough-Draft Issues

### 1. `ComplexTorus.Defs` imports the challenge spec with many `sorry`s

`Jacobian/ComplexTorus/Defs.lean` imports `Jacobian.Challenge`. That pulls the
entire public challenge file, whose central declarations are still `sorry`:
`genus`, `Jacobian`, compactness, manifold and Lie group instances,
`ofCurve`, pushforward, pullback, degree, and the final push-pull theorem.

For project development this is harmless if the file builds, but it weakens the
rough draft as an independent construction. The torus quotient infrastructure
should ideally be independent of the challenge API. A cleanup pass should split
the reusable torus material into files that import only Mathlib, then let the
challenge layer import those files.

### 2. `FullComplexLattice` is still a project abstraction, not a mathlib API

`FullComplexLattice` in `Jacobian/ComplexTorus/Defs.lean` stores an
`AddSubgroup`, closedness, discreteness, and a compact fundamental domain with
a covering property. This is a practical local interface, but the rough draft
should eventually explain its relation to existing `Submodule Z`, `ZLattice`,
or a generic cocompact-discrete subgroup predicate.

The current structure also does not state finite-dimensionality. Mathlib
manifolds can be infinite-dimensional, so this is not a type error, but a
"complex torus" in the algebraic-geometric sense should eventually carry a
finite-dimensional model. At minimum, name the current object as a quotient of
a normed complex additive group by a full discrete cocompact subgroup, not as
the final Jacobian torus object.

### 3. The chart construction is project-valid but not yet polished for mathlib

The chart layer is logically plausible:

- discreteness gives an isolation radius;
- small balls inject into the quotient;
- `localSection` is the inverse on the image;
- `chartAtBall` packages an `OpenPartialHomeomorph`;
- transition maps are locally translations;
- translations are smooth.

For a polished rough draft, I would still tighten the presentation:

- `chartAtPoint` chooses a representative and an isolation radius separately
  at every chart construction. This is acceptable but hard to read and brittle
  under simplification.
- `localSection` is a global `Function.invFunOn` with arbitrary values outside
  the chart image. A mathlib API should expose the partial inverse as a
  `PartialEquiv`/`OpenPartialHomeomorph` construction directly.
- The proofs rely on definitional equalities such as
  `((chartAt V q).symm : V -> quotient V Lambda) = mk V Lambda := rfl`.
  That is fine for local staging, but mathlib reviewers will want the intended
  chart construction and coercions to be expressed by named lemmas.

### 4. Global instances need a typeclass-search audit

The quotient layer declares global instances for compactness, connectedness,
path-connectedness, first-countability, second-countability under a hypothesis,
charted space, manifold, `ContMDiffAdd`, and `LieAddGroup`.

Some are natural, but global instances should still be audited carefully. In
particular:

- `CompactSpace (quotient V Lambda)` is not just quotient topology; it depends
  on the selected `FullComplexLattice` data.
- `PathConnectedSpace (quotient V Lambda)` is proved by a generic quotient
  instance, but the file comment mentions the continuous image argument. The
  declaration should either use the documented proof path or cite the exact
  Mathlib instance in the comment.
- `FullComplexLattice.isDiscrete` is marked as an instance. This is convenient,
  but it means any `Lambda : FullComplexLattice V` contributes an instance for
  `DiscreteTopology Lambda.subgroup`. That deserves scrutiny before export.

### 5. Many quotient lemmas are wrappers around existing Mathlib declarations

Files such as `Basic.lean`, `GenericQuotient.lean`, `Mk.lean`,
`MkBundled.lean`, `MkRange.lean`, `MkImage.lean`, and related map lemmas are
mostly short wrappers around `QuotientAddGroup` API.

That is useful for this project. Before cleanup, classify each lemma as one of:

- delete and use the existing Mathlib name;
- generalize to `AddSubgroup G` or `Submodule` and contribute under the right
  namespace;
- keep only in the project namespace as notation glue.

### 6. `chartedForm` is not the correct chart pullback of a 1-form

This is the biggest mathematical issue outside the torus layer.

`Jacobian/Periods/ChartedForm.lean` defines

```lean
chartedForm c omega e := omega.toFun (c.symm e)
```

as an `E -> E ->L[Complex] Complex`. A true chart-local expression for a
1-form must also apply the tangent map of `c.symm` at `e`:

```text
v |-> omega(c.symm e) (D(c.symm)_e v)
```

The current definition only evaluates the section at the point. It ignores
how tangent vectors in model coordinates are transported to the manifold. If
Lean accepts the type, it is because the tangent-space model has been made
definitionally convenient, not because the pullback has been formalized.

Consequences:

- `pathIntegralInChart` currently integrates the wrong local representative in
  general.
- The later period pairing cannot be made independent of charts from this
  definition alone.
- The README's period-layer progress should be read as API scaffolding, not as
  genuine differential-form integration.

### 7. The period pairing is opaque, so analytic Jacobian progress is only a
group-shaped placeholder

`Jacobian/Periods/PeriodFunctional.lean` introduces `opaque periodPairing`.
`AnalyticJacobianGroup` is then the quotient of the dual of holomorphic forms
by the range of that opaque map.

This is good naming scaffolding, but no downstream theorem should treat it as a
completed mathematical construction. The period subgroup still needs:

- a real multi-chart path integral;
- a homology/cycle interface with boundaries;
- Stokes or a replacement theorem;
- discreteness and full-rank/nondegeneracy of the image.

The README already says "opaque pairing"; the important review point is that
this prevents the analytic Jacobian layer from being more than a placeholder.

### 8. `StatementBank` still has a separate placeholder holomorphic-form story

The production Queue C files define
`HolomorphicForms.HolomorphicOneForm E X` as a `ContMDiffSection` of the
cotangent bundle. But `Jacobian/WorkPackets/StatementBank.lean` still has its
own placeholder:

```lean
abbrev HolomorphicOneForm ... : Type := Complex
```

That means downstream statement-bank goals about genus, periods, Abel-Jacobi,
and trace/degree are not yet exercising the real `HolomorphicForms.Defs` API.
This is acceptable for work packets, but it should be called out in progress
tracking. Otherwise the README can make Queue C/D/E look more connected to the
real definitions than they are.

### 9. Reconnaissance files are correctly not re-exported, but they remain
non-submission files

`Jacobian/ComplexTorus.lean`, `Jacobian/HolomorphicForms.lean`, and
`Jacobian/Periods.lean` now explicitly exclude recon modules from public API.
That is a good cleanup.

For a cleaner rough draft, those files should still be moved out of the Lean
source tree or kept only as project notes. `ManifoldRecon.lean` and
`ZLatticeRecon.lean` contain `sorry`s; even if they are not imported by the
umbrella, they are not production files.

## README Status Review

The following README lines are accurate as project-local build milestones:

- `Complex torus quotient`: mostly yes, assuming "quotient" means the local
  `FullComplexLattice` wrapper and basic quotient API.
- `Quotient charted-space/manifold`: yes for the local construction.
- `Projection (mk) smoothness`: yes as a theorem over the local charted-space
  instance.
- `LieAddGroup smoothness`: yes as a registered local instance, assuming the
  imported files build.

Recommended wording change: avoid presenting these as mathlib-ready completion.
Something like this would be more precise:

```text
Complex torus local quotient API      100%  project-local FullComplexLattice API
Local quotient manifold structure     100%  ChartedSpace + IsManifold, not mathlib-polished
Projection (mk) smoothness            100%  contMDiff_mk over local charts
Local LieAddGroup instance            100%  +, -, LieAddGroup instance wired
```

For the lower layers, the current percentages are generous but not misleading
if they are understood as scaffolding:

- `Holomorphic forms 30%`: reasonable for type/API only.
- `Path integration/periods 30%`: should probably say "chart/local scaffolding;
  global integration opaque" because `chartedForm` is not yet the correct
  pullback.
- `Analytic Jacobian 10%`: accurate; it is currently an abstract quotient
  group, not a compact complex torus.
- `Abel-Jacobi API 5%`: accurate; currently recon only.

## Suggested Next Steps For The Rough Draft

1. Split reusable torus code away from `Jacobian.Challenge`.
2. Decide whether the mathlib-facing abstraction is `ZLattice`, a generic
   closed discrete cocompact subgroup, or a new `ComplexTorus` namespace.
3. Generalize or delete local wrappers around existing `QuotientAddGroup`
   lemmas.
4. Repackage local charts as a direct partial-homeomorphism construction with
   named API lemmas instead of relying on `rfl` through `chartAt`.
5. Audit every global instance for assumptions, diamonds, and typeclass-search
   cost.
6. Replace `chartedForm` with a genuine chart pullback using the tangent map of
   `c.symm`.
7. Connect `StatementBank` Queue C/D/E to the production
   `HolomorphicForms.Defs` and `Periods` APIs, or label those queues as
   independent placeholders.
8. Keep recon files out of public imports and consider moving them to prose
   notes once their findings have been absorbed.

## Bottom Line

The torus layer is a credible project-local milestone now. I would accept the
README's new 100% claims as "this local layer has landed and builds." I would
not treat them as meaning the surrounding Jacobian construction is already
mathematically mature. The highest-priority technical fix is not in the Lie
group packaging; it is the period/chart integration layer, where the current
chart-local form is missing the derivative part of the pullback.
