# Code Review: `Jacobian/ComplexTorus`

Review scope: read-only review of the current Lean files under
`Jacobian/ComplexTorus`, with mathlib submission as the eventual target. I did
not run or verify the code.

## High-Level Assessment

The directory contains useful quotient-group and quotient-topology facts, but
it is still shaped like a work-packet staging area rather than mathlib-ready
code. The strongest material is the small additive quotient API around `mk`,
`map`, compactness from a compact fundamental domain, and the `ZLattice`
packaging helper. The weakest material is the public import of reconnaissance
files, unresolved `sorry`s, project-local wrapper lemmas around existing
Mathlib declarations, and assumptions that are too specialized to complex
tori when the statements are really about generic additive quotient groups.

For mathlib, I would not try to submit this directory as-is. I would first
separate the generic quotient lemmas from the complex-torus specialization,
delete or move reconnaissance files out of the public API, and rebuild the
main torus definition around existing `ZLattice`/`Submodule ℤ` infrastructure
where possible.

## Blocking Issues

### 1. Public import path includes reconnaissance files and `sorry`s

`Jacobian/ComplexTorus.lean` imports both `ZLatticeRecon` and `ManifoldRecon`
at lines 30-31, and imports `DiscretenessRecon` at line 35. `ManifoldRecon`
then defines `quotientChartedSpace` and `quotientIsManifold` with `sorry`s at
`ManifoldRecon.lean:114-115` and `ManifoldRecon.lean:179-182`.

That is fine for internal exploration, but it is a non-starter for mathlib.
Reconnaissance notes should be moved to prose documentation or issue-tracking
material, not re-exported by the main Lean module. The top-level module should
only import declarations intended as stable API.

Suggested split:

- `ComplexTorus/Basic.lean` and a small number of cohesive API files for
  proved declarations.
- `ComplexTorus/Manifold.lean` only once the charted-space construction is
  actually implemented.
- A non-imported `notes/` or `feedback/` Markdown file for reconnaissance.

### 2. `ManifoldRecon` contradicts the discreteness analysis

`DiscretenessRecon.lean:13-32` correctly documents that closed+cocompact
additive subgroups of finite-dimensional real normed spaces need not be
discrete. However, `ManifoldRecon.lean:155-170` still says step (a) is to show
`Λ.subgroup` is discrete from `Λ.isClosed + FiniteDimensional`, and lists that
as missing Mathlib.

This is not just a wording issue: it points the chart construction at a false
lemma. The construction should instead use the existing `FullComplexLattice`
field `isDiscrete` from `StatementBank.lean:136-148`, or move to a
`ZLattice`-based definition where discreteness is an explicit class parameter.

Concrete fix: rewrite the construction outline in `ManifoldRecon` to start
from `[DiscreteTopology Λ.subgroup]`, and delete the claim that closedness plus
finite dimensionality suffices.

### 3. The second-countability instance appears too strong

`FirstCountable.lean:24-27` declares

```lean
instance secondCountableTopology_quotient :
    SecondCountableTopology (quotient V Λ) :=
  inferInstance
```

under only `[NormedAddCommGroup V] [NormedSpace ℂ V]`.

By inspection, this is mathematically too strong: an arbitrary normed complex
vector space need not be second countable. For the intended complex torus, you
probably want `[FiniteDimensional ℂ V]`, or more generally
`[SecondCountableTopology V]`, and then use the quotient/open-map machinery.

The docstring at `FirstCountable.lean:9-11` says the quotient of a
second-countable additive topological group is second countable; the code does
not assume the premise.

### 4. The project-local `FullComplexLattice` shape is unlikely to be the
right mathlib abstraction

`FullComplexLattice` in `StatementBank.lean:136-146` stores:

- an `AddSubgroup V`,
- closedness,
- discreteness,
- a compact fundamental domain,
- a covering property.

This is useful for staging, but mathlib already has substantial `ZLattice`
API. A mathlib submission should probably not introduce a parallel notion of
full lattice unless there is a strong reason. The bridge in
`ZLatticeRecon.lean:81-106` is evidence that the target abstraction should be
closer to `Submodule ℤ V` plus `[IsZLattice ℝ L]`, with `L.toAddSubgroup` used
for the additive quotient.

At minimum, the public torus API should be parameterized over the existing
Mathlib lattice notion and only expose `FullComplexLattice` as a project-local
adapter, not as the central mathlib concept.

### 5. `StatementBank` is still acting as an implementation dependency

`StatementBank.lean:4-12` says it is not part of the challenge target and is a
bank of statements intended to be split into Aristotle-sized work packets.
That means the dependency direction should be:

- unfinished queue statements live in `StatementBank`;
- completed work moves into the relevant implementation directory;
- `StatementBank` may import completed files to state later work items;
- stable implementation files should not import `StatementBank`.

The current `ComplexTorus` files still import `Jacobian.WorkPackets.StatementBank`
for core declarations such as `FullComplexLattice`, `quotient`, `mk`, and
`map`. That is backwards if the lower complex-torus layer is considered done.
Those core declarations should graduate into something like
`Jacobian/ComplexTorus/Defs.lean` or `Jacobian/ComplexTorus/Basic.lean`, and the
work-packet bank should either remove the completed declarations or reduce them
to comments / remaining target statements.

Concretely, `StatementBank.lean:136-203` still owns the central complex-torus
definition and quotient map API. If Phase 1 lower-layer work is done, that
block should move under `Jacobian/ComplexTorus/`. The bank should keep only the
not-yet-done targets, e.g. charted-space/manifold/Lie-group statements.

## API And Generality Issues

### 6. Many lemmas are specialized to complex normed spaces without using that
structure

Examples:

- `Basic.lean:20-30` (`mk_continuous`, `mk_isOpenQuotientMap`,
  `mk_isOpenMap`) are generic additive topological quotient facts.
- `Mk.lean`, `MkBundled.lean`, `MkHomKer.lean`, `MkRange.lean`,
  `MapMk.lean`, `MapNegSub.lean`, `MapInjective.lean`, and `Surjective.lean`
  are algebraic quotient facts and mostly do not need normed spaces or complex
  scalar multiplication.
- `Compact.lean:24-37` needs a topological additive group, compactness of
  `K`, and continuity of the quotient projection. It does not need
  `NormedSpace ℂ V`.

Mathlib reviewers will usually prefer the most general natural statement. The
complex-torus wrappers can exist downstream, but the contribution-worthy
lemmas should live closer to `QuotientAddGroup` and use `AddSubgroup G` rather
than `FullComplexLattice V`.

### 7. Wrapper lemmas duplicate existing Mathlib names

Several declarations are just local aliases for existing facts:

- `mk_continuous` wraps `QuotientAddGroup.continuous_mk`.
- `mk_isOpenQuotientMap` wraps `QuotientAddGroup.isOpenQuotientMap_mk`.
- `mk_image_isOpen` wraps `QuotientAddGroup.isOpenMap_coe`.
- `mkHom` wraps `QuotientAddGroup.mk'`.
- `continuous_add` and `continuous_neg` wrap global continuity instances.

That is acceptable in a project namespace for readability, but it is not a
good mathlib contribution strategy. For mathlib, either use the existing names
directly or contribute genuinely missing generic lemmas with names that fit the
existing namespace.

## Mathematical And Design Notes

### 8. Small files are fine during the work-queue phase

The current one-lemma-or-small-cluster-per-file layout is consistent with
`ref/plan.md`'s Aristotle workflow: many small jobs with disjoint write scopes are
easier to submit, review, and integrate. I would keep that structure while the
work is still being formalized.

The eventual mathlib cleanup can be a final packaging step. The more urgent
issue is not file granularity; it is making sure completed files no longer
depend on `StatementBank`.

### 9. The local section API is too weak for charts

`LocalSection.lean:31-45` defines a global function
`localSection : quotient V Λ → V` by `Function.invFunOn`. The two lemmas prove
the expected right-inverse and membership properties on the image, but this is
not yet the right abstraction for an `OpenPartialHomeomorph`.

For charts, the useful object is a partial inverse on a specified open source
`mk '' Metric.ball v r`, with:

- an `InjOn` hypothesis on the ball,
- `left_inv`/`right_inv` on the source and target,
- continuity of both directions on the relevant sets,
- open source and target.

The current global `invFunOn` definition hides the domain condition and gives
arbitrary values outside the image. That makes later chart proofs noisier and
less canonical. Consider building a `PartialEquiv` or
`OpenPartialHomeomorph` directly from the small-ball injectivity package.

### 10. Compactness is proved twice

The plan says compactness has been moved toward `Compact.lean`, but this is
exactly the kind of declaration that should not remain duplicated in
`StatementBank`. `Compact.lean:24-37` proves the reusable lemma
`compactSpace_quotient_of_cover`; any instance should call that lemma from the
implementation side, not keep a separate proof in the bank.

The duplicated proof logic should be collapsed. The instance should call the
lemma, or the lemma should be the only exported statement and instances should
be introduced only when they are not likely to cause typeclass search
surprises.

### 11. Global instances deserve scrutiny

The code declares quotient instances for compactness, connectedness,
path-connectedness, first-countability, second-countability, and T2. Some of
these are harmless, but global instances in mathlib need a higher bar:

- Are the assumptions minimal and visible to typeclass search?
- Will the instance create diamonds with existing quotient instances?
- Is it better as a lemma than as an instance?

`CompactSpace (quotient V Λ)` is especially worth thinking about. Compactness
depends on the selected lattice data and fundamental-domain witness, not just
on a generic quotient construction.

### 12. Naming should follow existing namespace conventions

Names like `mk_continuous`, `mk_image_isOpen`, and
`compactSpace_quotient_of_cover` are understandable locally, but mathlib tends
to group names by namespace and object:

- `QuotientAddGroup.continuous_mk`
- `QuotientAddGroup.isCompact_image_mk`
- `AddSubgroup.compactSpace_quotient_of_cocompact`

Before a mathlib PR, choose whether the target namespace is
`QuotientAddGroup`, `AddSubgroup`, `Submodule`, `ZLattice`, or a new
`ComplexTorus` namespace, and name the lemmas accordingly.

### 13. Several proofs rely on brittle definitional equalities

Many proofs are intentionally short and use `rfl` or direct rewriting through
the project-local abbreviations. That is fine for staging, but mathlib code is
easier to maintain when key coercions and quotient maps are made explicit at
API boundaries.

Examples include `mk_add`, `mk_neg`, `map_mk`, and the `mapClm` functoriality
lemmas. I would keep the `simp` lemmas, but ensure the statements are phrased
against Mathlib's canonical quotient maps so they remain stable if local
abbreviations change.

## Positive Notes

- `DiscretenessRecon.lean` identifies an important mathematical trap: closed
  plus cocompact does not imply discreteness. That is exactly the kind of issue
  worth catching before chart construction.
- `MkInjOnSmallBall.lean` has the right shape: it takes the isolation property
  explicitly, so it is independent of how discreteness is obtained.
- `ZLatticeFundDom.lean` is the most plausible mathlib-facing contribution in
  the directory. The lemma packages existing `ZLattice` fundamental-domain API
  into a form useful for additive quotients.
- The additive map API (`map_surjective`,
  `map_injective_of_preimage_subset`, `mapClm_surjective`, and
  `mapClm_injective_of_preimage_subset`) is a useful layer once generalized.

## Suggested Submission Path

1. Move completed complex-torus declarations out of `StatementBank` and into
   `Jacobian/ComplexTorus/`, then make `StatementBank` depend on the completed
   API rather than the other way around.
2. Move `ManifoldRecon`, `DiscretenessRecon`, and other reconnaissance content
   out of the re-exported Lean API.
3. Generalize the quotient lemmas away from `FullComplexLattice` where the
   complex/normed assumptions are unused.
4. Decide whether the real mathlib object is a new `ComplexTorus` definition
   or a theorem family about quotients by `ZLattice`s.
5. Fix the second-countability assumptions.
6. Replace the local-section global function with a partial equivalence or
   open partial homeomorphism construction.
7. Only then attempt the charted-space/manifold layer; it should consume the
   explicit discreteness field or `ZLattice` discreteness, not try to derive
   discreteness from closedness.
