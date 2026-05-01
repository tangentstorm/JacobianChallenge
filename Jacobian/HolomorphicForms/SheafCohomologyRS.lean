import Mathlib.Topology.Sheaves.Sheaf
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic

/-!
# Sheaf cohomology on a Riemann surface (project API layer)

Project-side wrappers around Mathlib's topological-sheaf and Ext-based
sheaf-cohomology infrastructure, scoped to abelian sheaves on a
topological space `X`. This file is the leaf bank for
`def:sheaf-cohomology-rs` in
`tex/sections/02-holomorphic-forms-and-genus.tex`.

## What lives here (this round)

* `RSAbSheaf X` (leaf 1, TRIVIAL) — alias for `TopCat.Sheaf AddCommGrpCat (TopCat.of X)`,
  i.e. abelian-group-valued sheaves on the topology of `X`.
* `RSSheafCohomology X F q` (leaf 2, SHORT) — alias for Mathlib's
  `CategoryTheory.Sheaf.H F q` (Ext-defined sheaf cohomology). Carries
  the `[HasSheafify]` + `[HasExt]` typeclass dependencies through to
  the call site (Mathlib does not auto-infer them on the
  `Opens.grothendieckTopology X` site for `AddCommGrpCat`; downstream
  consumers must either provide them as `letI`/`haveI` or refine the
  blueprint to a site where they are available).
* `RSLineBundleSheaf X` (leaf 5, TRIVIAL) — placeholder alias for
  `RSAbSheaf X`. A genuine `𝒪_X`-module / locally-free-sheaf API does
  not yet exist in Mathlib v4.28.0 (see plan §2 *ABSENT* rows); the
  alias names the intended slot without committing to coherent
  analytic machinery.
* `RSLineBundleCohomology X L q` (leaf 6, TRIVIAL) — names the
  intended line-bundle cohomology API as the underlying-abelian-sheaf
  cohomology.

## What is intentionally NOT here

* Leaf 3 (`AddCommGroup` instance wrapper) — Mathlib already provides
  `noncomputable instance : AddCommGroup (F.H n)` directly on
  `Sheaf.H`, so the wrapper is redundant. (Recorded for completeness;
  no project work needed.)
* Leaf 4 (Čech cochain complex packaging) — MEDIUM, deferred.
* Leaf 7 (`FiniteDimensionalSheafCohomologyRS` class) — HARD frontier
  class, deferred.
-/

namespace JacobianChallenge.HolomorphicForms

open CategoryTheory

/-- Abelian sheaves on the topology of `X`: a thin alias over
`TopCat.Sheaf AddCommGrpCat (TopCat.of X)`. Plan leaf 1 (TRIVIAL). -/
abbrev RSAbSheaf (X : Type*) [TopologicalSpace X] : Type _ :=
  TopCat.Sheaf AddCommGrpCat (TopCat.of X)

/-- Sheaf cohomology of an abelian sheaf on `X`, as the project alias
for Mathlib's Ext-based `CategoryTheory.Sheaf.H`. Plan leaf 2 (SHORT).

The `[HasSheafify]` and `[HasExt]` hypotheses are required by
Mathlib's underlying `Sheaf.H` definition (see
`Mathlib.CategoryTheory.Sites.SheafCohomology.Basic`); they are not
automatically derivable for the `Opens.grothendieckTopology X` site on
`AddCommGrpCat` in v4.28.0, so they remain as instance arguments at
this layer and propagate to consumers. -/
noncomputable abbrev RSSheafCohomology
    (X : Type*) [TopologicalSpace X]
    [HasSheafify (Opens.grothendieckTopology (TopCat.of X)) AddCommGrpCat.{0}]
    [HasExt.{0} (Sheaf (Opens.grothendieckTopology (TopCat.of X)) AddCommGrpCat.{0})]
    (F : RSAbSheaf X) (q : ℕ) : Type 0 :=
  Sheaf.H F q

/-- Placeholder alias: until coherent analytic `𝒪_X`-module sheaves
exist in Mathlib, the "line bundle sheaf" datum is just an underlying
abelian sheaf on `X`. Plan leaf 5 (TRIVIAL). -/
abbrev RSLineBundleSheaf (X : Type*) [TopologicalSpace X] : Type _ :=
  RSAbSheaf X

/-- Cohomology of a (placeholder) line-bundle sheaf, expressed as the
sheaf cohomology of the underlying abelian sheaf. Plan leaf 6
(TRIVIAL). -/
noncomputable abbrev RSLineBundleCohomology
    (X : Type*) [TopologicalSpace X]
    [HasSheafify (Opens.grothendieckTopology (TopCat.of X)) AddCommGrpCat.{0}]
    [HasExt.{0} (Sheaf (Opens.grothendieckTopology (TopCat.of X)) AddCommGrpCat.{0})]
    (L : RSLineBundleSheaf X) (q : ℕ) : Type 0 :=
  RSSheafCohomology X L q

end JacobianChallenge.HolomorphicForms
