import Mathlib.Topology.Sheaves.Sheaf
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.Geometry.Manifold.IsManifold.Basic

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

This round adds:
* Leaf 7 (`FiniteDimensionalSheafCohomologyRS`, HARD) as a frontier
  class, since coherent analytic sheaf theory is ABSENT in Mathlib
  v4.28.0 (per the plan's inventory). The class records the two
  finite-dimensionality axioms that classical RR/Serre duality would
  prove; downstream consumers can either supply instances by hand for
  specific sheaves (e.g. constant sheaves on a discrete base) or wait
  for analytic-sheaf machinery to land.
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

open scoped Manifold in
/-- **Frontier class.** Records, as a typeclass boundary, the
finite-dimensionality of `H⁰` and `H¹` of an abelian sheaf on a
compact Riemann surface — the two cohomological degrees that classical
Riemann-Roch / Serre duality cares about.

This is plan leaf 7 (HARD). Mathlib v4.28.0 has neither coherent
analytic 𝒪_X-modules nor the finite-dimensionality theorem for
coherent sheaf cohomology on a compact Riemann surface (both ABSENT
in the plan's inventory), so we cannot prove this as a theorem here.
Exposing it as a class lets downstream consumers state results
parametrically over "F whose cohomology is finite-dimensional" and
discharge the obligation when the analytic-sheaf machinery lands or
for ad-hoc sheaves where a direct argument exists.

The `[Module ℂ (RSSheafCohomology X F q)]` instance arguments are not
auto-derivable from `Sheaf.H`'s `AddCommGroup` alone; consumers
provide them (e.g. via a sheaf-of-ℂ-modules realisation, or a
`letI`-built `Module` instance via Mathlib's
`AddCommGroup.toIntModule` and a `ℂ`-action witness). The class only
asserts the two `FiniteDimensional` properties on top of those data. -/
class FiniteDimensionalSheafCohomologyRS
    (X : Type*) [TopologicalSpace X] [CompactSpace X] [T2Space X]
    [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [HasSheafify (Opens.grothendieckTopology (TopCat.of X)) AddCommGrpCat.{0}]
    [HasExt.{0} (Sheaf (Opens.grothendieckTopology (TopCat.of X)) AddCommGrpCat.{0})]
    (F : RSAbSheaf X)
    [Module ℂ (RSSheafCohomology X F 0)]
    [Module ℂ (RSSheafCohomology X F 1)] : Prop where
  /-- `H⁰(X, F)` is a finite-dimensional ℂ-vector space. -/
  finiteDimensional_H0 : FiniteDimensional ℂ (RSSheafCohomology X F 0)
  /-- `H¹(X, F)` is a finite-dimensional ℂ-vector space. -/
  finiteDimensional_H1 : FiniteDimensional ℂ (RSSheafCohomology X F 1)

end JacobianChallenge.HolomorphicForms
