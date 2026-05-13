import Mathlib.Topology.Sheaves.Sheaf
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import Mathlib.CategoryTheory.Sites.SheafCohomology.Cech
import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.Algebra.Category.Grp.Preadditive
import Mathlib.CategoryTheory.Limits.Lattice
import Jacobian.Periods.TrivializationContinuousLinearMapAt

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

* (was leaf 3) — see `RSSheafCohomologyGroup` below; reinstated as a
  thin project-facing API alias.

This round adds:
* Leaf 3 (`RSSheafCohomologyGroup`, TRIVIAL) — exposes the
  `AddCommGroup (RSSheafCohomology X F q)` instance through a
  named project-facing alias. Mathlib provides the underlying
  instance on `Sheaf.H` directly; the alias just renames it for
  consistency with the rest of this file.
* Leaf 4 (`RSCechComplex`, MEDIUM) — packages
  `CategoryTheory.cechComplexFunctor` for an open cover of `X`
  with values in abelian-group presheaves. Pure aliasing; no
  Čech-derived comparison theorem here.
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

/-- Project-facing alias for the `AddCommGroup` instance on
`RSSheafCohomology X F q`. Plan leaf 3 (TRIVIAL).

Mathlib already provides this instance directly on `Sheaf.H`; the
alias just exposes it under a project-side name for downstream
consumers that want to depend only on this file. -/
noncomputable abbrev RSSheafCohomologyGroup
    (X : Type*) [TopologicalSpace X]
    [HasSheafify (Opens.grothendieckTopology (TopCat.of X)) AddCommGrpCat.{0}]
    [HasExt.{0} (Sheaf (Opens.grothendieckTopology (TopCat.of X)) AddCommGrpCat.{0})]
    (F : RSAbSheaf X) (q : ℕ) : AddCommGroup (RSSheafCohomology X F q) :=
  inferInstance

/-- Čech cochain complex of an abelian-group-valued presheaf along an
open cover. Plan leaf 4 (MEDIUM).

Thin alias around Mathlib's `CategoryTheory.cechComplexFunctor`,
specialised to the topological-presheaf source category
`(Opens (TopCat.of X))ᵒᵖ ⥤ AddCommGrpCat`. The instance arguments
required by `cechComplexFunctor`
(`HasFiniteProducts (Opens (TopCat.of X))`,
`Preadditive AddCommGrpCat`,
`HasProducts AddCommGrpCat`) are all derivable in Mathlib v4.28.0:
`Opens` is a `CompleteLattice` (so has all small limits, hence finite
products), and `AddCommGrpCat` is a Grothendieck-abelian preadditive
category with all small limits.

No Čech-derived comparison theorem (i.e. quasi-iso to derived global
sections, or `H^*(Cech) ≃ H^*` under good cover hypotheses) is
provided here — that is downstream work tracked separately. -/
noncomputable abbrev RSCechComplex
    (X : Type*) [TopologicalSpace X]
    {ι : Type} (U : ι → TopologicalSpace.Opens (TopCat.of X))
    (F : TopCat.Presheaf AddCommGrpCat.{0} (TopCat.of X)) :
    CochainComplex AddCommGrpCat.{0} ℕ :=
  (cechComplexFunctor (A := AddCommGrpCat.{0}) U).obj F

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
    [JacobianChallenge.Periods.StableChartAt ℂ X]
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
