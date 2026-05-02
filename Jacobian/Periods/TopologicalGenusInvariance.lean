/-
Copyright (c) 2026 Jacobian Challenge contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Jacobian.Periods.TopologicalGenus
import Mathlib.Topology.Category.TopCat.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank

/-!
# Homeomorphism invariance of `topologicalGenus`

This file refines the Stage A leaf
`topologicalGenus_homeo_invariant` (declared in
`Jacobian.Periods.SurfaceClassification`) into a single, smaller named
obligation about the first singular homology functor.

## Top-down role

A homeomorphism `M ≃ₜ N` lifts to an isomorphism in `TopCat`, which
the singular-homology functor sends to a ℤ-linear isomorphism of
`singularH1 M` and `singularH1 N`. From a ℤ-linear isomorphism, the
ℤ-rank (`Module.finrank ℤ`) is preserved, so dividing by 2 gives
`topologicalGenus M = topologicalGenus N`.

Only the *finrank* statement carries any nontrivial homological
content; once `singularH1_finrank_homeo_invariant` is in hand,
the umbrella body is a one-line `Nat.div` rewrite.
-/

noncomputable section

namespace JacobianChallenge.Periods

open AlgebraicTopology CategoryTheory

/-- A homeomorphism `M ≃ₜ N` lifts to a ℤ-linear isomorphism of
`singularH1 M ≃ₗ[ℤ] singularH1 N`, by functoriality of
`singularHomologyFunctor (ModuleCat ℤ) 1`. -/
def singularH1LinearEquivOfHomeo
    {M N : Type} [TopologicalSpace M] [TopologicalSpace N]
    (h : M ≃ₜ N) :
    singularH1 M ≃ₗ[ℤ] singularH1 N :=
  (((singularHomologyFunctor (ModuleCat.{0} ℤ) 1).obj
      (ModuleCat.of ℤ ℤ)).mapIso (TopCat.isoOfHomeo h)).toLinearEquiv

/-- **Leaf (homeomorphism invariance of `singularH1` finrank).**
A homeomorphism `M ≃ₜ N` between topological spaces induces equality
of the ℤ-finrank of singular `H₁`.

Body: lift to a ℤ-linear isomorphism via
`singularH1LinearEquivOfHomeo` and apply `LinearEquiv.finrank_eq`. -/
theorem singularH1_finrank_homeo_invariant
    {M N : Type} [TopologicalSpace M] [TopologicalSpace N]
    (h : M ≃ₜ N) :
    Module.finrank ℤ (singularH1 M) = Module.finrank ℤ (singularH1 N) :=
  (singularH1LinearEquivOfHomeo h).finrank_eq

end JacobianChallenge.Periods
