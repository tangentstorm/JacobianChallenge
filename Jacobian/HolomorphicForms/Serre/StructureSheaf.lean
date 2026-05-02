import Jacobian.HolomorphicForms.SheafCohomologyRS
import Jacobian.HolomorphicForms.Serre.StructurePresheaf

/-!
# Analytic structure sheaf `𝒪_X` (frontier)

Project-side frontier `def` for the **analytic structure sheaf** `𝒪_X`
of a topological space carrying a complex-manifold (charted-space)
structure. Classically, `𝒪_X(U) = { f : U → ℂ holomorphic }`, with
restriction maps the obvious ones; this is a sheaf of commutative
ℂ-algebras.

## Mathlib v4.28.0 status

Per `ref/plans/sheaf-cohomology-rs.md` §2 inventory the analytic
structure sheaf is **ABSENT**: Mathlib has the algebraic structure
sheaf in `Mathlib.AlgebraicGeometry.StructureSheaf`, but no analytic
counterpart for complex-manifold charted spaces.

## Refinement role

This file is the bottom of the round-1 refinement of
`RSDualizingSheaf`: the cotangent sheaf `Ω¹_X` is built as a
locally-free `𝒪_X`-module, so any analytic realisation of the
dualizing sheaf eventually grounds out in this declaration. The
declaration is exposed under the project's `RSAbSheaf` alias
(abelian-group-valued, structure-sheaf data forgotten); a richer
sheaf-of-rings refinement is downstream future work.

## Sub-leaves

* (Round 6) `RSStructureSheaf` will be refined into a presheaf of
  abelian groups + sheaf-condition + holomorphicity-of-sections data.
-/

namespace JacobianChallenge.HolomorphicForms

open CategoryTheory

/-- **Refined (round 6).** The analytic structure sheaf `𝒪_X` on a
complex-manifold-flavoured topological space `X`, assembled from the
presheaf of holomorphic functions
(`holomorphicFunctionPresheaf`, frontier) and its sheaf-condition
witness (`holomorphicFunctionPresheaf_isSheaf`, frontier). -/
noncomputable def RSStructureSheaf (X : Type*) [TopologicalSpace X] :
    RSAbSheaf X :=
  ⟨holomorphicFunctionPresheaf X, holomorphicFunctionPresheaf_isSheaf X⟩

end JacobianChallenge.HolomorphicForms
