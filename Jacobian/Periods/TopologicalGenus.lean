/-
Copyright (c) 2025 Jacobian Challenge contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.AlgebraicTopology.SingularHomology.Basic
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.LinearAlgebra.Dimension.Finrank

/-!
# Topological genus via singular homology

We define the **topological genus** of a compact connected topological space `M`
as half the ℤ-rank of its first singular homology group H₁(M; ℤ).

For a compact connected oriented 2-manifold (surface of genus g), this equals g.
For non-orientable or non-compact spaces the value is mathematically meaningless,
but the definition is still well-typed.

## Main definitions

* `JacobianChallenge.Periods.singularH1` — the first singular homology H₁(M; ℤ)
  as a type carrying `AddCommGroup` and `Module ℤ` instances.
* `JacobianChallenge.Periods.topologicalGenus` — `Module.finrank ℤ H₁(M; ℤ) / 2`.
-/

noncomputable section

namespace JacobianChallenge.Periods

open AlgebraicTopology CategoryTheory

/-- The first singular homology of `M` with ℤ-coefficients, viewed as a ℤ-module.

This extracts the carrier of the `ModuleCat ℤ` object produced by
`singularHomologyFunctor (ModuleCat ℤ) 1` applied to `TopCat.of M`. -/
abbrev singularH1 (M : Type) [TopologicalSpace M] : Type :=
  ((singularHomologyFunctor (ModuleCat.{0} ℤ) 1).obj
    (ModuleCat.of ℤ ℤ)).obj (TopCat.of M)

instance singularH1.addCommGroup (M : Type) [TopologicalSpace M] :
    AddCommGroup (singularH1 M) :=
  ModuleCat.isAddCommGroup _

instance singularH1.module (M : Type) [TopologicalSpace M] :
    Module ℤ (singularH1 M) :=
  ModuleCat.isModule _

/-- Topological genus of a compact connected 2-manifold, defined as
half the ℤ-rank of singular H₁. The definition is `noncomputable`
and is intended for compact connected oriented 2-manifolds; for
non-orientable or non-compact spaces the value is meaningless. -/
noncomputable def topologicalGenus
    (M : Type) [TopologicalSpace M] [CompactSpace M] [ConnectedSpace M] :
    ℕ :=
  Module.finrank ℤ (singularH1 M) / 2

end JacobianChallenge.Periods

end
