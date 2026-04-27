import Jacobian.HolomorphicForms.AnalyticGenus
import Mathlib.LinearAlgebra.Dual.Basis

/-!
# Basis-aligned dual equivalence

For a complex manifold `X` with `FiniteDimensionalHolomorphicOneForms`,
this file builds the noncomputable linear equivalence between the linear
dual `HolomorphicOneForm E X →ₗ[ℂ] ℂ` and the basis-aligned model space
`Fin (analyticGenus E X) → ℂ`:

```text
holomorphicOneFormDualEquiv :
  (HolomorphicOneForm E X →ₗ[ℂ] ℂ) ≃ₗ[ℂ] (Fin (analyticGenus E X) → ℂ)
```

This is the bridge that lets period-lattice work in
`Jacobian/Periods/PeriodLattice.lean` (basis-aligned model) connect to
the period-pairing image in `Jacobian/Periods/PeriodFunctional.lean`
(linear-dual space). It uses Mathlib's `Module.finBasis` (an arbitrary
basis) and `Module.Basis.dualBasis` to dualize.

The equivalence depends on a choice of basis (it is not canonical — the
underlying basis is `Module.finBasis ℂ (HolomorphicOneForm E X)`, which
is itself an arbitrary choice via `Module.Free.chooseBasis`). For
defining `periodSubgroup` in the basis-aligned model it suffices that
*some* equivalence exists — the resulting subgroup depends on the basis,
but its abstract isomorphism class (and all topological/discreteness
properties) does not.

This file is a Claude-owned design move (commit aa2e593 next-tick plan):
the bottom-up infrastructure that future ticks can use to unfreeze the
`opaque periodSubgroup` in `PeriodLattice.lean`.
-/

namespace JacobianChallenge.HolomorphicForms

open scoped Manifold

variable (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E]
  (X : Type*) [TopologicalSpace X] [ChartedSpace E X]
  [IsManifold (modelWithCornersSelf ℂ E) (⊤ : WithTop ℕ∞) X]
  [FiniteDimensionalHolomorphicOneForms E X]

/-- An arbitrary `Fin (analyticGenus E X)`-indexed basis of
`HolomorphicOneForm E X`. Comes from `Module.finBasis`, which itself
calls `Module.Free.chooseBasis`. The choice is non-canonical. -/
noncomputable def holomorphicOneFormFinBasis :
    Module.Basis (Fin (analyticGenus E X)) ℂ (HolomorphicOneForm E X) :=
  Module.finBasis ℂ (HolomorphicOneForm E X)

/-- The dual basis of `holomorphicOneFormFinBasis`: an arbitrary
`Fin (analyticGenus E X)`-indexed basis of the linear dual
`HolomorphicOneForm E X →ₗ[ℂ] ℂ`. -/
noncomputable def holomorphicOneFormDualFinBasis :
    Module.Basis (Fin (analyticGenus E X)) ℂ
      (HolomorphicOneForm E X →ₗ[ℂ] ℂ) :=
  (holomorphicOneFormFinBasis E X).dualBasis

/-- The basis-aligned dual equivalence: a noncomputable `LinearEquiv`
between the linear dual of holomorphic 1-forms and the basis-aligned
model space. Uses the dual basis of an arbitrary chosen basis. -/
noncomputable def holomorphicOneFormDualEquiv :
    (HolomorphicOneForm E X →ₗ[ℂ] ℂ) ≃ₗ[ℂ]
      (Fin (analyticGenus E X) → ℂ) :=
  (holomorphicOneFormDualFinBasis E X).equivFun

/-- Pointwise reformulation: applying the equivalence to a dual basis
vector gives the standard basis vector at the same index. -/
theorem holomorphicOneFormDualEquiv_dualBasis_apply
    (i : Fin (analyticGenus E X)) :
    holomorphicOneFormDualEquiv E X
        (holomorphicOneFormDualFinBasis E X i) =
      Pi.single i 1 := by
  ext j
  rw [holomorphicOneFormDualEquiv, Module.Basis.equivFun_self,
      Pi.single_apply]
  by_cases h : i = j
  · subst h; simp
  · rw [if_neg h, if_neg (fun heq : j = i => h heq.symm)]

end JacobianChallenge.HolomorphicForms
