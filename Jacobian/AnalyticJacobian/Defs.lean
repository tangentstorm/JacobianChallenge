import Jacobian.HolomorphicForms.Defs
import Jacobian.Periods.PeriodFunctional
import Jacobian.Periods.TrivializationContinuousLinearMapAt

/-!
# The analytic Jacobian as an abstract group quotient

Queue E foundation. Defines

```text
AnalyticJacobianGroup E X :=
    (HolomorphicOneForm E X →ₗ[ℂ] ℂ) ⧸ periodSubgroup E X
```

This is the **group-theoretic** shape of the analytic Jacobian — the
linear dual of holomorphic 1-forms quotiented by the period subgroup.
`AddCommGroup` structure comes for free from `QuotientAddGroup`.

The full **complex-Lie-group** structure (topology, manifold, compact
torus) requires `periodSubgroup` to be a full complex lattice, which
in turn needs `Module.Finite ℂ (HolomorphicOneForm E X)` plus the
nondegeneracy of the period pairing (Riemann bilinear relations).
Both are deferred.
-/

namespace JacobianChallenge.AnalyticJacobian

open JacobianChallenge.HolomorphicForms JacobianChallenge.Periods

/-- The analytic Jacobian as an additive quotient group.
The full Lie-group structure is layered on top of this base type via
the deferred lattice/full-rank theorems. -/
noncomputable abbrev AnalyticJacobianGroup
    (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E]
    (X : Type) [TopologicalSpace X] [ChartedSpace E X]
    [IsManifold (modelWithCornersSelf ℂ E) (⊤ : WithTop ℕ∞) X]
    [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [JacobianChallenge.Periods.StableChartAt ℂ X] :
    Type _ :=
  (HolomorphicOneForm E X →ₗ[ℂ] ℂ) ⧸ periodSubgroup E X

/-- Sanity check: the additive group structure on `AnalyticJacobianGroup`
comes for free from `QuotientAddGroup`. -/
noncomputable example
    (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E]
    (X : Type) [TopologicalSpace X] [ChartedSpace E X]
    [IsManifold (modelWithCornersSelf ℂ E) (⊤ : WithTop ℕ∞) X]
    [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [JacobianChallenge.Periods.StableChartAt ℂ X] :
    AddCommGroup (AnalyticJacobianGroup E X) :=
  inferInstance

end JacobianChallenge.AnalyticJacobian
