import Jacobian.HolomorphicForms.Defs
import Jacobian.HolomorphicForms.BasisAlignedDualEquiv
import Jacobian.HolomorphicForms.CompactRiemannSurface
import Jacobian.Periods.IntegralOneCycle

/-!
# Period functional (target statement)

Queue D scaffolding. States the period pairing as an opaque
`AddMonoidHom`:

```text
periodPairing : IntegralOneCycle X →+ (HolomorphicOneForm E X →ₗ[ℂ] ℂ)
```

Mathematically: given a 1-cycle `σ : H₁(X, ℤ)` (an integer linear
combination of singular 1-simplices, modulo boundaries) and a
holomorphic 1-form `ω`, the pairing returns `∫_σ ω`. This is the
classical period pairing.

The construction is **deferred**: it requires
- multi-chart path integration (a `γ : Path` may cross chart
  boundaries; we have the single-chart version in
  `Periods/PathIntegralChart.lean`);
- linearity in `σ` (sum of integrals = integral of sum);
- well-definedness modulo boundary, i.e., Stokes for 1-forms on
  manifolds (ABSENT in Mathlib v4.28.0; see Inventory §4.5).

Until those land, this file uses `opaque` to give the type its
public name without committing to an implementation.
-/

namespace JacobianChallenge.Periods

open JacobianChallenge.HolomorphicForms

/-- The period pairing
`IntegralOneCycle X →+ (HolomorphicOneForm E X →ₗ[ℂ] ℂ)`.
Mathematically: integrate the form over the cycle. The
implementation is deferred (multi-chart path integration + Stokes
on manifolds; see file docstring). -/
opaque periodPairing
    (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E]
    (X : Type) [TopologicalSpace X] [ChartedSpace E X]
    [IsManifold (modelWithCornersSelf ℂ E) (⊤ : WithTop ℕ∞) X] :
    IntegralOneCycle X →+ (HolomorphicOneForm E X →ₗ[ℂ] ℂ)

/-- The basis-aligned period subgroup is discrete.

Bottom-up content: integrality of the period pairing image. Equivalently,
the image is a free `ℤ`-module of rank `2g`, spanned by `2g` real-linearly
independent period vectors after transport to the basis-aligned model.

This is the named bottom-up obligation that
`Jacobian.Periods.basisAlignedPeriodSubgroup_isDiscrete` delegates to.
A real proof requires the integrality of `periodPairing` on integral
1-cycles. -/
theorem periodSubgroup_isZLattice
    (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E]
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace E X]
    [IsManifold (modelWithCornersSelf ℂ E) (⊤ : WithTop ℕ∞) X]
    [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X] :
    DiscreteTopology
      (AddSubgroup.map
        (holomorphicOneFormDualEquiv ℂ X).toLinearMap.toAddMonoidHom
        ((periodPairing ℂ X).range)) := sorry

/-- The period subgroup: the image of the period pairing, as an
additive subgroup of the linear dual of holomorphic 1-forms. -/
noncomputable def periodSubgroup
    (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E]
    (X : Type) [TopologicalSpace X] [ChartedSpace E X]
    [IsManifold (modelWithCornersSelf ℂ E) (⊤ : WithTop ℕ∞) X] :
    AddSubgroup (HolomorphicOneForm E X →ₗ[ℂ] ℂ) :=
  (periodPairing E X).range

end JacobianChallenge.Periods
