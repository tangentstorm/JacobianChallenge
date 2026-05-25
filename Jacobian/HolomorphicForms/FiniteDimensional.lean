import Jacobian.HolomorphicForms.Defs

/-!
# Finite-dimensionality of holomorphic 1-forms

```text
analyticGenus X = Module.finrank ℂ (HolomorphicOneForm E X)
```
-/

namespace JacobianChallenge.HolomorphicForms


class FiniteDimensionalHolomorphicOneForms
    (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E]
    (X : Type*) [TopologicalSpace X] [ChartedSpace E X]
    [IsManifold (modelWithCornersSelf ℂ E) (⊤ : WithTop ℕ∞) X] : Prop where
  /-- The space of holomorphic 1-forms is finite-dimensional. -/
  finiteDimensional : Module.Finite ℂ (HolomorphicOneForm E X)

attribute [instance] FiniteDimensionalHolomorphicOneForms.finiteDimensional

/--
Analytic genus: the ℂ-dimension of the space of holomorphic
1-forms on `X`.
-/
noncomputable def analyticGenus
    (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E]
    (X : Type*) [TopologicalSpace X] [ChartedSpace E X]
    [IsManifold (modelWithCornersSelf ℂ E) (⊤ : WithTop ℕ∞) X]
    [FiniteDimensionalHolomorphicOneForms E X] : ℕ :=
  Module.finrank ℂ (HolomorphicOneForm E X)

end JacobianChallenge.HolomorphicForms
