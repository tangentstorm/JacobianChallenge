import Jacobian.HolomorphicForms.Defs

/-!
# Finite-dimensionality of holomorphic 1-forms

Queue C work-packet target. States the class
`FiniteDimensionalHolomorphicOneForms` over the real
`HolomorphicOneForm` definition (from `Defs.lean`), and exposes the
analytic genus

```text
analyticGenus X = Module.finrank ℂ (HolomorphicOneForm E X)
```

The proof of finite-dimensionality on a compact connected complex
manifold is the single largest analytic ingredient remaining; it is
deferred — this module merely names the goal.
-/

namespace JacobianChallenge.HolomorphicForms

/-- A complex manifold has finite-dimensional space of holomorphic
1-forms. The proof is deferred — for compact connected Riemann
surfaces this is the classical `dim H⁰(X, Ω¹) = g` identity. -/
class FiniteDimensionalHolomorphicOneForms
    (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E]
    (X : Type*) [TopologicalSpace X] [ChartedSpace E X]
    [IsManifold (modelWithCornersSelf ℂ E) (⊤ : WithTop ℕ∞) X] : Prop where
  /-- The space of holomorphic 1-forms is finite-dimensional. -/
  finiteDimensional : Module.Finite ℂ (HolomorphicOneForm E X)

attribute [instance] FiniteDimensionalHolomorphicOneForms.finiteDimensional

/-- Analytic genus: the ℂ-dimension of the space of holomorphic
1-forms on `X`. -/
noncomputable def analyticGenus
    (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E]
    (X : Type*) [TopologicalSpace X] [ChartedSpace E X]
    [IsManifold (modelWithCornersSelf ℂ E) (⊤ : WithTop ℕ∞) X]
    [FiniteDimensionalHolomorphicOneForms E X] : ℕ :=
  Module.finrank ℂ (HolomorphicOneForm E X)

end JacobianChallenge.HolomorphicForms
