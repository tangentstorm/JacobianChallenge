import Jacobian.HolomorphicForms.Defs
import Mathlib.Geometry.Manifold.MFDeriv.Basic

namespace JacobianChallenge.Periods

open JacobianChallenge.HolomorphicForms

/--
The genuine chart pullback of a holomorphic 1-form: at `e : E`,
the value is `ω` at the manifold point `c.symm e` precomposed with the
manifold derivative of `c.symm` at `e`. The fiber types collapse:
`TangentSpace 𝓘(ℂ, E) e = E` and `TangentSpace 𝓘(ℂ, E) (c.symm e) = E`
because Mathlib's tangent-space trivialization picks the model fiber
at every point.
-/
noncomputable def chartedFormPullback
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {X : Type*} [TopologicalSpace X] [ChartedSpace E X]
    [IsManifold (modelWithCornersSelf ℂ E) (⊤ : WithTop ℕ∞) X]
    (c : OpenPartialHomeomorph X E)
    (ω : HolomorphicOneForm E X) :
    E → E →L[ℂ] ℂ :=
  fun e =>
    (ω.toFun (c.symm e)).comp
      (mfderiv (modelWithCornersSelf ℂ E)
               (modelWithCornersSelf ℂ E) c.symm e)

end JacobianChallenge.Periods
