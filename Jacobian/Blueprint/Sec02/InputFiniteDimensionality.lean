import Jacobian.Blueprint.Sec02.HoneUnitBallCompact
import Jacobian.Blueprint.Sec02.FdFromRiesz

/-! # Blueprint stub: `input:finite-dimensionality`

Section 2 of `tex/sections/02-holomorphic-forms-and-genus.tex`.

Umbrella combining `thm:hone-unit-ball-compact` with `thm:fd-from-riesz`
to conclude finite-dimensionality of `H⁰(X, Ω¹)`.

The statement is parameterised by an abstract normed-space realisation
`H` of `HolomorphicOneForm ℂ X` whose norm matches
`holomorphicSupNorm`, mirroring the parameterisation of
`hone_unit_ball_compact`. The `H` realisation will be supplied
downstream by the production-side `HolomorphicOneFormBanachData` glue;
the blueprint stays agnostic about how that glue is built. -/

namespace JacobianChallenge.Blueprint

open scoped Manifold
open JacobianChallenge.HolomorphicForms

/-- Umbrella: under any normed-space realisation of `H⁰(X, Ω¹)` whose
norm equals `holomorphicSupNorm`, the realisation is finite-dimensional
over `ℂ`. -/
theorem input_finite_dimensionality
    (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
    (e : HolomorphicOneForm ℂ X ≃ₗ[ℂ] H)
    (_h_norm : ∀ ω : HolomorphicOneForm ℂ X, ‖e ω‖ = holomorphicSupNorm X ω) :
    FiniteDimensional ℂ H := by
  -- DEPENDS ON node 5 (`hone_unit_ball_compact`). Once that landed:
  -- `exact fd_from_riesz one_pos (hone_unit_ball_compact X e _h_norm)`
  sorry

end JacobianChallenge.Blueprint
