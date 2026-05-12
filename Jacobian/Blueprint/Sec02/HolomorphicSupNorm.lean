import Jacobian.Blueprint.Sec02.CotangentFiberNorm
import Jacobian.HolomorphicForms.Defs
import Jacobian.Periods.TrivializationContinuousLinearMapAt

/-! # Blueprint stub: `def:holomorphic-sup-norm`

Section 2 of `tex/sections/02-holomorphic-forms-and-genus.tex`.

Sup norm on the space of global holomorphic 1-forms `H⁰(X, Ω¹)`,
defined as
`‖ω‖ = sup_{x ∈ X} cotangentFiberNormAt X x (ω.1 x)`.

`X` is required to be compact so the supremum is finite.

NOTE FOR WORKERS: `HolomorphicOneForm ℂ X` is a PROJECT-SIDE
abbreviation (not a Mathlib type). Find it at
`Jacobian/HolomorphicForms/Defs.lean`; its full path is
`JacobianChallenge.HolomorphicForms.HolomorphicOneForm` and it unfolds
to `Cₛ^(⊤ : WithTop ℕ∞)⟮…; CotangentModelFiber ℂ, CotangentSpace ℂ X⟯`
(an `abbrev` for the analytic-`ContMDiffSection` of the cotangent
bundle). Open `JacobianChallenge.HolomorphicForms` in your file or use
the fully qualified name. The smoothness index `(⊤ : WithTop ℕ∞)` is
analytic regularity (`ω`); see
`Mathlib/Geometry/Manifold/IsManifold/Basic.lean:781` for the meaning.
The fiber-norm helper `cotangentFiberNormAt` lives in
`Jacobian/Blueprint/Sec02/CotangentFiberNorm.lean`. -/

namespace JacobianChallenge.Blueprint

open scoped Manifold
open JacobianChallenge.HolomorphicForms

/-- The sup norm on `H⁰(X, Ω¹)` for a compact complex 1-manifold `X`:
the supremum over `x : X` of `cotangentFiberNormAt X x (ω.1 x)`.

The supremum is realised via `Real.iSup` (= `sSup` of the range with a
`0` fallback for empty/unbounded). When the base is compact and the
fiber-norm composition is continuous, the supremum is attained and
finite; cf.\ `IsCompact.exists_isMaxOn` and the production
`SectionSupNorm.supNorm`. -/
noncomputable def holomorphicSupNorm
    (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [JacobianChallenge.Periods.StableChartAt ℂ X]
    (ω : HolomorphicOneForm ℂ X) : ℝ :=
  ⨆ x : X, cotangentFiberNormAt X x (ω.1 x)

end JacobianChallenge.Blueprint
