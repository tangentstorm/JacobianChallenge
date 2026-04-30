import Jacobian.Blueprint.Sec02.CotangentFiberNorm
import Jacobian.HolomorphicForms.Defs

/-! # Blueprint stub: `def:holomorphic-sup-norm`

Section 2 of `tex/sections/02-holomorphic-forms-and-genus.tex`.

Sup norm on the space of global holomorphic 1-forms `H⁰(X, Ω¹)`,
defined as
`‖ω‖ = sup_{x ∈ X} cotangentFiberNorm X x (ω x)`.

`X` is required to be compact so the supremum is finite. -/

namespace JacobianChallenge.Blueprint

open scoped Manifold
open JacobianChallenge.HolomorphicForms

/-- The sup norm on `H⁰(X, Ω¹)` for a compact complex 1-manifold `X`.
Stub: the value is the supremum over `x : X` of
`cotangentFiberNorm X x (ω.1 x)`. -/
noncomputable def holomorphicSupNorm
    (X : Type*) [TopologicalSpace X] [CompactSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (_ω : HolomorphicOneForm ℂ X) : ℝ := sorry

end JacobianChallenge.Blueprint
