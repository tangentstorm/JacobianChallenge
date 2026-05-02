import Jacobian.Blueprint.Sec01.VanishingOrder
import Mathlib.Topology.Compactification.OnePoint.Basic

/-! Blueprint: `def:meromorphic-function` in
`tex/sections/01-compact-riemann-surfaces.tex`.

The set `Mer(X)` of meromorphic functions on a compact Riemann surface,
viewed as the field of meromorphic germ sections. -/

namespace JacobianChallenge.Blueprint

open scoped Manifold

/-- The type of meromorphic functions on a compact Riemann surface `X`.

A bundled structure carrying:
* `toFun : X → OnePoint ℂ` — the underlying set function (sending poles
  to `∞`).
* `isMeromorphic` — for every point `p ∈ X`, the chart-pulled-back
  ℂ-projection `(fun q => (toFun q).getD 0)` is meromorphic at `p` in
  the manifold sense (i.e. its pullback through the canonical extended
  chart at `p` is `MeromorphicAt` in the usual `ℂ → ℂ` sense — see
  `JacobianChallenge.HolomorphicForms.VanishingOrder.MeromorphicAtX`).

The pullback `(fun q => (toFun q).getD 0)` agrees with `f` on every
chart-neighbourhood of a non-pole, and at a pole takes the sentinel
value `0` at the pole point itself but tends to `∞` in modulus on a
punctured neighbourhood; `meromorphicOrderAt` ignores the value at the
distinguished point, so this still records the right Laurent order
(positive at zeros, negative at poles).

A `CoeFun` lets us continue to write `f x` for the underlying function
application; this preserves the surface API of the previous placeholder
(`MeromorphicFunctionType X := X → OnePoint ℂ`). -/
structure MeromorphicFunctionType (X : Type*) [TopologicalSpace X]
    [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X] where
  /-- Underlying set function from `X` to the Riemann sphere
  `OnePoint ℂ`. -/
  toFun : X → OnePoint ℂ
  /-- The lift `X → OnePoint ℂ` is continuous: poles map to `∞`, and
  in the disk model of a chart, `toFun` tends to `∞` near each pole. -/
  toFun_continuous : Continuous toFun
  /-- The ℂ-projection of `toFun` is meromorphic at every point of `X`,
  in the manifold sense (chart-pulled-back). -/
  isMeromorphic :
    ∀ p, JacobianChallenge.HolomorphicForms.VanishingOrder.MeromorphicAtX
           (fun q => (toFun q).getD 0) p

namespace MeromorphicFunctionType

/-- Apply a `MeromorphicFunctionType` as a function `X → OnePoint ℂ`. -/
instance instCoeFun (X : Type*) [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X] :
    CoeFun (MeromorphicFunctionType X) (fun _ => X → OnePoint ℂ) :=
  ⟨MeromorphicFunctionType.toFun⟩

end MeromorphicFunctionType

end JacobianChallenge.Blueprint
