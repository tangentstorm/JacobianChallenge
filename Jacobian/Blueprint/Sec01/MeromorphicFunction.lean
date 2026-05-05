import Jacobian.Blueprint.Sec01.VanishingOrder
import Jacobian.HolomorphicForms.HolomorphicMap
import Jacobian.HolomorphicForms.OnePointCxIsManifold
import Mathlib.Topology.Compactification.OnePoint.Basic

/-! Blueprint: `def:meromorphic-function` in
`tex/sections/01-compact-riemann-surfaces.tex`.

The set `Mer(X)` of meromorphic functions on a compact Riemann surface,
viewed as the field of meromorphic germ sections. -/

namespace JacobianChallenge.Blueprint

open scoped Manifold OnePoint
open scoped Topology
open JacobianChallenge.HolomorphicForms.HolomorphicMap

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
  /-- The associated CP¹-valued map is holomorphic at every point, in
  the project-local chart predicate. -/
  holomorphicAt :
    ∀ p, IsHolomorphicAt toFun p
  /-- At a zero of the finite chart projection, the scalar vanishing
  order agrees with the chart-local analytic order of the CP¹ lift. -/
  finite_order_eq_mapAnalyticOrderAt :
    ∀ p, toFun p = ((0 : ℂ) : OnePoint ℂ) →
      (vanishingOrder X p (fun q => (toFun q).getD 0)).untopD 0 =
        (mapAnalyticOrderAt toFun p : ℤ)
  /-- At a pole, the scalar order is the negative of the chart-local
  analytic order in the infinity chart. -/
  pole_order_eq_neg_mapAnalyticOrderAt :
    ∀ p, toFun p = (∞ : OnePoint ℂ) →
      (vanishingOrder X p (fun q => (toFun q).getD 0)).untopD 0 =
        -(mapAnalyticOrderAt toFun p : ℤ)
  /-- Positive scalar order means the CP¹ value is the finite zero. -/
  value_eq_zero_of_pos_order :
    ∀ p, 0 <
      (vanishingOrder X p (fun q => (toFun q).getD 0)).untopD 0 →
      toFun p = ((0 : ℂ) : OnePoint ℂ)
  /-- Negative scalar order means the CP¹ value is the point at infinity. -/
  value_eq_infty_of_neg_order :
    ∀ p,
      (vanishingOrder X p (fun q => (toFun q).getD 0)).untopD 0 < 0 →
      toFun p = (∞ : OnePoint ℂ)
  /-- Classical local `k`-fold fibre-counting theorem for the associated
  holomorphic map `X → OnePoint ℂ`.

  This is part of the current placeholder API for `def:meromorphic-function`:
  the genuine meromorphic-germ/sheaf construction is still absent, and this
  field records the one-variable local mapping theorem needed downstream by
  the branched-cover route. -/
  local_kfold_ramified :
    ∀ [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
      [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) (OnePoint ℂ)]
      {x : X} {k : ℕ}, 0 < k → mapAnalyticOrderAt toFun x = k →
      ∃ U : Set X, IsOpen U ∧ x ∈ U ∧
      ∃ V : Set (OnePoint ℂ), IsOpen V ∧ toFun x ∈ V ∧
      ∀ y ∈ V, y ≠ toFun x →
      ∃ s : Finset X, s.card = k ∧ ↑s ⊆ U ∧
        (∀ x' ∈ s, toFun x' = y ∧ mapAnalyticOrderAt toFun x' = 1) ∧
        (∀ x' ∈ U, toFun x' = y → x' ∈ s)
  /-- Classical local constancy of the weighted fibre count for the
  associated holomorphic map `X → OnePoint ℂ`.

  As with `local_kfold_ramified`, this field sits at the explicit
  meromorphic-function placeholder boundary until the full Riemann-surface
  meromorphic sheaf API is available. -/
  weightedFiberSum_eventually_eq :
    ∀ [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
      [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) (OnePoint ℂ)]
      [CompactSpace X] [T2Space X] [PreconnectedSpace X] [T2Space (OnePoint ℂ)],
      (¬ ∃ y₀ : OnePoint ℂ, ∀ x, toFun x = y₀) →
      (finite_fiber : ∀ y : OnePoint ℂ, (toFun ⁻¹' {y}).Finite) →
      ∀ y₀ : OnePoint ℂ, ∀ᶠ y in 𝓝 y₀,
        ((finite_fiber y).toFinset).sum (mapAnalyticOrderAt toFun) =
        ((finite_fiber y₀).toFinset).sum (mapAnalyticOrderAt toFun)

namespace MeromorphicFunctionType

/-- Apply a `MeromorphicFunctionType` as a function `X → OnePoint ℂ`. -/
instance instCoeFun (X : Type*) [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X] :
    CoeFun (MeromorphicFunctionType X) (fun _ => X → OnePoint ℂ) :=
  ⟨MeromorphicFunctionType.toFun⟩

end MeromorphicFunctionType

end JacobianChallenge.Blueprint
