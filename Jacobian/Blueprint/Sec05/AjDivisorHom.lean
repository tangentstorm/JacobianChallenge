import Jacobian.Blueprint.Sec05.AbelExistence

/-! Blueprint stub: `thm:aj-divisor-hom` in
`tex/sections/05-abel-jacobi.tex` (sec05 row of `ref/scope-out.md`,
classified **MEDIUM**).

The Abel–Jacobi map `AJ`, originally defined point-wise, extends by
`ℤ`-linearity to an additive group homomorphism

  `AJ_full : Divisor X →+ Jacobian X`

on the *full* divisor group (not just `Div⁰ X`). The MEDIUM-class
sketch in `ref/scope-out.md` is:

> `AJ` extends to `Divisor X →+ Jacobian X` by `ℤ`-linearity from
> pointwise definition; production-side `Jacobian.ofCurve` already
> separates points.

This file records the concrete Lean shape of that statement. The
two genuine math obligations — preservation of zero and additivity
of `AJ_full` over `Divisor X` — carry `sorry` proofs; the bundled
`AddHom` structure is sorry-free assembly above them.

## Conventions

* No Mathlib imports — pure Lean placeholders so the dep-graph node
  is pickup-able. The `Add` and `Zero` typeclasses used here are in
  core Lean (`Init.Core`), not Mathlib.
* Helpers live in the nested namespace
  `JacobianChallenge.Blueprint.AbelExistence.AjDivisorHom` to avoid
  colliding with the genuine `Divisor` / `Jacobian` decls in
  `Jacobian/Blueprint/Sec01/Divisor.lean`,
  `Jacobian/AnalyticJacobian/`, etc.
* Eventual production target: an `AddMonoidHom (Divisor X) (Jacobian X)`
  built on top of the production `AbelJacobi.analyticOfCurve` and
  the Sec01 `Blueprint.Divisor` finsupp. -/

namespace JacobianChallenge.Blueprint
namespace AbelExistence
namespace AjDivisorHom

/-- Placeholder for the type of *all* divisors on `X` (not just
`Div⁰ X`). The eventual production definition is the free abelian
group on points, i.e. `X →₀ ℤ` (cf.
`Jacobian/Blueprint/Sec01/Divisor.lean` `Blueprint.Divisor`). -/
def Divisor (_X : Type) : Type := Unit

/-- Placeholder for the (analytic) Jacobian of `X`. The eventual
production definition is the complex torus
`JacobianChallenge.AnalyticJacobian.AnalyticJacobianType X`. -/
def Jacobian (_X : Type) : Type := Unit

instance instDivisorAdd (X : Type) : Add (Divisor X) := ⟨fun _ _ => ()⟩
instance instDivisorZero (X : Type) : Zero (Divisor X) := ⟨()⟩
instance instJacobianAdd (X : Type) : Add (Jacobian X) := ⟨fun _ _ => ()⟩
instance instJacobianZero (X : Type) : Zero (Jacobian X) := ⟨()⟩

/-- The full Abel–Jacobi map `AJ_full : Divisor X → Jacobian X`,
extending the pointwise `AJ` of
`Jacobian/Blueprint/Sec05/AbelExistence.lean` to all divisors by
`ℤ`-linearity. Placeholder. -/
def AJ_full {X : Type} (_D : Divisor X) : Jacobian X := ()

/-- **Sub-leaf (MEDIUM, math).** `AJ_full` preserves zero:
`AJ_full (0 : Divisor X) = 0`.

The empty divisor maps to the trivial coset `0 ∈ Jacobian X`
because the integral of any holomorphic 1-form over the empty
1-chain vanishes. -/
theorem AJ_full_map_zero (X : Type) :
    AJ_full (X := X) 0 = 0 := by
  rfl

/-- **Sub-leaf (MEDIUM, math).** `AJ_full` is additive:
`AJ_full (D₁ + D₂) = AJ_full D₁ + AJ_full D₂`.

Additivity follows from `ℤ`-linearity of the integral over a
1-chain: integrating along `c₁ + c₂` is the sum of the integrals
along `c₁` and `c₂`, taken modulo the period lattice (and the mod
respects the sum because `Jacobian X` is the *quotient* of an
abelian group). -/
theorem AJ_full_map_add (X : Type) (D₁ D₂ : Divisor X) :
    AJ_full (D₁ + D₂) = AJ_full D₁ + AJ_full D₂ := by
  rfl

/-- A bundled additive group homomorphism between types carrying
`Zero` and `Add`. Local to this stub file; the eventual production
target is Mathlib's `AddMonoidHom`. -/
structure AddHom (α β : Type) [Zero α] [Zero β] [Add α] [Add β] where
  /-- The underlying function. -/
  toFun : α → β
  /-- Preserves zero. -/
  map_zero' : toFun 0 = 0
  /-- Preserves addition. -/
  map_add' : ∀ a b : α, toFun (a + b) = toFun a + toFun b

/-- **Sub-leaf (MEDIUM, assembly).** `AJ_full` packaged as an
additive group homomorphism `Divisor X →+ Jacobian X`. Sorry-free
once `AJ_full_map_zero` and `AJ_full_map_add` are in. -/
def AJ_addHom (X : Type) : AddHom (Divisor X) (Jacobian X) where
  toFun := AJ_full
  map_zero' := AJ_full_map_zero X
  map_add' := AJ_full_map_add X

end AjDivisorHom
end AbelExistence
end JacobianChallenge.Blueprint
