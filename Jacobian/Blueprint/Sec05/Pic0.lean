import Jacobian.Blueprint.Sec05.AbelExistence

/-! Blueprint stub: degree-zero Picard group `Pic⁰(X)` and the
Abel–Jacobi isomorphism `Pic⁰(X) ≃ Jac(X)` (sec05).

This is the natural categorical packaging of the two main sec05
theorems already stubbed in this folder:

* **Abel's theorem** (`AbelExistence.principal_iff_AJ_zero`,
  `Jacobian/Blueprint/Sec05/AbelExistence.lean`) says
  `AJ : Div⁰(X) → Jac(X)` factors through the quotient
  `Pic⁰(X) := Div⁰(X) / Principal(X)` and the induced map is
  injective.
* **Jacobi inversion** (the surjectivity half) says the induced map
  is also surjective. Combining gives the classical isomorphism

    `Pic⁰(X) ≃ Jac(X)`.

This file records the four sub-leaves of that statement:

1. `Pic0` (TRIVIAL placeholder) — the quotient type.
2. `aj_Pic0` (TRIVIAL placeholder) — the induced map.
3. `aj_Pic0_injective` (MEDIUM, `sorry`) — injectivity, follows
   from Abel's theorem ⇐ (`existence_of_f`).
4. `aj_Pic0_surjective` (HARD, `sorry`) — surjectivity, follows
   from Jacobi inversion (which itself depends on theta /
   Riemann-Roch infrastructure listed ABSENT in
   `ref/plans/abel-existence.md`).
5. `aj_Pic0_bijective` (MEDIUM, sorry-free assembly) — bundles
   injectivity and surjectivity using `Function.Injective` and
   `Function.Surjective` from core Lean.

## Conventions

* No Mathlib imports — only the sibling Sec05 stub
  `Jacobian.Blueprint.Sec05.AbelExistence` for `Div0` and
  `IsPrincipal`. `Function.Injective` / `Function.Surjective` /
  `Add` / `Zero` are all in core Lean.
* Helpers nested under
  `JacobianChallenge.Blueprint.AbelExistence.Pic0` to avoid
  colliding with sibling sec05 stub namespaces. -/

import Jacobian.Blueprint.Sec05.AbelExistence
import Jacobian.AnalyticJacobian.Defs

/-! Blueprint stub: degree-zero Picard group `Pic⁰(X)` and the
Abel–Jacobi isomorphism `Pic⁰(X) ≃ Jac(X)`. -/

namespace JacobianChallenge.Blueprint
namespace AbelExistence
namespace Pic0

open JacobianChallenge.HolomorphicForms
open JacobianChallenge.AnalyticJacobian


/-! ## Supporting placeholders -/

/-- The degree-zero Picard group `Pic⁰(X) := Div⁰(X) / Principal(X)`,
the quotient of degree-zero divisors by principal divisors. -/
def Pic0 (X : Type*) [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X] : Type _ :=
  QuotientAddGroup.Quotient (AbelExistence.IsPrincipal (X := X)) -- placeholder for the subgroup

/-- The Jacobian variety as a target of `aj_Pic0`. -/
def Jac (X : Type*) [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X] : Type _ :=
  AnalyticJacobianGroup ℂ X

/-- The class map `Div⁰(X) → Pic⁰(X)`, `D ↦ [D]`. -/
def classMap {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (D : Div0 X) : Pic0 X :=
  QuotientAddGroup.mk D

/-- The Abel–Jacobi map descended to the quotient
`AJ_Pic⁰ : Pic⁰(X) → Jac(X)`. -/
noncomputable def aj_Pic0 (X : Type*) [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X] :
    Pic0 X → Jac X :=
  QuotientAddGroup.lift _ (AJ X) (by
    intro D hD
    exact AbelExistence.AJ_principal_zero X (hD.choose) (by rw [hD.choose_spec]) -- placeholder
  )

/-- The composition `Div⁰(X) → Pic⁰(X) → Jac(X)` agrees with the
...
theorem aj_Pic0_factors (X : Type*) [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (D : Div0 X) :
    aj_Pic0 X (classMap D) = AJ X D := by
  rfl

/-! ## Sub-leaves -/

/-- **Sub-leaf 1 (MEDIUM).** Injectivity of the descended
Abel–Jacobi map. -/
theorem aj_Pic0_injective (X : Type*) [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X] :
    Function.Injective (aj_Pic0 X) := by
  intro a b h
  sorry

/-- **Sub-leaf 2 (HARD).** Surjectivity of the descended
Abel–Jacobi map (Jacobi inversion). -/
theorem aj_Pic0_surjective (X : Type*) [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X] :
    Function.Surjective (aj_Pic0 X) := by
  intro y
  sorry

/-- **Sub-leaf 3 (MEDIUM, assembly).** The descended Abel–Jacobi
map is a bijection: `Pic⁰(X) ≃ Jac(X)`. -/
theorem aj_Pic0_bijective (X : Type*) [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X] :
    Function.Injective (aj_Pic0 X) ∧ Function.Surjective (aj_Pic0 X) :=
  ⟨aj_Pic0_injective X, aj_Pic0_surjective X⟩

end Pic0


end Pic0
end AbelExistence
end JacobianChallenge.Blueprint
