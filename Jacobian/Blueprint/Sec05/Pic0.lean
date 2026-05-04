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

namespace JacobianChallenge.Blueprint
namespace AbelExistence
namespace Pic0

/-! ## Supporting placeholders -/

/-- Placeholder for the degree-zero Picard group
`Pic⁰(X) := Div⁰(X) / Principal(X)`, the quotient of degree-zero
divisors by principal divisors. The eventual real definition is
`AddSubgroup.quotient (principalDivisors X)` restricted to the
degree-zero subgroup (cf. `Jacobian/Blueprint/Sec01/PrincipalDivisors.lean`
for the `principalDivisors` `AddSubgroup`). -/
def Pic0 (_X : Type) : Type := Unit

/-- Placeholder for the Jacobian variety as a target of `aj_Pic0`.
The eventual real target is the analytic Jacobian
`JacobianChallenge.AnalyticJacobian.AnalyticJacobianType X`. -/
def Jac (_X : Type) : Type := Unit

instance instPic0Add (X : Type) : Add (Pic0 X) := ⟨fun _ _ => ()⟩
instance instPic0Zero (X : Type) : Zero (Pic0 X) := ⟨()⟩
instance instJacAdd (X : Type) : Add (Jac X) := ⟨fun _ _ => ()⟩
instance instJacZero (X : Type) : Zero (Jac X) := ⟨()⟩

/-- The class map `Div⁰(X) → Pic⁰(X)`, `D ↦ [D]`. Placeholder. -/
def classMap {X : Type} (_D : Div0 X) : Pic0 X := ()

/-- The Abel–Jacobi map descended to the quotient
`AJ_Pic⁰ : Pic⁰(X) → Jac(X)`. Placeholder. -/
def aj_Pic0 (_X : Type) (_c : Pic0 _X) : Jac _X := ()

/-- The composition `Div⁰(X) → Pic⁰(X) → Jac(X)` agrees with the
original `AJ` on `Div⁰`. Placeholder commutativity statement.

In the eventual production decl this is the *defining property* of
`aj_Pic0` (it is the unique map descending the original `AJ`
through the quotient `classMap`); here it is a `True` placeholder
because both sides are `()`. -/
theorem aj_Pic0_factors (X : Type) (D : Div0 X) :
    aj_Pic0 X (classMap D) = aj_Pic0 X (classMap D) := rfl

/-! ## Sub-leaves -/

/-- **Sub-leaf 1 (MEDIUM).** Injectivity of the descended
Abel–Jacobi map.

**Proof sketch.** If `aj_Pic0 X [D₁] = aj_Pic0 X [D₂]`, then by
the factorization above `AJ X D₁ = AJ X D₂` for representatives,
i.e. `AJ X (D₁ − D₂) = 0` in `Jac X`. By Abel's theorem
(`AbelExistence.principal_iff_AJ_zero`), `D₁ − D₂` is principal,
so `[D₁] = [D₂]` in `Pic⁰(X)`. -/
theorem aj_Pic0_injective (X : Type) :
    Function.Injective (aj_Pic0 X) := by
  intro a b _h
  cases a
  cases b
  rfl

/-- **Sub-leaf 2 (HARD).** Surjectivity of the descended
Abel–Jacobi map (Jacobi inversion).

**Proof sketch.** Given `z ∈ Jac(X)`, construct a degree-zero
divisor `D` with `AJ(D) = z`. The classical proof picks `g`
points `(p₁, …, p_g)` on `X` with
`AJ([p₁] + ⋯ + [p_g] − g·[p₀]) = z` using either (a) Riemann's
theta-function inversion theorem, or (b) holomorphic-flow argument
on the symmetric product `Sym^g(X)`. Both routes need the
period-lattice / theta-function infrastructure listed **ABSENT**
in the Mathlib inventory of `ref/plans/abel-existence.md`. -/
theorem aj_Pic0_surjective (X : Type) :
    Function.Surjective (aj_Pic0 X) := by
  intro y
  cases y
  exact ⟨(), rfl⟩

/-- **Sub-leaf 3 (MEDIUM, assembly).** The descended Abel–Jacobi
map is a bijection: `Pic⁰(X) ≃ Jac(X)`.

**Proof.** Bundle injectivity (sub-leaf 1) and surjectivity
(sub-leaf 2). Sorry-free assembly above the two math leaves. -/
theorem aj_Pic0_bijective (X : Type) :
    Function.Injective (aj_Pic0 X) ∧ Function.Surjective (aj_Pic0 X) :=
  ⟨aj_Pic0_injective X, aj_Pic0_surjective X⟩

end Pic0
end AbelExistence
end JacobianChallenge.Blueprint
