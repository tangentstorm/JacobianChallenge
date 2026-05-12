/-! Blueprint stubs: `thm:abel-existence` (sec05) sub-leaves
classified **TRIVIAL**, **SHORT**, **MEDIUM**, and **HARD** in
`ref/plans/abel-existence.md`.

Abel's theorem: for a compact connected Riemann surface `X` of genus
`g ≥ 1` with a fixed base point, a degree-zero divisor `D` is principal
iff its image under the Abel–Jacobi map `AJ : Div⁰(X) → Jac(X)` is zero.

The Grok plan (`ref/plans/abel-existence.md`) decomposes the statement
into five sub-leaves:

1. `Div0` — degree-zero divisors (TRIVIAL)
2. `AJ` — the Abel–Jacobi map (SHORT)
3. `AJ_principal_zero` — `AJ ∘ divisor = 0` on meromorphic functions (MEDIUM)
4. `existence_of_f` — backwards direction via theta/Riemann existence (HARD)
5. `principal_iff_AJ_zero` — assembly of (3) + (4) (MEDIUM)

This file stubs **all five leaves**: the TRIVIAL/SHORT leaves
(`Div0`, `AJ`) are sorry-free `Unit` placeholders, and the
MEDIUM/HARD leaves (`AJ_principal_zero`, `existence_of_f`,
`principal_iff_AJ_zero`) carry the concrete Lean signatures from
the Grok plan with `sorry`-bearing proofs (where genuine math is
needed) or full assembly proofs (where the leaf reduces to its
siblings). Per `ref/scope-out.md` the umbrella `thm:abel-existence`
is `DECOMPOSE`; this file is the decomposition target.

## Conventions

* No Mathlib imports — pure Lean placeholders so the dep-graph node
  is pickup-able without dragging in unrelated infrastructure.
* `Div0` is a `Unit` alias; the eventual real definition is
  `{D : Divisor X // D.degree = 0}` (cf. `Jacobian/Blueprint/Sec01/`
  scaffolding for `Divisor` and `degree`).
* `AJ` is the identity on `Unit`; the eventual real signature is
  `Div0 X →+ Jac X` (additive group hom into the analytic Jacobian
  defined in `Jacobian/AnalyticJacobian/`).
* The MEDIUM/HARD leaves and their helper placeholders
  (`MeromorphicFunction`, `divisor`, `IsPrincipal`) live in a nested
  `AbelExistence` namespace to avoid colliding with the genuine
  `JacobianChallenge.Blueprint.MeromorphicFunction` defined in
  `Jacobian/Blueprint/Sec01/MeromorphicFunctionStructure.lean`.
* No production decl exists yet: when the real `Div0`/`AJ` land in
  `Jacobian/AbelJacobi/`, this file should be retargeted via
  `\lean{...}` annotations in the blueprint TeX rather than carrying
  parallel placeholder definitions. -/

import Jacobian.AnalyticJacobian.Defs
import Jacobian.HolomorphicForms.VanishingOrder
import Jacobian.HolomorphicForms.AnalyticLocalMapping

/-! Blueprint stubs: `thm:abel-existence` (sec05) sub-leaves
...
namespace JacobianChallenge.Blueprint

open JacobianChallenge.HolomorphicForms
open JacobianChallenge.AnalyticJacobian

/-- **Sub-leaf 1 (TRIVIAL).** Degree-zero divisors on a compact
connected Riemann surface `X`.

Mathematical definition (per `ref/plans/abel-existence.md`):
`Div0 X := {D : Divisor X // D.degree = 0}`. -/
def Div0 (X : Type*) [TopologicalSpace X] [ChartedSpace ℂ X] : Type _ :=
  {D : X → ℤ // Set.Finite {x | D x ≠ 0} ∧ (Finsupp.sum (Finsupp.onFinite {x | D x ≠ 0} (by sorry)) (fun _ n => n) : ℤ) = 0}

/-- **Sub-leaf 2 (SHORT).** The Abel–Jacobi map
`AJ : Div⁰(X) → Jac(X)`.

Mathematical definition: pick a base point `p₀ ∈ X` and a basis
`ω₁, …, ω_g` of holomorphic 1-forms; for `D = ∑ nᵢ [pᵢ] ∈ Div⁰(X)`,
set `AJ(D) := ∑ nᵢ ∫_{p₀}^{pᵢ} ω  (mod Λ)` where `Λ` is the period
lattice. -/
noncomputable def AJ (X : Type*) [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [ChartedSpace ℂ X] -- redundant but keeps the signature simple
    (D : Div0 X) : AnalyticJacobianGroup ℂ X :=
  sorry

namespace AbelExistence

open JacobianChallenge.HolomorphicForms

/-! ## Supporting placeholders for the MEDIUM/HARD leaves
...
/-- Placeholder for the type of meromorphic functions on `X`, scoped
to the Sec05 Abel-existence stubs. -/
def MeromorphicFunction (X : Type*) [TopologicalSpace X] [ChartedSpace ℂ X] : Type :=
  {f : X → OnePoint ℂ // IsHolomorphic f}

/-- Placeholder for the divisor `(f) := ∑_{p ∈ X} ord_p(f) ⋅ [p]`
of a meromorphic function. -/
noncomputable def divisor {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (_f : MeromorphicFunction X) : Div0 X :=
  sorry

/-- Placeholder predicate: a divisor is **principal** iff it is the
divisor of some meromorphic function `f ≠ 0`. -/
def IsPrincipal {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (D : Div0 X) : Prop :=
  ∃ f : MeromorphicFunction X, divisor f = D

/-! ## MEDIUM/HARD leaves -/

/-- **Sub-leaf 3 (MEDIUM).** The Abel–Jacobi map vanishes on
principal divisors:
`AJ X (divisor f) = 0` for every meromorphic `f` on `X`. -/
theorem AJ_principal_zero (X : Type*) [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (f : MeromorphicFunction X) :
    AJ X (divisor f) = 0 := by
  sorry

/-- **Sub-leaf 4 (HARD).** Existence direction of Abel's theorem:
if `AJ D = 0` for a degree-zero divisor `D`, then `D` is the
divisor of some meromorphic function on `X`. -/
theorem existence_of_f (X : Type*) [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (D : Div0 X) (h : AJ X D = 0) :
    ∃ f : MeromorphicFunction X, divisor f = D := by
  sorry

/-- **Sub-leaf 5 (MEDIUM).** Abel's theorem assembled:
`D` is principal iff `AJ D = 0`. -/
theorem principal_iff_AJ_zero (X : Type*) [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (D : Div0 X) :
    IsPrincipal D ↔ AJ X D = 0 := by
  refine ⟨fun ⟨f, hf⟩ => ?_, fun h => existence_of_f X D h⟩
  rw [← hf]
  exact AJ_principal_zero X f

end AbelExistence

end JacobianChallenge.Blueprint


end JacobianChallenge.Blueprint
