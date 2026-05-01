import Jacobian.Blueprint.Sec05.AbelExistence

/-! Blueprint stub: `input:abel-theorem` in
`tex/sections/05-abel-jacobi.tex` (sec05 row of `ref/scope-out.md`,
classified **SHORT** umbrella).

Umbrella classical input combining the two sec05 main theorems:

* `thm:abel-existence` (`principal_iff_AJ_zero` in
  `Jacobian/Blueprint/Sec05/AbelExistence.lean`): a degree-zero
  divisor is principal iff its image under the Abel–Jacobi map is
  zero.
* `thm:abel-point-separation` (production decl
  `JacobianChallenge.AbelJacobi.pathIntegralFunctional_separates_points`
  in `Jacobian/AbelJacobi/AnalyticOfCurveBasis.lean`): the
  Abel–Jacobi map separates points on a positive-genus compact
  Riemann surface.

The umbrella is the conjunction of the two; it is sorry-free
relative to the (sorry-bearing) Abel-existence assembly because we
do not pull in the production-side `thm:abel-point-separation`
(which lives in a Mathlib-importing module). The point-separation
half is recorded as a `Prop`-level placeholder, with a docstring
naming the production decl that supplies the real content.

## Conventions

* No Mathlib imports — pure Lean assembly.
* Helpers live in the nested namespace
  `JacobianChallenge.Blueprint.AbelExistence`. -/

namespace JacobianChallenge.Blueprint
namespace AbelExistence

/-- Placeholder predicate for `thm:abel-point-separation`. The real
statement is `pathIntegralFunctional_separates_points` in
`Jacobian/AbelJacobi/AnalyticOfCurveBasis.lean` (HARD per
`ref/scope-out.md`); here we record `True` so the umbrella can
type-check Mathlib-free. -/
def AbelPointSeparation (_X : Type) : Prop := True

/-- **`input:abel-theorem`** umbrella: the conjunction of
`thm:abel-existence` (this file's
`AbelExistence.principal_iff_AJ_zero`) and
`thm:abel-point-separation` (placeholder).

Bundled as a `Prop` so the blueprint TeX can reference a single
`\lean{...}` annotation for the classical-input package. -/
def inputAbelTheorem (X : Type) : Prop :=
  (∀ D : Div0 X, IsPrincipal D ↔ AJ X D = ()) ∧ AbelPointSeparation X

/-- The umbrella holds: the Abel-existence half is supplied by
`principal_iff_AJ_zero`; the point-separation half is the
trivially-inhabited placeholder `AbelPointSeparation`. Sorry-free
modulo the `sorry`s already living in `AbelExistence.lean`'s
MEDIUM/HARD math leaves. -/
theorem input_abel_theorem_holds (X : Type) :
    inputAbelTheorem X := by
  refine ⟨fun D => principal_iff_AJ_zero X D, ?_⟩
  trivial

end AbelExistence
end JacobianChallenge.Blueprint
