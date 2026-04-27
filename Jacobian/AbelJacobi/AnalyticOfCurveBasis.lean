import Jacobian.Periods.PeriodLattice
import Jacobian.ComplexTorus.Defs
import Jacobian.ComplexTorus.ChartedSpace
import Jacobian.ComplexTorus.IsManifold

/-!
# Analytic Abel-Jacobi map (basis-aligned carrier)

This module provides the Abel-Jacobi map valued in the basis-aligned
analytic carrier, the same carrier used by `Jacobian/Solution.lean` for
`Jacobian X`. The named obligations here are what the top-down
`Solution.ofCurve` family delegates to.

The construction mirrors the witness algebra in
`Jacobian/AbelJacobi/Defs.lean` (`witnessAbelJacobi`), but stays on the
basis-aligned model `Fin (analyticGenus ℂ X) → ℂ` rather than the
algebraic dual `(HolomorphicOneForm ℂ X →ₗ[ℂ] ℂ)`. A future bridge
step can identify the two; until then this carrier is the one Solution
talks about.

Following the project's preference for *small* named obligations:

* `pathIntegralFunctional X P Q` — the path-integral coordinates (data,
  `opaque`);
* `pathIntegralFunctional_self` — base-point integral vanishes;
* `analyticOfCurve P` — the Abel-Jacobi map (assembly, no own sorry);
* `analyticOfCurve_self` — base-point sends to zero (assembly);
* `analyticOfCurve_contMDiff` — holomorphicity (named sorry);
* `analyticOfCurve_injective` — Abel injectivity for positive genus
  (named sorry).
-/

namespace JacobianChallenge.AbelJacobi

open scoped Manifold
open JacobianChallenge.HolomorphicForms JacobianChallenge.Periods
open JacobianChallenge.ComplexTorus

variable (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]

/-- The basis-aligned analytic carrier for the Jacobian: the complex
torus quotient of `Fin (analyticGenus ℂ X) → ℂ` by the period lattice.
This is the type that `Jacobian/Solution.lean` ULifts to produce
`Jacobian X`. -/
abbrev BasisAnalyticJacobian : Type :=
  quotient (Fin (analyticGenus ℂ X) → ℂ) (periodFullComplexLattice X)

/-- The path-integral functional from a base point `P` to an endpoint
`Q`, in basis coordinates (i.e. integrating a chosen ℂ-basis of
holomorphic 1-forms over a chosen path).

Top-down obligation. Bottom-up: requires multi-chart path integration
plus a basis choice. -/
opaque pathIntegralFunctional (P Q : X) : Fin (analyticGenus ℂ X) → ℂ

/-- The base-point self path integral vanishes.

Top-down obligation. Bottom-up: a constant-path integral is zero. -/
lemma pathIntegralFunctional_self (P : X) :
    pathIntegralFunctional X P P = 0 := sorry

/-- The analytic Abel-Jacobi map on the basis-aligned carrier.

Pure assembly: lifts `pathIntegralFunctional` through the period quotient. -/
noncomputable def analyticOfCurve (P : X) : X → BasisAnalyticJacobian X :=
  fun Q => mk (Fin (analyticGenus ℂ X) → ℂ)
    (periodFullComplexLattice X) (pathIntegralFunctional X P Q)

/-- The Abel-Jacobi map sends the base point to zero.

Pure assembly from `pathIntegralFunctional_self`. -/
lemma analyticOfCurve_self (P : X) :
    analyticOfCurve X P P = 0 := by
  unfold analyticOfCurve
  rw [pathIntegralFunctional_self]
  rfl

/-- Holomorphicity of the analytic Abel-Jacobi map.

Top-down obligation. Bottom-up: holomorphicity of path integrals plus
smoothness of the period quotient projection. -/
lemma analyticOfCurve_contMDiff (P : X) :
    ContMDiff 𝓘(ℂ)
      (modelWithCornersSelf ℂ (Fin (analyticGenus ℂ X) → ℂ))
      (⊤ : WithTop ℕ∞) (analyticOfCurve X P) := sorry

/-- Abel injectivity for positive genus.

Top-down obligation. Bottom-up: Abel's theorem — for `0 < g`, the
analytic Abel-Jacobi map separates points. Requires point-separation
by holomorphic 1-forms. -/
lemma analyticOfCurve_injective (P : X) (h : 0 < analyticGenus ℂ X) :
    Function.Injective (analyticOfCurve X P) := sorry

end JacobianChallenge.AbelJacobi
