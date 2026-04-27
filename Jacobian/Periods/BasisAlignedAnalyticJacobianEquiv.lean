import Jacobian.Periods.BasisAlignedPeriodSubgroup
import Jacobian.AnalyticJacobian.Defs
import Jacobian.AnalyticJacobian.Mk

/-!
# Quotient-level equivalence

Top-level result for the basis-aligned period bridge: the additive
isomorphism between the functional-space `AnalyticJacobianGroup ℂ X`
and the basis-aligned quotient
`(Fin (analyticGenus ℂ X) → ℂ) ⧸ basisAlignedPeriodSubgroupConcrete X`.

Built via `QuotientAddGroup.congr` against the
`holomorphicOneFormDualEquiv` and the AddEquiv on the period subgroups
constructed in `BasisAlignedPeriodSubgroup.lean`.

This is the bridge that lets the basis-aligned-side of the project
borrow the functional-side `AnalyticJacobianGroup` machinery (group
operations, evalJacobianClass, mk-arith etc.) once the universe lift on
`PeriodFunctional`/`IntegralOneCycle` lands. Currently uses the
*concrete* basis-aligned representative — distinct from the opaque
`basisAlignedPeriodSubgroup` in `Jacobian/Periods/PeriodLattice.lean`.
-/

namespace JacobianChallenge.Periods

open JacobianChallenge.HolomorphicForms JacobianChallenge.AnalyticJacobian

variable (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]

/-- The basis-aligned analytic Jacobian (concrete version): the quotient
of the basis-aligned model `Fin (analyticGenus ℂ X) → ℂ` by the
concrete basis-aligned period subgroup. Distinct from the user's
`BasisAnalyticJacobian X` in `AnalyticOfCurveBasis.lean`, which uses
the opaque `basisAlignedPeriodSubgroup` from `PeriodLattice.lean`. -/
abbrev BasisAlignedAnalyticJacobian : Type :=
  (Fin (analyticGenus ℂ X) → ℂ) ⧸ basisAlignedPeriodSubgroupConcrete X

/-- The basis-aligned dual equivalence lifts to an isomorphism between
the functional-space `AnalyticJacobianGroup ℂ X` and the basis-aligned
analytic Jacobian quotient. Built via Mathlib's `QuotientAddGroup.congr`
against the dual equivalence's image-equation on the period subgroup. -/
noncomputable def analyticJacobianBasisAlignedEquiv :
    AnalyticJacobianGroup ℂ X ≃+ BasisAlignedAnalyticJacobian X :=
  QuotientAddGroup.congr (periodSubgroup ℂ X)
    (basisAlignedPeriodSubgroupConcrete X)
    (holomorphicOneFormDualEquiv ℂ X).toAddEquiv rfl

/-- The quotient-level equiv sends the class of a functional to the class
of its image under the basis-aligned dual equivalence. Direct corollary
of `QuotientAddGroup.congr_mk`. -/
@[simp] theorem analyticJacobianBasisAlignedEquiv_mk
    (φ : HolomorphicOneForm ℂ X →ₗ[ℂ] ℂ) :
    analyticJacobianBasisAlignedEquiv X
        (JacobianChallenge.AnalyticJacobian.mk ℂ X φ) =
      QuotientAddGroup.mk (holomorphicOneFormDualEquiv ℂ X φ) :=
  rfl

/-- The inverse equiv sends a basis-aligned class back to the class of
the inverse-equiv-pulled-back functional. -/
theorem analyticJacobianBasisAlignedEquiv_symm_mk
    (v : Fin (analyticGenus ℂ X) → ℂ) :
    (analyticJacobianBasisAlignedEquiv X).symm
        (QuotientAddGroup.mk v) =
      JacobianChallenge.AnalyticJacobian.mk ℂ X
        ((holomorphicOneFormDualEquiv ℂ X).symm v) :=
  rfl

end JacobianChallenge.Periods
