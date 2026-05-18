import Jacobian.Periods.BasisAlignedPeriodSubgroup
import Jacobian.Periods.BasisAlignedPeriodPairing
import Jacobian.AnalyticJacobian.Defs
import Jacobian.AnalyticJacobian.Mk
import Jacobian.AnalyticJacobian.MkExt
import Jacobian.AbelJacobi.Defs
import Jacobian.Periods.TrivializationContinuousLinearMapAt

/-!
# Quotient-level equivalence — top of the basis-aligned period bridge

This file packages the additive isomorphism between the functional-space
`AnalyticJacobianGroup ℂ X` and the basis-aligned quotient
`(Fin (analyticGenus ℂ X) → ℂ) ⧸ basisAlignedPeriodSubgroupConcrete X`.

Built via `QuotientAddGroup.congr` against the
`holomorphicOneFormDualEquiv` and the AddEquiv on the period subgroups
constructed in `BasisAlignedPeriodSubgroup.lean`.

This is the top of a four-file basis-aligned period bridge:

```
HolomorphicForms/BasisAlignedDualEquiv      (LinearEquiv on linear duals)
   ↓
Periods/BasisAlignedPeriodSubgroup          (image of periodSubgroup ℂ X)
   ↓                                            +AddEquiv on subgroups
Periods/BasisAlignedPeriodPairing           (cycles → basis-aligned model)
   ↓
Periods/BasisAlignedAnalyticJacobianEquiv   (this file: AddEquiv on quotients)
```

The bridge lets either side of the project borrow the other's machinery.
Functional-space-side has rich AnalyticJacobianGroup machinery (group
operations, evalJacobianClass, witnessAbelJacobi, mk-arith etc.); the
basis-aligned side is what `Jacobian/Solution.lean` and the user's
`Jacobian/AbelJacobi/AnalyticOfCurveBasis.lean` operate on.

Post-keystone-refactor (commit 952e750, 2026-04-27): PeriodLattice's
`basisAlignedPeriodSubgroup` is now `noncomputable def` routing to
`basisAlignedPeriodSubgroupConcrete`, so the user's `BasisAnalyticJacobian X`
and this file's `BasisAlignedAnalyticJacobian X` are definitionally
equal as types, modulo the umbrella unfolding.
-/

namespace JacobianChallenge.Periods

open JacobianChallenge.HolomorphicForms JacobianChallenge.AnalyticJacobian

variable (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
  [JacobianChallenge.Periods.StableChartAt ℂ X]
  [FiniteDimensionalHolomorphicOneForms ℂ X]

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

omit [T2Space X] [CompactSpace X] [ConnectedSpace X] in
/-- The quotient-level equiv sends the class of a functional to the class
of its image under the basis-aligned dual equivalence. Direct corollary
of `QuotientAddGroup.congr_mk`. -/
@[simp] theorem analyticJacobianBasisAlignedEquiv_mk
    (φ : HolomorphicOneForm ℂ X →ₗ[ℂ] ℂ) :
    analyticJacobianBasisAlignedEquiv X
        (JacobianChallenge.AnalyticJacobian.mk ℂ X φ) =
      QuotientAddGroup.mk (holomorphicOneFormDualEquiv ℂ X φ) :=
  rfl

omit [T2Space X] [CompactSpace X] [ConnectedSpace X] in
/-- The inverse equiv sends a basis-aligned class back to the class of
the inverse-equiv-pulled-back functional. -/
theorem analyticJacobianBasisAlignedEquiv_symm_mk
    (v : Fin (analyticGenus ℂ X) → ℂ) :
    (analyticJacobianBasisAlignedEquiv X).symm
        (QuotientAddGroup.mk v) =
      JacobianChallenge.AnalyticJacobian.mk ℂ X
        ((holomorphicOneFormDualEquiv ℂ X).symm v) :=
  rfl

omit [T2Space X] [CompactSpace X] [ConnectedSpace X] in
/-- The basis-aligned image of an `evalJacobianClass` value: applying the
equiv to `evalJacobianClass P v` gives the basis-aligned class of the
corresponding `evalLinearMap`. Combines `evalJacobianClass_def` with
the previous mk-simp lemma. -/
@[simp] theorem analyticJacobianBasisAlignedEquiv_evalJacobianClass
    (P : X) (v : ℂ) :
    analyticJacobianBasisAlignedEquiv X
        (JacobianChallenge.AnalyticJacobian.evalJacobianClass P v) =
      QuotientAddGroup.mk
        (holomorphicOneFormDualEquiv ℂ X
          (JacobianChallenge.HolomorphicForms.evalLinearMap P v)) := by
  rw [JacobianChallenge.AnalyticJacobian.evalJacobianClass_def,
      analyticJacobianBasisAlignedEquiv_mk]

omit [T2Space X] [CompactSpace X] [ConnectedSpace X] in
/-- The basis-aligned image of a `witnessAbelJacobi` value: the equiv
distributes over the underlying subtraction and the `evalJacobianClass`
unfolding. -/
theorem analyticJacobianBasisAlignedEquiv_witnessAbelJacobi
    (basePoint P : X) (v : ℂ) :
    analyticJacobianBasisAlignedEquiv X
        (JacobianChallenge.AbelJacobi.witnessAbelJacobi
          (E := ℂ) (X := X) basePoint P v) =
      QuotientAddGroup.mk
        (holomorphicOneFormDualEquiv ℂ X
          (JacobianChallenge.HolomorphicForms.evalLinearMap P v)) -
      QuotientAddGroup.mk
        (holomorphicOneFormDualEquiv ℂ X
          (JacobianChallenge.HolomorphicForms.evalLinearMap basePoint v)) := by
  unfold JacobianChallenge.AbelJacobi.witnessAbelJacobi
  rw [(analyticJacobianBasisAlignedEquiv X).map_sub,
      analyticJacobianBasisAlignedEquiv_evalJacobianClass,
      analyticJacobianBasisAlignedEquiv_evalJacobianClass]

omit [T2Space X] [CompactSpace X] [ConnectedSpace X] in
/-- The basis-aligned image of a diagonal `witnessAbelJacobi` is `0`:
follows from `witnessAbelJacobi_self` and `map_zero` of the equiv. -/
@[simp] theorem analyticJacobianBasisAlignedEquiv_witnessAbelJacobi_self
    (basePoint : X) (v : ℂ) :
    analyticJacobianBasisAlignedEquiv X
        (JacobianChallenge.AbelJacobi.witnessAbelJacobi
          (E := ℂ) (X := X) basePoint basePoint v) = 0 := by
  rw [JacobianChallenge.AbelJacobi.witnessAbelJacobi_self]
  exact (analyticJacobianBasisAlignedEquiv X).map_zero

omit [T2Space X] [CompactSpace X] [ConnectedSpace X] in
/-- Period pairings are killed by the basis-aligned quotient projection:
`mk (basisAlignedPeriodPairing X σ) = 0` in the basis-aligned analytic
Jacobian quotient, for any cycle `σ`. Follows from
`basisAlignedPeriodPairing_mem` (membership in the period subgroup) plus
`QuotientAddGroup.eq_zero_iff`. -/
@[simp] theorem mk_basisAlignedPeriodPairing_eq_zero
    (σ : IntegralOneCycle X) :
    (QuotientAddGroup.mk (basisAlignedPeriodPairing X σ) :
        BasisAlignedAnalyticJacobian X) = 0 :=
  (QuotientAddGroup.eq_zero_iff _).mpr (basisAlignedPeriodPairing_mem X σ)

omit [T2Space X] [CompactSpace X] [ConnectedSpace X] in
/-- Single-`mk` form of the witnessAbelJacobi-bridge theorem:
distributes the bridge over witness subtraction and combines the two
`mk`-classes via `QuotientAddGroup.mk_sub`. Useful when downstream
proofs want to act on a single representative rather than on a
subtraction of two. -/
theorem analyticJacobianBasisAlignedEquiv_witnessAbelJacobi_mk_sub
    (basePoint P : X) (v : ℂ) :
    analyticJacobianBasisAlignedEquiv X
        (JacobianChallenge.AbelJacobi.witnessAbelJacobi
          (E := ℂ) (X := X) basePoint P v) =
      QuotientAddGroup.mk
        (holomorphicOneFormDualEquiv ℂ X
          (JacobianChallenge.HolomorphicForms.evalLinearMap P v) -
         holomorphicOneFormDualEquiv ℂ X
          (JacobianChallenge.HolomorphicForms.evalLinearMap basePoint v)) := by
  rw [analyticJacobianBasisAlignedEquiv_witnessAbelJacobi,
      ← QuotientAddGroup.mk_sub]

end JacobianChallenge.Periods
