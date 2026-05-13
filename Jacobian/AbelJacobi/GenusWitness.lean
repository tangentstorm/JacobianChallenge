import Jacobian.AbelJacobi.Nontrivial
import Jacobian.HolomorphicForms.AnalyticGenusWitness
import Jacobian.Periods.TrivializationContinuousLinearMapAt

/-!
# Unified witness chain: genus + Jacobian non-triviality

Combines `HolomorphicForms.AnalyticGenusWitness` (positive
`analyticGenus` from a non-zero `evalLinearMap` value) with
`AbelJacobi.Nontrivial` (Nontrivial `AnalyticJacobianGroup` from a
non-zero `witnessAbelJacobi`).
-/

namespace JacobianChallenge.AbelJacobi

open JacobianChallenge.HolomorphicForms JacobianChallenge.Periods
open JacobianChallenge.AnalyticJacobian

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {X : Type} [TopologicalSpace X] [ChartedSpace E X]
  [IsManifold (modelWithCornersSelf ℂ E) (⊤ : WithTop ℕ∞) X]
  [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
  [JacobianChallenge.Periods.StableChartAt ℂ X]

/-- A non-zero witness `evalLinearMap basePoint v ≠ evalLinearMap P v`
modulo the period subgroup gives both: positive `analyticGenus` and
non-trivial `AnalyticJacobianGroup`. -/
theorem genus_pos_and_nontrivial_jacobian_of_witness_ne_zero
    [FiniteDimensionalHolomorphicOneForms E X]
    (basePoint P : X) (v : E)
    (h : witnessAbelJacobi (E := E) (X := X) basePoint P v ≠ 0) :
    0 < analyticGenus E X ∧ Nontrivial (AnalyticJacobianGroup E X) := by
  refine ⟨?_, nontrivial_analyticJacobian_of_witness_ne_zero basePoint P v h⟩
  -- A non-zero witness implies the difference of `evalLinearMap` values is
  -- not in the period subgroup, hence at least one of them is non-zero,
  -- giving a positive genus.
  by_contra hgenus
  rw [not_lt, Nat.le_zero] at hgenus
  haveI := analyticGenus_eq_zero_iff_subsingleton.mp hgenus
  -- Subsingleton ⇒ all evalLinearMap values are zero ⇒ all classes are zero.
  apply h
  show evalJacobianClass P v - evalJacobianClass basePoint v = 0
  rw [show evalJacobianClass P v = evalJacobianClass basePoint v from ?_]
  · exact sub_self _
  rw [evalJacobianClass_def, evalJacobianClass_def]
  congr 1
  apply Subsingleton.elim

/-- Same conclusion via a direct `toFun`-witness: a non-zero
`η.toFun x v` for some `(x, v, η)` whose value is not in the period
subgroup. (Genus alone follows from any non-zero form via the
existing `analyticGenus_pos_of_toFun_ne_zero`; this packages it
with the Jacobian-side conclusion at a chosen base point.) -/
theorem genus_pos_of_witness_ne_zero
    [FiniteDimensionalHolomorphicOneForms E X]
    (basePoint P : X) (v : E)
    (h : witnessAbelJacobi (E := E) (X := X) basePoint P v ≠ 0) :
    0 < analyticGenus E X :=
  (genus_pos_and_nontrivial_jacobian_of_witness_ne_zero basePoint P v h).1

/-- The `Nontrivial` conclusion in isolation. -/
theorem nontrivial_jacobian_of_witness_ne_zero
    (basePoint P : X) (v : E)
    (h : witnessAbelJacobi (E := E) (X := X) basePoint P v ≠ 0) :
    Nontrivial (AnalyticJacobianGroup E X) :=
  nontrivial_analyticJacobian_of_witness_ne_zero basePoint P v h

/-- The contrapositive: if the analytic Jacobian is `Subsingleton`,
every witness vanishes. -/
theorem witness_eq_zero_of_subsingleton_jacobian
    [Subsingleton (AnalyticJacobianGroup E X)]
    (basePoint P : X) (v : E) :
    witnessAbelJacobi (E := E) (X := X) basePoint P v = 0 :=
  Subsingleton.elim _ _

end JacobianChallenge.AbelJacobi
