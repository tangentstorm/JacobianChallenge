import Jacobian.Periods.ChartLiftTrans

/-!
# Pointwise apply form of `chartLift_trans`

Pointwise restatement of `chartLift_trans` as a function-application
equality. Useful in proofs that need to reason about the value at a
specific `t : unitInterval`.
-/

namespace JacobianChallenge.Periods

open Set
open JacobianChallenge.HolomorphicForms

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {X : Type*} [TopologicalSpace X] [ChartedSpace E X]
  [IsManifold (modelWithCornersSelf ℂ E) (⊤ : WithTop ℕ∞) X]

set_option linter.unusedSectionVars false in
/--
Pointwise apply form: chart lift of a `Path.trans` equals the
concatenation of the two chart lifts, evaluated at `t`.
-/
theorem chartLift_trans_apply
    (c : OpenPartialHomeomorph X E)
    {a b d : X} (γab : Path a b) (γbd : Path b d)
    (h : range (γab.trans γbd) ⊆ c.source)
    (hab : range γab ⊆ c.source) (hbd : range γbd ⊆ c.source)
    (t : unitInterval) :
    chartLift c (γab.trans γbd) h t =
      ((chartLift c γab hab).trans (chartLift c γbd hbd)) t := by
  rw [chartLift_trans c γab γbd h hab hbd]

end JacobianChallenge.Periods
