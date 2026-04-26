import Jacobian.Periods.PathLift
import Mathlib.Topology.Path

/-!
# Chart lift commutes with path concatenation

`chartLift c (γab.trans γbd) h` is the same path as
`(chartLift c γab _).trans (chartLift c γbd _)`. Helper lemma needed
to lift the conditional in-chart `_trans` linearity to the from-`X`
via-chart layer.

The Mathlib analogue is `Path.map_trans`, which uses the global
`Continuous` form. Here we need the `ContinuousOn`-friendly version
via `Path.map'` (which is what `chartLift` uses).
-/

namespace JacobianChallenge.Periods

open Set
open JacobianChallenge.HolomorphicForms

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {X : Type*} [TopologicalSpace X] [ChartedSpace E X]
  [IsManifold (modelWithCornersSelf ℂ E) (⊤ : WithTop ℕ∞) X]

set_option linter.unusedSectionVars false in
/-- Chart lifting commutes with `Path.trans`: lifting a concatenation
equals concatenating the two lifts. -/
theorem chartLift_trans
    (c : OpenPartialHomeomorph X E)
    {a b d : X} (γab : Path a b) (γbd : Path b d)
    (h : range (γab.trans γbd) ⊆ c.source)
    (hab : range γab ⊆ c.source) (hbd : range γbd ⊆ c.source) :
    chartLift c (γab.trans γbd) h =
      (chartLift c γab hab).trans (chartLift c γbd hbd) := by
  apply Path.ext
  funext t
  show c.toFun ((γab.trans γbd) t) =
       ((chartLift c γab hab).trans (chartLift c γbd hbd)) t
  rw [Path.trans_apply, Path.trans_apply]
  split_ifs with ht
  · rfl
  · rfl

end JacobianChallenge.Periods
