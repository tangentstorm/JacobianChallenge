import Jacobian.TraceDegree.PullbackFun
import Jacobian.TraceDegree.PullbackFunId
import Jacobian.HolomorphicForms.EvalLinearMap

/-!
# Light bridge: pullback through `evalLinearMap`

A handful of small bridge lemmas linking
`TraceDegree.pullbackFormsFun` with
`HolomorphicForms.evalLinearMap` at fixed `x` and `v`.

The full vec-applied identity
`pullbackFormsFun f η x v = evalLinearMap (f x) (mfderiv f x v) η`
is *not* a `rfl`-bridge, because `mfderiv f x v` lives in
`TangentSpace 𝓘 (f x)` rather than `E` and Lean does not unify these
types automatically here. So we settle for the unbundled
factorisation lemma plus consequences via the new `evalLinearMap`
linearity facade.
-/

namespace JacobianChallenge.TraceDegree

open JacobianChallenge.HolomorphicForms

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {X Y : Type*}
  [TopologicalSpace X] [ChartedSpace E X]
  [TopologicalSpace Y] [ChartedSpace E Y]
  [IsManifold (modelWithCornersSelf ℂ E) (⊤ : WithTop ℕ∞) Y]

set_option linter.unusedSectionVars false in
/--
`pullbackFormsFun f η x` factors as `(η.toFun (f x)) ∘ mfderiv f x`.
This is the definition of `pullbackFormsFun`, exposed as a named lemma.
-/
theorem pullbackFormsFun_apply_eq_comp
    (f : X → Y) (η : HolomorphicOneForm E Y) (x : X) :
    pullbackFormsFun f η x =
      (η.toFun (f x)).comp
        (mfderiv (modelWithCornersSelf ℂ E)
                 (modelWithCornersSelf ℂ E) f x) := rfl

set_option linter.unusedSectionVars false in
/-- `pullbackFormsFun id η x = η.toFun x`. -/
theorem pullbackFormsFun_id_apply_eq_toFun
    (η : HolomorphicOneForm E Y) (x : Y) :
    pullbackFormsFun (id : Y → Y) η x = η.toFun x := by
  rw [pullbackFormsFun_id]

set_option linter.unusedSectionVars false in
/-- `pullbackFormsFun id η x v = evalLinearMap x v η`. -/
theorem pullbackFormsFun_id_apply_vec_eq_evalLinearMap
    (η : HolomorphicOneForm E Y) (x : Y) (v : E) :
    pullbackFormsFun (id : Y → Y) η x v = evalLinearMap x v η := by
  rw [pullbackFormsFun_id_apply_eq_toFun]; rfl

set_option linter.unusedSectionVars false in
/--
The pullback `pullbackFormsFun f η x v` is ℂ-linear in `η` —
explicit evalLinearMap-free `_add` form.
-/
theorem pullbackFormsFun_apply_vec_add'
    (f : X → Y) (η ζ : HolomorphicOneForm E Y) (x : X) (v : E) :
    pullbackFormsFun f (η + ζ) x v =
      pullbackFormsFun f η x v + pullbackFormsFun f ζ x v := by
  show ((η + ζ).toFun (f x)).comp
        (mfderiv (modelWithCornersSelf ℂ E)
                 (modelWithCornersSelf ℂ E) f x) v = _
  rw [add_toFun_apply, ContinuousLinearMap.add_comp]; rfl

end JacobianChallenge.TraceDegree
