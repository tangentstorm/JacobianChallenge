import Jacobian.HolomorphicForms.EvalLinearMap

/-!
# Linear-arithmetic facade simps for `evalLinearMap`

Closes the basic linear-arithmetic API around
`HolomorphicForms.evalLinearMap`. All trivial — they reduce to
`LinearMap.map_*` — but useful as named simp targets so downstream
proofs don't need to peek into the bundled definition.
-/

namespace JacobianChallenge.HolomorphicForms

open scoped Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {X : Type*} [TopologicalSpace X] [ChartedSpace E X]
  [IsManifold (modelWithCornersSelf ℂ E) (⊤ : WithTop ℕ∞) X]

theorem evalLinearMap_neg
    (x : X) (v : E) (η : HolomorphicOneForm E X) :
    evalLinearMap x v (-η) = -evalLinearMap x v η :=
  (evalLinearMap x v).map_neg η

theorem evalLinearMap_sub
    (x : X) (v : E) (η ζ : HolomorphicOneForm E X) :
    evalLinearMap x v (η - ζ) = evalLinearMap x v η - evalLinearMap x v ζ :=
  (evalLinearMap x v).map_sub η ζ

theorem evalLinearMap_smul
    (x : X) (v : E) (k : ℂ) (η : HolomorphicOneForm E X) :
    evalLinearMap x v (k • η) = k • evalLinearMap x v η :=
  (evalLinearMap x v).map_smul k η

theorem evalLinearMap_nsmul
    (x : X) (v : E) (n : ℕ) (η : HolomorphicOneForm E X) :
    evalLinearMap x v (n • η) = n • evalLinearMap x v η := by
  induction n with
  | zero => simp
  | succ n ih => rw [succ_nsmul, succ_nsmul, map_add, ih]

end JacobianChallenge.HolomorphicForms
