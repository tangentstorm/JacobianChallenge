import Jacobian.Periods.PathIntegralCongr
import Jacobian.Periods.PathPartitionSymm

/-!
# Per-segment symmetry for `pathIntegralViaChartCorrect`

Combines `path_symm_subpath_divFinIcc` and
`pathIntegralViaChartCorrect_symm` to give the segment-level
sign-flip identity used inside the eventual
`pathIntegralViaCoverWith_symm` proof:

```
pathIntegralViaChartCorrect c ω
    (γ.symm.subpath (i/n) ((i+1)/n)) h_symm
  = - pathIntegralViaChartCorrect c ω
        (γ.subpath (σ ((i+1)/n)) (σ (i/n))) h
```

The endpoints on the RHS are kept in `σ` form so the Path types
unify definitionally; downstream callers can use `divFinIcc_symm`
to rewrite to arithmetic form after escaping the Path type.

The proof handles a dependent-type issue: the `h_symm` argument
has type that depends on the path, so we can't directly `rw` on
the path inside `pathIntegralViaChartCorrect c ω <path> h_symm`.
Instead we use `pathIntegralViaChartCorrect_eq_of_path_eq` (a
congruence lemma proved by `subst` + proof irrelevance) to bridge.
-/

namespace JacobianChallenge.Periods

open Set unitInterval JacobianChallenge.HolomorphicForms

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {X : Type*} [TopologicalSpace X] [ChartedSpace E X]
  [IsManifold (modelWithCornersSelf ℂ E) (⊤ : WithTop ℕ∞) X]

/-- Per-segment sign-flip: integrating γ.symm's i-th segment equals
the negative of integrating γ's segment with σ-reflected endpoints. -/
theorem pathIntegralViaChartCorrect_symm_subpath_divFinIcc
    (c : OpenPartialHomeomorph X E) (ω : HolomorphicOneForm E X)
    {a b : X} (γ : Path a b)
    (n : ℕ) (hn : 0 < n) (i : ℕ) (hi : i + 1 ≤ n)
    (h : range (γ.subpath
        (σ (divFinIcc n hn (i + 1) hi))
        (σ (divFinIcc n hn i (Nat.le_of_succ_le hi)))) ⊆ c.source)
    (h_symm : range (γ.symm.subpath
        (divFinIcc n hn i (Nat.le_of_succ_le hi))
        (divFinIcc n hn (i + 1) hi)) ⊆ c.source) :
    pathIntegralViaChartCorrect c ω
        (γ.symm.subpath (divFinIcc n hn i (Nat.le_of_succ_le hi))
                        (divFinIcc n hn (i + 1) hi)) h_symm =
      - pathIntegralViaChartCorrect c ω
          (γ.subpath (σ (divFinIcc n hn (i + 1) hi))
                     (σ (divFinIcc n hn i (Nat.le_of_succ_le hi)))) h := by
  set σpath := γ.subpath (σ (divFinIcc n hn (i + 1) hi))
                          (σ (divFinIcc n hn i (Nat.le_of_succ_le hi)))
  have eq : γ.symm.subpath (divFinIcc n hn i (Nat.le_of_succ_le hi))
                            (divFinIcc n hn (i + 1) hi) = σpath.symm :=
    path_symm_subpath_divFinIcc γ n hn i hi
  -- Transport h_symm along eq to get a range hypothesis for σpath.symm
  have h_symm' : range σpath.symm ⊆ c.source := eq ▸ h_symm
  -- LHS = pathIntegralViaChartCorrect c ω σpath.symm h_symm' by path congruence
  rw [pathIntegralViaChartCorrect_eq_of_path_eq c ω eq h_symm h_symm']
  exact pathIntegralViaChartCorrect_symm c ω σpath h h_symm'

end JacobianChallenge.Periods
