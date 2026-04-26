import Jacobian.Periods.PathIntegralViaChartCorrect

/-!
# Path-congruence helpers for the chart-corrected path integral

When two paths are equal (as Path values), the corrected from-`X`
chart-local integral takes the same value, regardless of which
range-hypothesis proof you use. This is the path-level analogue
of proof irrelevance: by `subst` plus definitional equality of
proofs in `Prop`.

These lemmas help work around dependent-type rewrite issues that
arise when trying to substitute one path for another inside
`pathIntegralViaChartCorrect c ω γ h`, where `h` depends on `γ`.
-/

namespace JacobianChallenge.Periods

open Set
open JacobianChallenge.HolomorphicForms

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {X : Type*} [TopologicalSpace X] [ChartedSpace E X]
  [IsManifold (modelWithCornersSelf ℂ E) (⊤ : WithTop ℕ∞) X]

/-- If two paths agree, their corrected from-`X` integrals agree
under any (possibly different) range-hypothesis proofs. -/
theorem pathIntegralViaChartCorrect_eq_of_path_eq
    (c : OpenPartialHomeomorph X E) (ω : HolomorphicOneForm E X)
    {a b : X} {γ γ' : Path a b} (hγ : γ = γ')
    (h : range γ ⊆ c.source) (h' : range γ' ⊆ c.source) :
    pathIntegralViaChartCorrect c ω γ h =
      pathIntegralViaChartCorrect c ω γ' h' := by
  subst hγ
  rfl

/-- Provisional analogue: if two paths agree, their from-`X`
integrals agree. -/
theorem pathIntegralViaChart_eq_of_path_eq
    (c : OpenPartialHomeomorph X E) (ω : HolomorphicOneForm E X)
    {a b : X} {γ γ' : Path a b} (hγ : γ = γ')
    (h : range γ ⊆ c.source) (h' : range γ' ⊆ c.source) :
    pathIntegralViaChart c ω γ h =
      pathIntegralViaChart c ω γ' h' := by
  subst hγ
  rfl

/-- HEq version: if two paths between possibly-different endpoints
agree heterogeneously, their corrected from-`X` integrals are equal.
Useful when the endpoint terms are propositionally equal but not
definitionally — e.g. `γ (σ (i/n))` vs `γ ((n-i)/n)`. -/
theorem pathIntegralViaChartCorrect_eq_of_heq
    (c : OpenPartialHomeomorph X E) (ω : HolomorphicOneForm E X)
    {a b a' b' : X} (ha : a = a') (hb : b = b')
    {γ : Path a b} {γ' : Path a' b'} (hγ : HEq γ γ')
    (h : range γ ⊆ c.source) (h' : range γ' ⊆ c.source) :
    pathIntegralViaChartCorrect c ω γ h =
      pathIntegralViaChartCorrect c ω γ' h' := by
  subst ha
  subst hb
  cases hγ
  rfl

end JacobianChallenge.Periods
