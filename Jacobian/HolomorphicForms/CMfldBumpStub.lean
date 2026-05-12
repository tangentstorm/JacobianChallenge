import Mathlib.Geometry.Manifold.Complex

namespace JacobianChallenge.HolomorphicForms

/-- Stubbed ℂ-manifold bump function. -/
noncomputable def cMfldBump
    {X : Type _} [TopologicalSpace X] [ChartedSpace ℂ X]
    (_Q : X) : X → ℝ := by
  exact fun _ => 0

theorem cMfldBump_apply_self
    {X : Type _} [TopologicalSpace X] [ChartedSpace ℂ X]
    (Q : X) : cMfldBump Q Q = 1 := by
  sorry

theorem cMfldBump_continuous
    {X : Type _} [TopologicalSpace X] [T2Space X] [ChartedSpace ℂ X]
    (Q : X) : Continuous (cMfldBump (X := X) Q) := by
  exact continuous_const

theorem cMfldBump_eq_zero_off_chartSource
    {X : Type _} [TopologicalSpace X] [ChartedSpace ℂ X]
    (Q : X) : ∀ x : X, x ∉ (chartAt ℂ Q).source → cMfldBump Q x = 0 := by
  intro x _hx
  simp [cMfldBump]

-- BLOCKER: `cMfldBump_eq_one_near` is unprovable as written.
--
-- With the current definition `cMfldBump _Q := fun _ => 0`, the conclusion
-- forces `cMfldBump Q Q = 1` (since `Q ∈ U`), which reduces to `0 = 1`.
-- Hence the theorem is provably false against the present stub.
--
-- Any honest redefinition of `cMfldBump` must simultaneously satisfy:
--   (a) `cMfldBump Q Q = 1`                          (cMfldBump_apply_self)
--   (b) `cMfldBump Q x = 0` for `x ∉ chartAt ℂ Q`    (cMfldBump_eq_zero_off_chartSource)
--   (c) `Continuous (cMfldBump Q)`                   (cMfldBump_continuous)
--   (d) `cMfldBump Q = 1` on an open nbhd of `Q`     (this theorem)
-- This is precisely a continuous (real) bump function supported in the chart
-- source. Building it requires infrastructure not present at these typeclass
-- assumptions:
--   * a normality / regularity hypothesis on `X` (only `T2Space` is available,
--     and only inside `cMfldBump_continuous`), or
--   * pulling back a continuous bump on `ℂ` through `chartAt ℂ Q`, which needs
--     `chartAt ℂ Q` treated as a partial homeomorphism with an embedded
--     closed disk around `chartAt ℂ Q Q` whose preimage is closed in `X`.
-- The Mathlib analogue is `Mathlib.Analysis.Calculus.BumpFunction.Basic`
-- (`ContDiffBump`); transporting one through a chart on a `ChartedSpace ℂ X`
-- requires at minimum `IsManifold` plus a regular/normal `X`. Until that is
-- added (and the definition of `cMfldBump` is upgraded accordingly), this
-- theorem cannot be discharged.
--
-- Prerequisite to unblock: a manifold bump function
-- `ChartedSpace.bump : (Q : X) → X → ℝ` with the four properties above,
-- presumably built from `ContDiffBump` on `ℂ` and a regular/normal assumption.
theorem cMfldBump_eq_one_near
    {X : Type _} [TopologicalSpace X] [ChartedSpace ℂ X]
    (Q : X) : ∃ U : Set X, IsOpen U ∧ Q ∈ U ∧ ∀ x ∈ U, cMfldBump Q x = 1 := by
  sorry

end JacobianChallenge.HolomorphicForms
