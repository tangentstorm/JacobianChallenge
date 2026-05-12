import Mathlib.Geometry.Manifold.Complex

namespace JacobianChallenge.HolomorphicForms

/-- Stubbed ℂ-manifold bump function. -/
noncomputable def cMfldBump
    {X : Type _} [TopologicalSpace X] [ChartedSpace ℂ X]
    (_Q : X) : X → ℝ := by
  exact fun _ => 0

-- BLOCKER: `cMfldBump_apply_self` cannot be proved while `cMfldBump` is the
-- placeholder `fun _ => 0`: the goal reduces to `0 = 1`. Repairing the
-- definition in isolation is also blocked, because the three sorry-free
-- siblings in this file jointly pin down a continuous function on `X` that
-- equals `1` at `Q` and `0` off `(chartAt ℂ Q).source`:
--   * `cMfldBump_continuous` is closed by `continuous_const`, which only
--     types if `cMfldBump Q` is definitionally constant.
--   * `cMfldBump_eq_zero_off_chartSource` is closed by `simp [cMfldBump]`,
--     which requires the body to reduce to `0` off the chart source.
--   * `cMfldBump_apply_self` requires the value `1` at `Q`.
-- A constant function cannot satisfy all three; an indicator of the
-- (open, not generally clopen) chart source is not continuous; and a
-- pointwise `if x = Q` discriminator is not continuous in non-discrete `X`.
-- Missing prerequisite: a real continuous (eventually `C^∞`) bump function
-- on `X` of value `1` at `Q` with support inside `(chartAt ℂ Q).source`,
-- e.g. via `ContDiffBump` on `ℂ` pulled back through `chartAt ℂ Q` and
-- extended by `0` off the chart source. Constructing such a bump requires
-- writing both the definition (in this file) and the supporting `Continuous`
-- proof together, which exceeds a single-sorry change here.
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

theorem cMfldBump_eq_one_near
    {X : Type _} [TopologicalSpace X] [ChartedSpace ℂ X]
    (Q : X) : ∃ U : Set X, IsOpen U ∧ Q ∈ U ∧ ∀ x ∈ U, cMfldBump Q x = 1 := by
  sorry

end JacobianChallenge.HolomorphicForms
