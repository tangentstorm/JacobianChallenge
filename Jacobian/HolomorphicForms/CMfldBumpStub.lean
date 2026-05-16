import Mathlib.Geometry.Manifold.BumpFunction
import Mathlib.Geometry.Manifold.Complex

namespace JacobianChallenge.HolomorphicForms

open scoped Manifold Topology

/-- A smooth bump function in a complex chart, centered at `Q`. -/
noncomputable def cMfldBump
    {X : Type _} [TopologicalSpace X] [ChartedSpace ℂ X]
    (Q : X) : X → ℝ :=
  let f : SmoothBumpFunction (𝓘(ℝ, ℂ)) Q :=
    Classical.choice (show Nonempty (SmoothBumpFunction (𝓘(ℝ, ℂ)) Q) from inferInstance)
  f

theorem cMfldBump_apply_self
    {X : Type _} [TopologicalSpace X] [ChartedSpace ℂ X]
    (Q : X) : cMfldBump Q Q = 1 := by
  rw [cMfldBump]
  exact SmoothBumpFunction.eq_one _

theorem cMfldBump_continuous
    {X : Type _} [TopologicalSpace X] [T2Space X] [ChartedSpace ℂ X]
    [IsManifold (𝓘(ℝ, ℂ)) (⊤ : WithTop ℕ∞) X]
    (Q : X) : Continuous (cMfldBump (X := X) Q) := by
  rw [cMfldBump]
  exact SmoothBumpFunction.continuous _

theorem cMfldBump_eq_zero_off_chartSource
    {X : Type _} [TopologicalSpace X] [ChartedSpace ℂ X]
    (Q : X) : ∀ x : X, x ∉ (chartAt ℂ Q).source → cMfldBump Q x = 0 := by
  intro x _hx
  simp [cMfldBump, SmoothBumpFunction.coe_def, _hx]

theorem cMfldBump_eq_one_near
    {X : Type _} [TopologicalSpace X] [ChartedSpace ℂ X]
    (Q : X) : ∃ U : Set X, IsOpen U ∧ Q ∈ U ∧ ∀ x ∈ U, cMfldBump Q x = 1 := by
  have hnear : cMfldBump Q =ᶠ[𝓝 Q] 1 := by
    rw [cMfldBump]
    exact SmoothBumpFunction.eventuallyEq_one _
  have hnear' : ∀ᶠ x in 𝓝 Q, cMfldBump Q x = 1 := hnear
  rw [eventually_nhds_iff] at hnear'
  rcases hnear' with ⟨U, hU, hUopen, hQU⟩
  exact ⟨U, hUopen, hQU, hU⟩

end JacobianChallenge.HolomorphicForms
