import Mathlib.Geometry.Manifold.Complex

namespace JacobianChallenge.HolomorphicForms

/-- Stubbed ℂ-manifold bump function. Step-1 agent will replace `axiom` with `def`
plus genuine smooth-bump construction; do not reference the implementation. -/
axiom cMfldBump
    {X : Type _} [TopologicalSpace X] [ChartedSpace ℂ X]
    (Q : X) : X → ℝ

axiom cMfldBump_apply_self
    {X : Type _} [TopologicalSpace X] [ChartedSpace ℂ X]
    (Q : X) : cMfldBump Q Q = 1

axiom cMfldBump_continuous
    {X : Type _} [TopologicalSpace X] [T2Space X] [ChartedSpace ℂ X]
    (Q : X) : Continuous (cMfldBump (X := X) Q)

axiom cMfldBump_eq_zero_off_chartSource
    {X : Type _} [TopologicalSpace X] [ChartedSpace ℂ X]
    (Q : X) : ∀ x : X, x ∉ (chartAt ℂ Q).source → cMfldBump Q x = 0

axiom cMfldBump_eq_one_near
    {X : Type _} [TopologicalSpace X] [ChartedSpace ℂ X]
    (Q : X) : ∃ U : Set X, IsOpen U ∧ Q ∈ U ∧ ∀ x ∈ U, cMfldBump Q x = 1

end JacobianChallenge.HolomorphicForms
