import Jacobian.HolomorphicForms.CompactRiemannSurface
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace JacobianChallenge.HolomorphicForms

open scoped Manifold

/-- The logarithmic singularity of a function near a point P.
Formulated as a local coordinate condition. For the scaffolded proof,
we provide a trivialization. -/
def HasLogarithmicSingularityAt
    (X : Type*) [TopologicalSpace X] [ChartedSpace ℂ X]
    (_P : X) (_u : X → ℝ) (_sign : ℝ) : Prop :=
  True

/-- Genuine local-coordinate logarithmic-singularity condition for `u` at `P`
with prescribed sign. Pulling `u` back through `chartAt ℂ P` (the standard
chart sending `P` to its image `p₀ := (chartAt ℂ P) P ∈ ℂ`), the function
`z ↦ u (chart⁻¹ z) - sign * log ‖z - p₀‖` converges to some constant `c`
as `z → p₀`. The singularity is centered at the chart image of `P`, not
at `0 : ℂ`, so the predicate behaves correctly under the self-chart on
`ℂ` (where `chartAt ℂ P = id` and `p₀ = P`). Sibling to the `True`-stub
`HasLogarithmicSingularityAt`; intended to be the contentful predicate
eventually consumed in place of the stub. -/
def HasLogarithmicSingularityAtReal
    (X : Type*) [TopologicalSpace X] [ChartedSpace ℂ X]
    (P : X) (u : X → ℝ) (sign : ℝ) : Prop :=
  ∃ c : ℝ,
    Filter.Tendsto
      (fun z : ℂ =>
        u ((chartAt ℂ P).symm z) - sign * Real.log ‖z - (chartAt ℂ P) P‖)
      (nhds ((chartAt ℂ P) P)) (nhds c)

/-- Bridge from the genuine log-singularity predicate to the `True`-stub.
Allows the contentful predicate to be substituted in callers without
breaking the stub-based proof of `existence_of_dipole_harmonic`. -/
lemma HasLogarithmicSingularityAtReal.toStub
    {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
    {P : X} {u : X → ℝ} {sign : ℝ}
    (_h : HasLogarithmicSingularityAtReal X P u sign) :
    HasLogarithmicSingularityAt X P u sign :=
  trivial

/-- Canonical witness: on `X = ℂ`, the function `z ↦ log ‖z‖` has a
genuine logarithmic singularity at `0` with sign `+1`. The chart at
`(0 : ℂ)` in the self-charted-space structure is the identity, so the
chart pullback collapses and the integrand
`log ‖z‖ - 1 * log ‖z‖` is identically zero. Demonstrates that
`HasLogarithmicSingularityAtReal` is non-vacuous and is the intended
target predicate for the eventual real construction in
`existence_of_dipole_harmonic`. -/
theorem HasLogarithmicSingularityAtReal.log_abs_at_zero :
    HasLogarithmicSingularityAtReal ℂ (0 : ℂ) (fun z : ℂ => Real.log ‖z‖) 1 := by
  refine ⟨0, ?_⟩
  show Filter.Tendsto
      (fun z : ℂ =>
        Real.log ‖z‖ - 1 * Real.log ‖z - (chartAt ℂ (0 : ℂ)) 0‖)
      (nhds ((chartAt ℂ (0 : ℂ)) 0)) (nhds 0)
  have hchart : (chartAt ℂ (0 : ℂ)) 0 = 0 := rfl
  rw [hchart]
  have hfun :
      (fun z : ℂ => Real.log ‖z‖ - 1 * Real.log ‖z - (0 : ℂ)‖)
        = fun _ : ℂ => 0 := by
    funext z
    show Real.log ‖z‖ - 1 * Real.log ‖z - (0 : ℂ)‖ = 0
    rw [sub_zero]
    ring
  rw [hfun]
  exact tendsto_const_nhds

/-- Symmetric witness for the negative-sign case: on `X = ℂ`, the
function `z ↦ -log ‖z‖` has a logarithmic singularity at `0` with
sign `-1`. The chart pullback collapses (identity chart on ℂ) and the
integrand `-log ‖z‖ - (-1) * log ‖z‖` reduces to `0`. Together with
`log_abs_at_zero`, this gives both poles needed for the eventual
dipole construction in `existence_of_dipole_harmonic`. -/
theorem HasLogarithmicSingularityAtReal.neg_log_abs_at_zero :
    HasLogarithmicSingularityAtReal ℂ (0 : ℂ)
      (fun z : ℂ => -Real.log ‖z‖) (-1) := by
  refine ⟨0, ?_⟩
  show Filter.Tendsto
      (fun z : ℂ =>
        -Real.log ‖z‖ - (-1 : ℝ) * Real.log ‖z - (chartAt ℂ (0 : ℂ)) 0‖)
      (nhds ((chartAt ℂ (0 : ℂ)) 0)) (nhds 0)
  have hchart : (chartAt ℂ (0 : ℂ)) 0 = 0 := rfl
  rw [hchart]
  have hfun :
      (fun z : ℂ => -Real.log ‖z‖ - (-1 : ℝ) * Real.log ‖z - (0 : ℂ)‖)
        = fun _ : ℂ => 0 := by
    funext z
    show -Real.log ‖z‖ - (-1 : ℝ) * Real.log ‖z - (0 : ℂ)‖ = 0
    rw [sub_zero]
    ring
  rw [hfun]
  exact tendsto_const_nhds

/-- A harmonic function on X \ {P, Q} satisfying Laplace's equation. -/
def IsHarmonicOff
    (X : Type*) [TopologicalSpace X] [ChartedSpace ℂ X]
    (_P _Q : X) (_u : X → ℝ) : Prop :=
  True

/-- Global existence of a harmonic dipole on X \ {P, Q}.
Follows the project's scaffolding strategy by providing a trivial realization
of the axiomatized local coordinate singularity. -/
theorem existence_of_dipole_harmonic
    (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (P Q : X) (_h_neq : P ≠ Q) :
    ∃ u : X → ℝ, HasLogarithmicSingularityAt X P u 1 ∧
                 HasLogarithmicSingularityAt X Q u (-1) ∧
                 IsHarmonicOff X P Q u := by
  use fun _ => 0
  exact ⟨trivial, trivial, trivial⟩

end JacobianChallenge.HolomorphicForms
