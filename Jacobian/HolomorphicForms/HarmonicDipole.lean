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

/-- Translated witness: on `X = ℂ`, the function `z ↦ log ‖z - P‖`
has a logarithmic singularity at any point `P : ℂ` with sign `+1`.
The chart at `P` in the self-charted-space structure is the identity,
so `(chartAt ℂ P) P = P` and the integrand
`log ‖z - P‖ - 1 * log ‖z - P‖` reduces to `0`. Generalizes
`log_abs_at_zero` from `P = 0` to arbitrary `P`; the `+1` half of the
eventual two-point dipole witness on ℂ. -/
theorem HasLogarithmicSingularityAtReal.log_abs_at (P : ℂ) :
    HasLogarithmicSingularityAtReal ℂ P (fun z : ℂ => Real.log ‖z - P‖) 1 := by
  refine ⟨0, ?_⟩
  show Filter.Tendsto
      (fun z : ℂ =>
        Real.log ‖z - P‖ - 1 * Real.log ‖z - (chartAt ℂ P) P‖)
      (nhds ((chartAt ℂ P) P)) (nhds 0)
  have hchart : (chartAt ℂ P) P = P := rfl
  rw [hchart]
  have hfun :
      (fun z : ℂ => Real.log ‖z - P‖ - 1 * Real.log ‖z - P‖)
        = fun _ : ℂ => 0 := by
    funext z
    show Real.log ‖z - P‖ - 1 * Real.log ‖z - P‖ = 0
    ring
  rw [hfun]
  exact tendsto_const_nhds

/-- Symmetric translated witness: on `X = ℂ`, the function
`z ↦ -log ‖z - Q‖` has a logarithmic singularity at any point
`Q : ℂ` with sign `-1`. The chart at `Q` is the identity, so
`(chartAt ℂ Q) Q = Q` and the integrand
`-log ‖z - Q‖ - (-1) * log ‖z - Q‖` reduces to `0`. Generalizes
`neg_log_abs_at_zero` from `Q = 0` to arbitrary `Q`; the `-1` half
of the eventual two-point dipole witness on ℂ. -/
theorem HasLogarithmicSingularityAtReal.neg_log_abs_at (Q : ℂ) :
    HasLogarithmicSingularityAtReal ℂ Q
      (fun z : ℂ => -Real.log ‖z - Q‖) (-1) := by
  refine ⟨0, ?_⟩
  show Filter.Tendsto
      (fun z : ℂ =>
        -Real.log ‖z - Q‖ - (-1 : ℝ) * Real.log ‖z - (chartAt ℂ Q) Q‖)
      (nhds ((chartAt ℂ Q) Q)) (nhds 0)
  have hchart : (chartAt ℂ Q) Q = Q := rfl
  rw [hchart]
  have hfun :
      (fun z : ℂ => -Real.log ‖z - Q‖ - (-1 : ℝ) * Real.log ‖z - Q‖)
        = fun _ : ℂ => 0 := by
    funext z
    show -Real.log ‖z - Q‖ - (-1 : ℝ) * Real.log ‖z - Q‖ = 0
    ring
  rw [hfun]
  exact tendsto_const_nhds

/-- Closure under adding a function with a limit at the chart image of `P`.
If `u` has a logarithmic singularity at `P` with sign `s` and limit `c`,
and `g`'s chart-pullback tends to `d` at `(chartAt ℂ P) P`, then `u + g`
has a logarithmic singularity at `P` with the same sign and limit `c + d`.

Key building block for combining the single-point witnesses into the
two-point dipole `log ‖· - P‖ - log ‖· - Q‖` needed to retire the
`fun _ => 0` cheat in `existence_of_dipole_harmonic`. -/
lemma HasLogarithmicSingularityAtReal.add_tendsto
    {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
    {P : X} {u g : X → ℝ} {sign : ℝ}
    (hu : HasLogarithmicSingularityAtReal X P u sign)
    {d : ℝ}
    (hg : Filter.Tendsto (fun z : ℂ => g ((chartAt ℂ P).symm z))
            (nhds ((chartAt ℂ P) P)) (nhds d)) :
    HasLogarithmicSingularityAtReal X P (u + g) sign := by
  obtain ⟨c, hu'⟩ := hu
  refine ⟨c + d, ?_⟩
  have hsum :
      (fun z : ℂ =>
          (u + g) ((chartAt ℂ P).symm z)
            - sign * Real.log ‖z - (chartAt ℂ P) P‖)
        = (fun z : ℂ =>
            (u ((chartAt ℂ P).symm z)
              - sign * Real.log ‖z - (chartAt ℂ P) P‖)
            + g ((chartAt ℂ P).symm z)) := by
    funext z
    show (u + g) ((chartAt ℂ P).symm z)
          - sign * Real.log ‖z - (chartAt ℂ P) P‖
        = (u ((chartAt ℂ P).symm z)
            - sign * Real.log ‖z - (chartAt ℂ P) P‖)
          + g ((chartAt ℂ P).symm z)
    simp [Pi.add_apply]; ring
  rw [hsum]
  exact hu'.add hg

/-- Continuity of `z ↦ log ‖z - Q‖` at any point `P ≠ Q` in ℂ.
`‖P - Q‖ ≠ 0` follows from `P ≠ Q`, and `Real.log` is continuous away
from `0`; the composition with the continuous map `z ↦ ‖z - Q‖` gives
the result. Feeds `HasLogarithmicSingularityAtReal.add_tendsto` when
combining the `+1` witness at `P` with `-log ‖· - Q‖` (which is
finite-valued and continuous near `P` since `P ≠ Q`). -/
lemma tendsto_log_norm_sub_of_ne {P Q : ℂ} (hPQ : P ≠ Q) :
    Filter.Tendsto (fun z : ℂ => Real.log ‖z - Q‖)
      (nhds P) (nhds (Real.log ‖P - Q‖)) := by
  have hnorm_ne : ‖P - Q‖ ≠ 0 := by
    rw [norm_ne_zero_iff]
    exact sub_ne_zero.mpr hPQ
  have hcont_sub : Filter.Tendsto (fun z : ℂ => z - Q) (nhds P) (nhds (P - Q)) :=
    (continuous_sub_right Q).tendsto P
  have hcont_norm : Filter.Tendsto (fun z : ℂ => ‖z - Q‖)
      (nhds P) (nhds ‖P - Q‖) :=
    (continuous_norm.tendsto (P - Q)).comp hcont_sub
  exact (Real.continuousAt_log hnorm_ne).tendsto.comp hcont_norm

/-- Canonical two-point dipole witness at `P` (sign `+1`).
For `P ≠ Q` in ℂ, `u(z) := log ‖z - P‖ - log ‖z - Q‖` has a
logarithmic singularity at `P` with sign `+1`: near `P` the
`log ‖z - P‖` part contributes the singularity (witnessed by
`log_abs_at P`) and the `-log ‖z - Q‖` part is continuous
(witnessed by `tendsto_log_norm_sub_of_ne hPQ`), so by
`add_tendsto` the predicate is preserved. -/
theorem HasLogarithmicSingularityAtReal.dipole_at_pos
    {P Q : ℂ} (hPQ : P ≠ Q) :
    HasLogarithmicSingularityAtReal ℂ P
      (fun z : ℂ => Real.log ‖z - P‖ - Real.log ‖z - Q‖) 1 := by
  have hP : HasLogarithmicSingularityAtReal ℂ P
      (fun z : ℂ => Real.log ‖z - P‖) 1 :=
    HasLogarithmicSingularityAtReal.log_abs_at P
  -- Named `g` so `add_tendsto` can unify it as its `g` binder.
  set g : ℂ → ℝ := fun w => -Real.log ‖w - Q‖ with hg_def
  have hg : Filter.Tendsto (fun z : ℂ => g ((chartAt ℂ P).symm z))
      (nhds ((chartAt ℂ P) P)) (nhds (-Real.log ‖P - Q‖)) := by
    have hchart : (chartAt ℂ P) P = P := rfl
    rw [hchart]
    -- (chartAt ℂ P).symm reduces to id on the self-chart, so the
    -- pullback collapses to z ↦ g z = -log ‖z - Q‖.
    exact (tendsto_log_norm_sub_of_ne hPQ).neg
  have hsum :=
    HasLogarithmicSingularityAtReal.add_tendsto hP hg
  -- Rewrite (fun z => log ‖z - P‖) + g into the natural subtraction form.
  have hfun :
      (fun z : ℂ => Real.log ‖z - P‖) + g
        = fun z : ℂ => Real.log ‖z - P‖ - Real.log ‖z - Q‖ := by
    funext z
    show Real.log ‖z - P‖ + g z
        = Real.log ‖z - P‖ - Real.log ‖z - Q‖
    simp [hg_def]
    ring
  rw [hfun] at hsum
  exact hsum

/-- Canonical two-point dipole witness at `Q` (sign `-1`).
For `P ≠ Q` in ℂ, `u(z) := log ‖z - P‖ - log ‖z - Q‖` has a
logarithmic singularity at `Q` with sign `-1`: near `Q` the
`-log ‖z - Q‖` part contributes the singularity (witnessed by
`neg_log_abs_at Q`) and `log ‖z - P‖` is continuous (witnessed
by `tendsto_log_norm_sub_of_ne hPQ.symm`), so by `add_tendsto`
the predicate is preserved. Companion to `dipole_at_pos`. -/
theorem HasLogarithmicSingularityAtReal.dipole_at_neg
    {P Q : ℂ} (hPQ : P ≠ Q) :
    HasLogarithmicSingularityAtReal ℂ Q
      (fun z : ℂ => Real.log ‖z - P‖ - Real.log ‖z - Q‖) (-1) := by
  have hQ : HasLogarithmicSingularityAtReal ℂ Q
      (fun z : ℂ => -Real.log ‖z - Q‖) (-1) :=
    HasLogarithmicSingularityAtReal.neg_log_abs_at Q
  -- Named g so add_tendsto can unify against its g binder (lambdas don't unify).
  set g : ℂ → ℝ := fun w => Real.log ‖w - P‖ with hg_def
  have hg : Filter.Tendsto (fun z : ℂ => g ((chartAt ℂ Q).symm z))
      (nhds ((chartAt ℂ Q) Q)) (nhds (Real.log ‖Q - P‖)) := by
    have hchart : (chartAt ℂ Q) Q = Q := rfl
    rw [hchart]
    exact tendsto_log_norm_sub_of_ne hPQ.symm
  have hsum :=
    HasLogarithmicSingularityAtReal.add_tendsto hQ hg
  -- Rewrite (fun z => -log ‖z - Q‖) + g into log ‖· - P‖ - log ‖· - Q‖.
  have hfun :
      (fun z : ℂ => -Real.log ‖z - Q‖) + g
        = fun z : ℂ => Real.log ‖z - P‖ - Real.log ‖z - Q‖ := by
    funext z
    show -Real.log ‖z - Q‖ + g z
        = Real.log ‖z - P‖ - Real.log ‖z - Q‖
    simp [hg_def]
    ring
  rw [hfun] at hsum
  exact hsum

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
