import Jacobian.Periods.PathPartition
import Jacobian.Periods.PathIntegralChartCorrect
import Jacobian.Periods.PathIntegralViaChartCorrect
import Jacobian.Periods.DivFinIcc
import Mathlib.Topology.Subpath

/-!
# Multi-chart path integral

Definition `pathIntegralViaCoverWith ω γ n hn pickChart hcov` —
the path integral of a holomorphic 1-form along a path `γ : Path a b`
on `X` that may cross chart boundaries, given an explicit partition
into `n` segments each contained in some chart's source.

The unparameterised wrapper `pathIntegralViaCover ω γ` (using
`exists_uniform_chart_partition` to produce the partition via
`Classical.choose`) lives in a separate file once linearity of the
parameterised version stabilises (well-definedness across partitions
is the hard step).

Linearity, `_refl`, and well-definedness are deferred follow-up
packets — see `PathIntegralViaCoverRecon.lean` for the design plan.
-/

namespace JacobianChallenge.Periods

open Set unitInterval JacobianChallenge.HolomorphicForms

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {X : Type*} [TopologicalSpace X] [ChartedSpace E X]
  [IsManifold (modelWithCornersSelf ℂ E) (⊤ : WithTop ℕ∞) X]

/-- Multi-chart path integral with an explicit partition + chart pick.

Given a path `γ : Path a b` on `X` and a uniform-chart partition into
`n` segments each contained in some chart's source (witnessed by
`pickChart` and `hcov`), sum the chart-local corrected integrals on
each segment.

The unparameterised wrapper that picks a partition via
`exists_uniform_chart_partition` is in a follow-up file. -/
noncomputable def pathIntegralViaCoverWith
    (ω : HolomorphicOneForm E X)
    {a b : X} (γ : Path a b)
    (n : ℕ) (hn : 0 < n) (pickChart : Fin n → X)
    (hcov : ∀ (i : Fin n) (t : unitInterval),
      (i : ℝ) / n ≤ (t : ℝ) → (t : ℝ) ≤ ((i : ℝ) + 1) / n →
      γ t ∈ (chartAt E (pickChart i)).source) : ℂ :=
  ∑ i : Fin n,
    pathIntegralViaChartCorrect (chartAt E (pickChart i)) ω
      (γ.subpath (divFinIcc n hn i.val (le_of_lt i.isLt))
                 (divFinIcc n hn (i.val + 1) i.isLt))
      (by
        rw [Path.range_subpath]
        intro x hx
        obtain ⟨t, ht, rfl⟩ := hx
        rw [Set.uIcc_of_le (divFinIcc_le_succ n hn i.val i.isLt)] at ht
        rcases Set.mem_Icc.mp ht with ⟨h1, h2⟩
        have hle1 : ((i.val : ℝ) / n) ≤ (t : ℝ) := h1
        have hle2 : (t : ℝ) ≤ ((i.val : ℝ) + 1) / n := by
          have h2' : (t : ℝ) ≤ (divFinIcc n hn (i.val + 1) i.isLt : ℝ) := h2
          rw [divFinIcc_val] at h2'
          push_cast at h2'
          exact h2'
        exact hcov i t hle1 hle2)

end JacobianChallenge.Periods
