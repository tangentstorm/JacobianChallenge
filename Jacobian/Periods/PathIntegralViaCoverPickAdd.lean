import Jacobian.Periods.PathIntegralViaCoverPick
import Jacobian.Periods.PathIntegralViaCoverWithAdd
import Jacobian.Periods.PathIntegralViaCoverWithRefine
import Jacobian.Periods.PathIntegralViaCoverTrans
import Jacobian.Periods.ChartedFormPullbackCurveIntegrable
import Jacobian.Periods.ChartLiftApply
import Jacobian.TraceDegree.PiecewiseC1Def
import Jacobian.TraceDegree.PiecewiseC1Instance

/-!
# Unconditional addition linearity of `pathIntegralViaCover`

Lifts the conditional `pathIntegralViaCoverWith_add_of_curveIntegrable`
to the unparameterised `pathIntegralViaCover` by:
1. Using the same `Classical.choose`-picked partition for ω, η and ω+η
   (the partition data depends only on `γ`, not on the form).
2. Discharging the per-segment `CurveIntegrable` hypotheses for any
   holomorphic form via the named obligation
   `pathIntegralViaCover_perSegment_curveIntegrable`, which states that
   the chartedFormPullback of a holomorphic 1-form is curve-integrable
   along the chart-lifted segment of a uniform-grain partition.

The per-segment obligation is the natural FTC-type residual: it
combines `pathPiecewiseC1_of_regularity` (the chart-lift C¹ regularity
provided by `[PiecewiseC1PathRegularity X]`) with
`chartedFormPullback_curveIntegrable` (sorry-free: every holomorphic
1-form is integrable along a C¹ path).
-/

namespace JacobianChallenge.Periods

open JacobianChallenge.HolomorphicForms
open JacobianChallenge.TraceDegree

variable {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
  [StableChartAt ℂ X] [PiecewiseC1PathRegularity X]

/-- **Per-segment curve-integrability obligation** (focused residual).

For any holomorphic 1-form `ω` on `X` and any uniform chart-cover
partition of a path `γ`, the chartedFormPullback of `ω` is
curve-integrable along the chart-lifted subpath of every segment.

Discharge route (deferred residual): combine
`pathPiecewiseC1_of_regularity γ` (chart-lift C¹ regularity, gated on
the `[PiecewiseC1PathRegularity X]` typeclass) with
`chartedFormPullback_curveIntegrable` (sorry-free: holomorphic ⇒
curve-integrable for a C¹ path). The plumbing requires unpacking the
per-segment `range subpath ⊆ chart.source` proof and matching the
chartLift's extend regularity to the curve-integrability hypothesis. -/
theorem pathIntegralViaCover_perSegment_curveIntegrable_of_witnesses
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [StableChartAt ℂ X]
    (ω : HolomorphicOneForm ℂ X)
    {a b : X} (γ : Path a b) (hγ : IsChartContDiffPath γ)
    (n : ℕ) (hn : 0 < n) (pickChart : Fin n → X)
    (hcov : ∀ (i : Fin n) (t : unitInterval),
      (i : ℝ) / n ≤ (t : ℝ) → (t : ℝ) ≤ ((i : ℝ) + 1) / n →
      γ t ∈ (chartAt ℂ (pickChart i)).source) (i : Fin n) :
    CurveIntegrable (chartedFormPullback (chartAt ℂ (pickChart i)) ω)
      (chartLift (chartAt ℂ (pickChart i))
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
          exact hcov i t hle1 hle2)) := by
  -- Substantive discharge: combine the witness `hγ.subpath` with
  -- `chartedFormPullback_curveIntegrable` (sorry-free).
  set c := chartAt ℂ (pickChart i) with hc_def
  set γseg := γ.subpath (divFinIcc n hn i.val (le_of_lt i.isLt))
                        (divFinIcc n hn (i.val + 1) i.isLt) with hγseg_def
  set hseg : Set.range γseg ⊆ c.source :=
    range_segment_subset_source_of_hcov γ n hn pickChart hcov i with hseg_def
  -- Maximal-atlas membership of the chart.
  have hc_mem : c ∈ IsManifold.maximalAtlas (modelWithCornersSelf ℂ ℂ)
      (⊤ : WithTop ℕ∞) X :=
    IsManifold.chart_mem_maximalAtlas (pickChart i)
  -- Preimage of chart source over the closed unit interval reduces to [0,1]
  -- because the segment's range is in the chart source by construction.
  have hpre_eq : γseg.extend ⁻¹' c.source ∩ Set.Icc (0 : ℝ) 1 =
      Set.Icc (0 : ℝ) 1 := by
    apply Set.inter_eq_right.mpr
    intro t ht
    show γseg.extend t ∈ c.source
    have ht_mem : t ∈ unitInterval := ht
    rw [γseg.extend_extends' ⟨t, ht_mem⟩]
    exact hseg ⟨⟨t, ht_mem⟩, rfl⟩
  -- C¹ regularity of the chart-lifted segment via the per-path witness.
  have hCD : ContDiffOn ℝ 1 (chartLift c γseg hseg).extend
      (Set.Icc (0 : ℝ) 1) := by
    have h_obl : ContDiffOn ℝ 1 ((c : X → ℂ) ∘ γseg.extend)
        (γseg.extend ⁻¹' c.source ∩ Set.Icc (0 : ℝ) 1) := by
      exact (hγ.subpath _ _) (pickChart i)
    rw [hpre_eq] at h_obl
    show ContDiffOn ℝ 1 ((c : X → ℂ) ∘ γseg.extend) (Set.Icc (0 : ℝ) 1)
    exact h_obl
  -- Range of the chart-lifted segment lies in `c.target`.
  have hrange : ∀ t, (chartLift c γseg hseg) t ∈ c.target := by
    intro t
    rw [chartLift_apply]
    exact c.map_source (hseg ⟨t, rfl⟩)
  -- Apply the unconditional curve-integrability lemma.
  exact chartedFormPullback_curveIntegrable c hc_mem ω
    (chartLift c γseg hseg) hCD hrange

/-- Original obligation-based variant; delegates to the witness form
above by supplying the universally-quantified
`path_contDiffOn_obligation` as the per-path witness. The remaining
sorry is concentrated in the obligation itself. -/
theorem pathIntegralViaCover_perSegment_curveIntegrable
    (ω : HolomorphicOneForm ℂ X)
    {a b : X} (γ : Path a b)
    (n : ℕ) (hn : 0 < n) (pickChart : Fin n → X)
    (hcov : ∀ (i : Fin n) (t : unitInterval),
      (i : ℝ) / n ≤ (t : ℝ) → (t : ℝ) ≤ ((i : ℝ) + 1) / n →
      γ t ∈ (chartAt ℂ (pickChart i)).source) (i : Fin n) :
    CurveIntegrable (chartedFormPullback (chartAt ℂ (pickChart i)) ω)
      (chartLift (chartAt ℂ (pickChart i))
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
          exact hcov i t hle1 hle2)) :=
  pathIntegralViaCover_perSegment_curveIntegrable_of_witnesses ω γ
    (fun q => path_contDiffOn_obligation X γ q) n hn pickChart hcov i

/-- **Witness-form variant of `pathIntegralViaCover_add`** (Stage III).
Takes an `IsChartContDiffPath γ` witness explicitly instead of relying
on the universally-quantified `[PiecewiseC1PathRegularity X]` typeclass
route. Sorry-free under the manifold structure + `[StableChartAt ℂ X]`
alone (no `[PiecewiseC1PathRegularity X]` needed). -/
theorem pathIntegralViaCover_add_of_witnesses
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [StableChartAt ℂ X]
    (ω η : HolomorphicOneForm ℂ X) {a b : X} (γ : Path a b)
    (hγ : IsChartContDiffPath γ) :
    pathIntegralViaCover (ω + η) γ =
      pathIntegralViaCover ω γ + pathIntegralViaCover η γ := by
  set p0 := exists_uniform_chart_partition ℂ γ.toContinuousMap with hp0
  set p1 := p0.choose_spec with hp1
  set p2 := p1.choose_spec with hp2
  set n := p0.choose with hn_def
  set hn := p1.choose with hhn_def
  set pickChart := p2.choose with hpick_def
  set hcov := p2.choose_spec with hcov_def
  show pathIntegralViaCoverWith (ω + η) γ n hn pickChart hcov =
      pathIntegralViaCoverWith ω γ n hn pickChart hcov +
        pathIntegralViaCoverWith η γ n hn pickChart hcov
  exact pathIntegralViaCoverWith_add_of_curveIntegrable
    ω η γ n hn pickChart hcov
    (fun i =>
      pathIntegralViaCover_perSegment_curveIntegrable_of_witnesses ω γ hγ n hn pickChart hcov i)
    (fun i =>
      pathIntegralViaCover_perSegment_curveIntegrable_of_witnesses η γ hγ n hn pickChart hcov i)

@[simp] theorem pathIntegralViaCover_add
    (ω η : HolomorphicOneForm ℂ X) {a b : X} (γ : Path a b) :
    pathIntegralViaCover (ω + η) γ =
      pathIntegralViaCover ω γ + pathIntegralViaCover η γ :=
  pathIntegralViaCover_add_of_witnesses ω η γ (fun q => path_contDiffOn_obligation X γ q)

end JacobianChallenge.Periods
