import Jacobian.Periods.PiecewiseC1Path
import Jacobian.Periods.ChartPullbackStraightPath
import Jacobian.Periods.PathPartition
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Topology.Connected.PathConnected

/-!
# Existence of chart-`C¹` paths with controlled endpoint behaviour

The flagship `closedForm_pathIntegral_primitive_exists` (in
`Jacobian/HolomorphicForms/DeRhamComparisonMap.lean`) requires a chosen
"path from the basepoint" that is chart-`C¹` *and* whose chart-derivative
at the endpoint is zero (so that gluing-via-`Path.trans` with another
chart-`C¹` path is automatically chart-`C¹` at the join — see
`IsChartContDiffPath.trans_of_constant_join`).

This file states the strengthened existence theorem
`exists_chartContDiffPath_constantTail` and reduces it to the strictly
weaker base existential `exists_chartContDiffPath` via a **smooth
reparametrization with constant tail**. The smoothness of the
reparam (via Mathlib's `Real.smoothTransition`, whose derivatives
vanish at the endpoints `0` and `1`) makes the corner at `t = 1 - ε`
*automatically* `C¹` — no derivative-matching obligation on `γ`.

## Outline

1. **`Path.smoothReparamConstantTail`** (root `Path` namespace) —
   reparametrize via `t ↦ γ.extend (Real.smoothTransition (t / (1 - ε)))`.
   The smooth transition is constantly `0` for `t ≤ 0` and constantly `1`
   for `t ≥ 1`, so the composition is constantly `b = γ.target` for
   `t ≥ 1 - ε` (constant tail), and matches `γ`'s shape on `(0, 1 - ε)`.
2. **Extend formula** — uniform `γ.extend ∘ Real.smoothTransition ∘ (·/(1-ε))`
   on `Icc 0 1`, with explicit value `b` on `[1 - ε, 1]`.
3. **`IsChartContDiffPath.smoothReparamConstantTail`** — preservation:
   sorry-free, via `ContDiffOn.comp` with the smooth transition.
4. **`exists_chartContDiffPath`** — sorry'd base existential (TRUE; the
   natural existence statement on a compact connected complex 1-manifold).
5. **`exists_chartContDiffPath_constantTail`** — sorry-free discharge:
   take a base witness and reparametrize.
-/

namespace Path

open Real

/-- **Smooth reparametrization with constant tail.**

Given a path `γ : Path a b` and `0 < ε < 1`, produces a path with the
same endpoints whose `extend` is `γ.extend ∘ Real.smoothTransition ∘ (·/(1-ε))`
on `Icc 0 1`. Key properties:

* Smooth: the composition is `C^∞` in `t` on `ℝ` (via `Real.smoothTransition.contDiff`).
* Constant tail: for `t ≥ 1 - ε`, the smooth-transition argument
  `t / (1 - ε) ≥ 1`, so `Real.smoothTransition = 1` and `γ.extend 1 = b`.
* Constant head: for `t ≤ 0`, the smooth-transition argument is `≤ 0`,
  so `Real.smoothTransition = 0` and `γ.extend 0 = a`. (Inside the unit
  interval `t ∈ (0, 1-ε)`, the reparam smoothly traverses γ's range.)

The smooth-transition's derivative vanishes at `0` and `1`, so the
chart-pullback's derivative at `t = 1 - ε` is `0` regardless of `γ`'s
own chart-derivative at its endpoint. This is what makes the
preservation lemma `IsChartContDiffPath.smoothReparamConstantTail`
sorry-free *for arbitrary `γ`*. -/
noncomputable def smoothReparamConstantTail
    {X : Type*} [TopologicalSpace X] {a b : X} (γ : Path a b)
    (ε : ℝ) (hε : 0 < ε ∧ ε < 1) : Path a b := by
  have hone_sub_pos : 0 < 1 - ε := by linarith [hε.2]
  refine Path.ofLine
    (f := fun t : ℝ => γ.extend (Real.smoothTransition (t / (1 - ε)))) ?_ ?_ ?_
  · -- ContinuousOn on `unitInterval`.
    refine Continuous.continuousOn ?_
    exact γ.extend.continuous.comp
      (Real.smoothTransition.continuous.comp (continuous_id.div_const (1 - ε)))
  · -- f 0 = a.
    show γ.extend (Real.smoothTransition (0 / (1 - ε))) = a
    rw [zero_div, Real.smoothTransition.zero, γ.extend_zero]
  · -- f 1 = b.
    show γ.extend (Real.smoothTransition (1 / (1 - ε))) = b
    have h_ge_one : (1 : ℝ) ≤ 1 / (1 - ε) := by
      rw [le_div_iff₀ hone_sub_pos]; linarith [hε.1]
    rw [Real.smoothTransition.one_of_one_le h_ge_one, γ.extend_one]

/-- Extend formula for `smoothReparamConstantTail` on `Icc 0 1`:
the extended path is `γ.extend ∘ Real.smoothTransition ∘ (·/(1-ε))`. -/
theorem smoothReparamConstantTail_extend
    {X : Type*} [TopologicalSpace X] {a b : X} (γ : Path a b)
    (ε : ℝ) (hε : 0 < ε ∧ ε < 1) (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    (γ.smoothReparamConstantTail ε hε).extend t =
      γ.extend (Real.smoothTransition (t / (1 - ε))) := by
  unfold smoothReparamConstantTail
  rw [Path.extend_apply _ ht]
  rfl

/-- On `[1 - ε, 1]`, the smoothly-reparametrized path is constantly `b`. -/
theorem smoothReparamConstantTail_extend_eq_target
    {X : Type*} [TopologicalSpace X] {a b : X} (γ : Path a b)
    (ε : ℝ) (hε : 0 < ε ∧ ε < 1) (t : ℝ)
    (ht_lb : 1 - ε ≤ t) (ht_ub : t ≤ 1) :
    (γ.smoothReparamConstantTail ε hε).extend t = b := by
  have hone_sub_pos : 0 < 1 - ε := by linarith [hε.2]
  have ht0 : 0 ≤ t := by linarith [hε.1]
  rw [smoothReparamConstantTail_extend γ ε hε t ⟨ht0, ht_ub⟩]
  have h_ge_one : (1 : ℝ) ≤ t / (1 - ε) := by
    rw [le_div_iff₀ hone_sub_pos]; linarith
  rw [Real.smoothTransition.one_of_one_le h_ge_one, γ.extend_one]

/-! ### Smooth reparametrization with constant head AND tail -/

/-- **Smooth reparametrization with constant head AND constant tail.**

Given a path `γ : Path a b` and `0 < ε < 1/2`, produces a path with the
same endpoints whose `extend` is `γ.extend ∘ ψ` on `Icc 0 1`, where
`ψ(t) := Real.smoothTransition ((t - ε) / (1 - 2*ε))`. Key properties:

* Constant head: for `t ∈ [0, ε]`, `(t - ε)/(1 - 2ε) ≤ 0`, so
  `ψ(t) = 0` and `γ.extend(0) = a`. The path is identically `a`.
* Constant tail: for `t ∈ [1 - ε, 1]`, `(t - ε)/(1 - 2ε) ≥ 1`, so
  `ψ(t) = 1` and `γ.extend(1) = b`. The path is identically `b`.
* Smooth: `ψ` is `C^∞` (composition of `Real.smoothTransition` with an
  affine real map), and at the endpoints of the active interval
  `[ε, 1 - ε]` the derivative of `ψ` is zero (by `smoothTransition`'s
  vanishing derivatives at `0` and `1`).

This is the dual-sided enhancement of `smoothReparamConstantTail`: it
makes BOTH endpoints constant on non-trivial intervals, so the resulting
path can be `Path.trans`'d on either side (or both) with another
constant-end path via `IsChartContDiffPath.trans_of_constant_join`. -/
noncomputable def smoothReparamConstantBoth
    {X : Type*} [TopologicalSpace X] {a b : X} (γ : Path a b)
    (ε : ℝ) (hε : 0 < ε ∧ ε < 1/2) : Path a b := by
  have hone_sub_two_pos : 0 < 1 - 2 * ε := by linarith [hε.2]
  refine Path.ofLine
    (f := fun t : ℝ => γ.extend (Real.smoothTransition ((t - ε) / (1 - 2 * ε)))) ?_ ?_ ?_
  · -- ContinuousOn on `unitInterval`.
    refine Continuous.continuousOn ?_
    exact γ.extend.continuous.comp
      (Real.smoothTransition.continuous.comp
        ((continuous_id.sub continuous_const).div_const (1 - 2 * ε)))
  · -- f 0 = a.
    show γ.extend (Real.smoothTransition ((0 - ε) / (1 - 2 * ε))) = a
    have h_le : ((0 - ε) / (1 - 2 * ε)) ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg (by linarith [hε.1]) hone_sub_two_pos.le
    rw [Real.smoothTransition.zero_of_nonpos h_le, γ.extend_zero]
  · -- f 1 = b.
    show γ.extend (Real.smoothTransition ((1 - ε) / (1 - 2 * ε))) = b
    have h_ge_one : (1 : ℝ) ≤ (1 - ε) / (1 - 2 * ε) := by
      rw [le_div_iff₀ hone_sub_two_pos]; linarith
    rw [Real.smoothTransition.one_of_one_le h_ge_one, γ.extend_one]

/-- Extend formula for `smoothReparamConstantBoth` on `Icc 0 1`. -/
theorem smoothReparamConstantBoth_extend
    {X : Type*} [TopologicalSpace X] {a b : X} (γ : Path a b)
    (ε : ℝ) (hε : 0 < ε ∧ ε < 1/2) (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    (γ.smoothReparamConstantBoth ε hε).extend t =
      γ.extend (Real.smoothTransition ((t - ε) / (1 - 2 * ε))) := by
  unfold smoothReparamConstantBoth
  rw [Path.extend_apply _ ht]
  rfl

/-- On `[0, ε]`, the doubly-smoothed reparametrized path is constantly `a`. -/
theorem smoothReparamConstantBoth_extend_eq_source
    {X : Type*} [TopologicalSpace X] {a b : X} (γ : Path a b)
    (ε : ℝ) (hε : 0 < ε ∧ ε < 1/2) (t : ℝ)
    (ht_lb : 0 ≤ t) (ht_ub : t ≤ ε) :
    (γ.smoothReparamConstantBoth ε hε).extend t = a := by
  have hone_sub_two_pos : 0 < 1 - 2 * ε := by linarith [hε.2]
  have ht1 : t ≤ 1 := by linarith [hε.2]
  rw [smoothReparamConstantBoth_extend γ ε hε t ⟨ht_lb, ht1⟩]
  have h_le : ((t - ε) / (1 - 2 * ε)) ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (by linarith) hone_sub_two_pos.le
  rw [Real.smoothTransition.zero_of_nonpos h_le, γ.extend_zero]

/-- On `[1 - ε, 1]`, the doubly-smoothed reparametrized path is constantly `b`. -/
theorem smoothReparamConstantBoth_extend_eq_target
    {X : Type*} [TopologicalSpace X] {a b : X} (γ : Path a b)
    (ε : ℝ) (hε : 0 < ε ∧ ε < 1/2) (t : ℝ)
    (ht_lb : 1 - ε ≤ t) (ht_ub : t ≤ 1) :
    (γ.smoothReparamConstantBoth ε hε).extend t = b := by
  have hone_sub_two_pos : 0 < 1 - 2 * ε := by linarith [hε.2]
  have ht0 : 0 ≤ t := by linarith [hε.1]
  rw [smoothReparamConstantBoth_extend γ ε hε t ⟨ht0, ht_ub⟩]
  have h_ge_one : (1 : ℝ) ≤ (t - ε) / (1 - 2 * ε) := by
    rw [le_div_iff₀ hone_sub_two_pos]; linarith
  rw [Real.smoothTransition.one_of_one_le h_ge_one, γ.extend_one]

/-- Range of `smoothReparamConstantBoth γ ε hε` is contained in the range of `γ`. -/
theorem smoothReparamConstantBoth_range_subset_range
    {X : Type*} [TopologicalSpace X] {a b : X} (γ : Path a b)
    (ε : ℝ) (hε : 0 < ε ∧ ε < 1/2) :
    Set.range (γ.smoothReparamConstantBoth ε hε) ⊆ Set.range γ := by
  rintro y ⟨t, rfl⟩
  -- (γ.smoothReparam) t = γ.extend (Real.smoothTransition ((t - ε) / (1 - 2ε)))
  -- with smoothTransition output in [0, 1], so γ.extend equals γ on unitInterval.
  set s : ℝ := Real.smoothTransition ((t - ε) / (1 - 2 * ε))
  have hs_mem : s ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩
  have hs_unit : s ∈ unitInterval := hs_mem
  -- Coerce ⟨t, t.2⟩ : unitInterval and unfold reparam definition.
  have h_eq : (γ.smoothReparamConstantBoth ε hε) t = γ ⟨s, hs_unit⟩ := by
    show (γ.smoothReparamConstantBoth ε hε).toFun t = γ ⟨s, hs_unit⟩
    -- Unfold smoothReparamConstantBoth (uses Path.ofLine).
    show γ.extend s = γ ⟨s, hs_unit⟩
    exact γ.extend_extends' ⟨s, hs_unit⟩
  rw [h_eq]
  exact ⟨⟨s, hs_unit⟩, rfl⟩

end Path

namespace JacobianChallenge.TraceDegree

open Set

/-- **Preservation of `IsChartContDiffPath` under doubly-smoothed reparam
(constant head AND constant tail).** Sorry-free for arbitrary `γ`, via the
same `ContDiffOn.comp` route as the tail-only variant. The inner function
`ψ(t) := Real.smoothTransition ((t - ε)/(1 - 2*ε))` is `C^∞` with output
in `[0, 1]`. -/
theorem IsChartContDiffPath.smoothReparamConstantBoth
    {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
    {a b : X} {γ : Path a b} (hγ : IsChartContDiffPath γ)
    (ε : ℝ) (hε : 0 < ε ∧ ε < 1/2) :
    IsChartContDiffPath (γ.smoothReparamConstantBoth ε hε) := by
  intro p
  have hone_sub_two_pos : 0 < 1 - 2 * ε := by linarith [hε.2]
  set ψ : ℝ → ℝ := fun t => Real.smoothTransition ((t - ε) / (1 - 2 * ε)) with hψ_def
  have hψ_contDiff : ContDiff ℝ (1 : WithTop ℕ∞) ψ := by
    have h1 : ContDiff ℝ (1 : WithTop ℕ∞) Real.smoothTransition :=
      Real.smoothTransition.contDiff
    have h2 : ContDiff ℝ (1 : WithTop ℕ∞) (fun t : ℝ => (t - ε) / (1 - 2 * ε)) :=
      (contDiff_id.sub contDiff_const).div_const (1 - 2 * ε)
    exact h1.comp h2
  have hψ_mapsTo_Icc : ∀ t : ℝ, ψ t ∈ Set.Icc (0 : ℝ) 1 := fun t =>
    ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩
  set S : Set ℝ :=
    (γ.smoothReparamConstantBoth ε hε).extend ⁻¹' (chartAt ℂ p).source ∩ Set.Icc 0 1
  have h_eq_on : Set.EqOn ((chartAt ℂ p) ∘ (γ.smoothReparamConstantBoth ε hε).extend)
      ((chartAt ℂ p) ∘ γ.extend ∘ ψ) S := by
    intro t ht
    obtain ⟨_, ht_Icc⟩ := ht
    show (chartAt ℂ p) ((γ.smoothReparamConstantBoth ε hε).extend t)
      = (chartAt ℂ p) (γ.extend (ψ t))
    rw [Path.smoothReparamConstantBoth_extend γ ε hε t ht_Icc]
  have h_maps : Set.MapsTo ψ S
      (γ.extend ⁻¹' (chartAt ℂ p).source ∩ Set.Icc 0 1) := by
    intro t ⟨ht_pre, ht_Icc⟩
    refine ⟨?_, hψ_mapsTo_Icc t⟩
    show γ.extend (ψ t) ∈ (chartAt ℂ p).source
    have h_eq : (γ.smoothReparamConstantBoth ε hε).extend t = γ.extend (ψ t) :=
      Path.smoothReparamConstantBoth_extend γ ε hε t ht_Icc
    rw [← h_eq]; exact ht_pre
  have h_outer : ContDiffOn ℝ 1 ((chartAt ℂ p) ∘ γ.extend)
      (γ.extend ⁻¹' (chartAt ℂ p).source ∩ Set.Icc 0 1) := hγ p
  have h_inner : ContDiffOn ℝ 1 ψ S := hψ_contDiff.contDiffOn
  exact (h_outer.comp h_inner h_maps).congr (fun t ht => h_eq_on ht)

/-- **Preservation of `IsChartContDiffPath` under smooth-reparam with constant tail.**

For any `IsChartContDiffPath γ` and `0 < ε < 1`, the reparametrized path
`γ.smoothReparamConstantTail ε hε` is also `IsChartContDiffPath`.

Proof: the chart-pullback of the reparam is
`(chartAt ℂ p) ∘ γ.extend ∘ Real.smoothTransition ∘ (·/(1-ε))`, and:
* `Real.smoothTransition ∘ (·/(1-ε))` is `ContDiff ℝ ⊤` (composition of smooth functions).
* It maps `ℝ` into `[0, 1]` (by `Real.smoothTransition`'s bounds), so the
  composed inner function maps every t ∈ ℝ to `Icc 0 1`, the natural domain
  of `γ.extend`'s chart-pullback C¹.
* `(chartAt ℂ p) ∘ γ.extend` is `ContDiffOn ℝ 1` on the preimage-intersected-Icc.
* Compose via `ContDiffOn.comp`. -/
theorem IsChartContDiffPath.smoothReparamConstantTail
    {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
    {a b : X} {γ : Path a b} (hγ : IsChartContDiffPath γ)
    (ε : ℝ) (hε : 0 < ε ∧ ε < 1) :
    IsChartContDiffPath (γ.smoothReparamConstantTail ε hε) := by
  intro p
  have hone_sub_pos : 0 < 1 - ε := by linarith [hε.2]
  -- Inner function: ψ(t) := Real.smoothTransition (t / (1-ε)).
  set ψ : ℝ → ℝ := fun t => Real.smoothTransition (t / (1 - ε)) with hψ_def
  -- ψ is C^∞.
  have hψ_contDiff : ContDiff ℝ (1 : WithTop ℕ∞) ψ := by
    have h1 : ContDiff ℝ (1 : WithTop ℕ∞) Real.smoothTransition :=
      Real.smoothTransition.contDiff
    have h2 : ContDiff ℝ (1 : WithTop ℕ∞) (fun t : ℝ => t / (1 - ε)) :=
      contDiff_id.div_const (1 - ε)
    exact h1.comp h2
  -- ψ maps any t into [0, 1] (by smoothTransition.nonneg + .le_one).
  have hψ_mapsTo_Icc : ∀ t : ℝ, ψ t ∈ Set.Icc (0 : ℝ) 1 := fun t =>
    ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩
  -- The composition equals f on Icc 0 1.
  set S : Set ℝ :=
    (γ.smoothReparamConstantTail ε hε).extend ⁻¹' (chartAt ℂ p).source ∩ Set.Icc 0 1
  have h_eq_on : Set.EqOn ((chartAt ℂ p) ∘ (γ.smoothReparamConstantTail ε hε).extend)
      ((chartAt ℂ p) ∘ γ.extend ∘ ψ) S := by
    intro t ht
    obtain ⟨_, ht_Icc⟩ := ht
    show (chartAt ℂ p) ((γ.smoothReparamConstantTail ε hε).extend t)
      = (chartAt ℂ p) (γ.extend (ψ t))
    rw [Path.smoothReparamConstantTail_extend γ ε hε t ht_Icc]
  -- MapsTo ψ from S into γ.extend ⁻¹' (chart).source ∩ Icc 0 1.
  have h_maps : Set.MapsTo ψ S
      (γ.extend ⁻¹' (chartAt ℂ p).source ∩ Set.Icc 0 1) := by
    intro t ⟨ht_pre, ht_Icc⟩
    refine ⟨?_, hψ_mapsTo_Icc t⟩
    -- ψ(t) ∈ γ.extend⁻¹' (chart).source: need γ.extend(ψ t) ∈ (chart).source.
    -- From h_eq_on at t: (chart) (smoothReparam.extend t) = (chart) (γ.extend (ψ t)).
    -- From ht_pre: smoothReparam.extend t ∈ (chart).source.
    -- Apply Path.smoothReparamConstantTail_extend to identify smoothReparam.extend t = γ.extend (ψ t).
    show γ.extend (ψ t) ∈ (chartAt ℂ p).source
    have h_eq : (γ.smoothReparamConstantTail ε hε).extend t = γ.extend (ψ t) :=
      Path.smoothReparamConstantTail_extend γ ε hε t ht_Icc
    rw [← h_eq]; exact ht_pre
  -- Compose: ContDiffOn ((chart) ∘ γ.extend) ∘ ψ on S → ContDiffOn ℝ 1.
  have h_outer : ContDiffOn ℝ 1 ((chartAt ℂ p) ∘ γ.extend)
      (γ.extend ⁻¹' (chartAt ℂ p).source ∩ Set.Icc 0 1) := hγ p
  have h_inner : ContDiffOn ℝ 1 ψ S := hψ_contDiff.contDiffOn
  exact (h_outer.comp h_inner h_maps).congr (fun t ht => h_eq_on ht)

end JacobianChallenge.TraceDegree

namespace JacobianChallenge.Periods

open Set
open JacobianChallenge.TraceDegree

/-! ### Fully-warmed chart-pullback straight path

The chart-pullback straight path with both a constant-head warmup and a
constant-tail warmup, ready to be `Path.trans`'d on either side with
another constant-end path via `IsChartContDiffPath.trans_of_constant_join`. -/

/-- The chart-pullback straight path with a smooth constant-head warmup
at `t = 0` and constant-tail at `t = 1`. Used in the flagship's
`pathPotential_chartLocal_eventually` discharge: both trans-witnesses
(outer and loop) become provable via `trans_of_constant_join`. -/
noncomputable def chartPullbackStraightPathFullyWarmed
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (p x : X) (r : ℝ) (hr_pos : 0 < r)
    (hr_subset : Metric.ball ((chartAt ℂ p) p) r ⊆ (chartAt ℂ p).target)
    (hx : (chartAt ℂ p) x ∈ Metric.ball ((chartAt ℂ p) p) r)
    (hx_source : x ∈ (chartAt ℂ p).source)
    (ε : ℝ) (hε : 0 < ε ∧ ε < 1/2) : Path p x :=
  (chartPullbackStraightPath p x r hr_pos hr_subset hx hx_source).smoothReparamConstantBoth ε hε

/-- The fully-warmed chart-pullback straight path is `IsChartContDiffPath`. -/
theorem chartPullbackStraightPathFullyWarmed_isChartContDiffPath
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (p x : X) (r : ℝ) (hr_pos : 0 < r)
    (hr_subset : Metric.ball ((chartAt ℂ p) p) r ⊆ (chartAt ℂ p).target)
    (hx : (chartAt ℂ p) x ∈ Metric.ball ((chartAt ℂ p) p) r)
    (hx_source : x ∈ (chartAt ℂ p).source)
    (ε : ℝ) (hε : 0 < ε ∧ ε < 1/2) :
    IsChartContDiffPath
      (chartPullbackStraightPathFullyWarmed p x r hr_pos hr_subset hx hx_source ε hε) :=
  (chartPullbackStraightPath_isChartContDiffPath p x r hr_pos hr_subset hx hx_source).smoothReparamConstantBoth ε hε

/-- Constant-head property of the fully-warmed CPS: identically `p` on `[0, ε]`. -/
theorem chartPullbackStraightPathFullyWarmed_extend_eq_source
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (p x : X) (r : ℝ) (hr_pos : 0 < r)
    (hr_subset : Metric.ball ((chartAt ℂ p) p) r ⊆ (chartAt ℂ p).target)
    (hx : (chartAt ℂ p) x ∈ Metric.ball ((chartAt ℂ p) p) r)
    (hx_source : x ∈ (chartAt ℂ p).source)
    (ε : ℝ) (hε : 0 < ε ∧ ε < 1/2) (t : ℝ)
    (ht_lb : 0 ≤ t) (ht_ub : t ≤ ε) :
    (chartPullbackStraightPathFullyWarmed p x r hr_pos hr_subset hx hx_source ε hε).extend t = p :=
  Path.smoothReparamConstantBoth_extend_eq_source _ ε hε t ht_lb ht_ub

/-- Constant-tail property of the fully-warmed CPS: identically `x` on `[1 - ε, 1]`. -/
theorem chartPullbackStraightPathFullyWarmed_extend_eq_target
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (p x : X) (r : ℝ) (hr_pos : 0 < r)
    (hr_subset : Metric.ball ((chartAt ℂ p) p) r ⊆ (chartAt ℂ p).target)
    (hx : (chartAt ℂ p) x ∈ Metric.ball ((chartAt ℂ p) p) r)
    (hx_source : x ∈ (chartAt ℂ p).source)
    (ε : ℝ) (hε : 0 < ε ∧ ε < 1/2) (t : ℝ)
    (ht_lb : 1 - ε ≤ t) (ht_ub : t ≤ 1) :
    (chartPullbackStraightPathFullyWarmed p x r hr_pos hr_subset hx hx_source ε hε).extend t = x :=
  Path.smoothReparamConstantBoth_extend_eq_target _ ε hε t ht_lb ht_ub

/-- Range of the fully-warmed CPS is contained in the chart's source. -/
theorem chartPullbackStraightPathFullyWarmed_range_subset_source
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (p x : X) (r : ℝ) (hr_pos : 0 < r)
    (hr_subset : Metric.ball ((chartAt ℂ p) p) r ⊆ (chartAt ℂ p).target)
    (hx : (chartAt ℂ p) x ∈ Metric.ball ((chartAt ℂ p) p) r)
    (hx_source : x ∈ (chartAt ℂ p).source)
    (ε : ℝ) (hε : 0 < ε ∧ ε < 1/2) :
    Set.range (chartPullbackStraightPathFullyWarmed p x r hr_pos hr_subset hx hx_source ε hε) ⊆
      (chartAt ℂ p).source :=
  Set.Subset.trans
    (Path.smoothReparamConstantBoth_range_subset_range _ ε hε)
    (chartPullbackStraightPath_range_subset_source p x r hr_pos hr_subset hx hx_source)

/-- Chart-image of the fully-warmed CPS stays in the ball. -/
theorem chartPullbackStraightPathFullyWarmed_image_in_ball
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (p x : X) (r : ℝ) (hr_pos : 0 < r)
    (hr_subset : Metric.ball ((chartAt ℂ p) p) r ⊆ (chartAt ℂ p).target)
    (hx : (chartAt ℂ p) x ∈ Metric.ball ((chartAt ℂ p) p) r)
    (hx_source : x ∈ (chartAt ℂ p).source)
    (ε : ℝ) (hε : 0 < ε ∧ ε < 1/2) (t : unitInterval) :
    (chartAt ℂ p)
        (chartPullbackStraightPathFullyWarmed p x r hr_pos hr_subset hx hx_source ε hε t)
      ∈ Metric.ball ((chartAt ℂ p) p) r := by
  have h_range :
      (chartPullbackStraightPathFullyWarmed p x r hr_pos hr_subset hx hx_source ε hε) t ∈
        Set.range (chartPullbackStraightPath p x r hr_pos hr_subset hx hx_source) :=
    Path.smoothReparamConstantBoth_range_subset_range _ ε hε ⟨t, rfl⟩
  obtain ⟨y, hy⟩ := h_range
  rw [← hy]
  exact chartPullbackStraightPath_image_in_ball p x r hr_pos hr_subset hx hx_source y

/-- **Single-chart chart-`C¹` segment existence**. Given two points
`a, b ∈ (chartAt ℂ p).source` with chart-images both in a ball `r` around
`(chartAt ℂ p) p` (and the ball contained in `(chartAt ℂ p).target`),
there exists a chart-`C¹` path from `a` to `b` that is constantly `a` on
a small interval near `t = 0` AND constantly `b` on a small interval near
`t = 1`.

**Discharge — V→Λ trick** (Increment 8, sorry-free): the path goes `a → p → b`
via two existing `chartPullbackStraightPath` calls (one in each direction
from `p`), each `smoothReparamConstantBoth`'d for constant endpoints, then
trans'd via `trans_of_constant_join` (constant join at the shared point `p`).
The ball-coord hypotheses on `a` and `b` are exactly what
`chartPullbackStraightPath` requires for the path-source ↔ target distinction. -/
theorem exists_chartContDiffPath_in_chart
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (p a b : X) (r : ℝ) (hr_pos : 0 < r)
    (hr_subset : Metric.ball ((chartAt ℂ p) p) r ⊆ (chartAt ℂ p).target)
    (ha_source : a ∈ (chartAt ℂ p).source)
    (hb_source : b ∈ (chartAt ℂ p).source)
    (ha_ball : (chartAt ℂ p) a ∈ Metric.ball ((chartAt ℂ p) p) r)
    (hb_ball : (chartAt ℂ p) b ∈ Metric.ball ((chartAt ℂ p) p) r) :
    ∃ γ : Path a b, IsChartContDiffPath γ ∧
      (∃ ε > 0, ∀ t ∈ Set.Icc (0 : ℝ) ε, γ.extend t = a) ∧
      (∃ ε > 0, ∀ t ∈ Set.Icc (1 - ε) (1 : ℝ), γ.extend t = b) := by
  -- Two existing chartPullbackStraightPath calls (p → a and p → b).
  set γ_pa := JacobianChallenge.Periods.chartPullbackStraightPath p a r hr_pos hr_subset
    ha_ball ha_source with hγ_pa_def
  set γ_pb := JacobianChallenge.Periods.chartPullbackStraightPath p b r hr_pos hr_subset
    hb_ball hb_source with hγ_pb_def
  have hγ_pa_chartC1 : IsChartContDiffPath γ_pa :=
    JacobianChallenge.Periods.chartPullbackStraightPath_isChartContDiffPath
      p a r hr_pos hr_subset ha_ball ha_source
  have hγ_pb_chartC1 : IsChartContDiffPath γ_pb :=
    JacobianChallenge.Periods.chartPullbackStraightPath_isChartContDiffPath
      p b r hr_pos hr_subset hb_ball hb_source
  -- Reverse γ_pa to go a → p.
  set γ_ap : Path a p := γ_pa.symm with hγ_ap_def
  have hγ_ap_chartC1 : IsChartContDiffPath γ_ap := hγ_pa_chartC1.symm
  -- Apply smoothReparamConstantBoth (ε := 1/4).
  have hε : (0 : ℝ) < (1/4 : ℝ) ∧ (1/4 : ℝ) < 1/2 := ⟨by norm_num, by norm_num⟩
  set γ_ap_warm : Path a p := γ_ap.smoothReparamConstantBoth (1/4) hε with hγ_ap_warm_def
  set γ_pb_warm : Path p b := γ_pb.smoothReparamConstantBoth (1/4) hε with hγ_pb_warm_def
  have hγ_ap_warm_chartC1 : IsChartContDiffPath γ_ap_warm :=
    hγ_ap_chartC1.smoothReparamConstantBoth (1/4) hε
  have hγ_pb_warm_chartC1 : IsChartContDiffPath γ_pb_warm :=
    hγ_pb_chartC1.smoothReparamConstantBoth (1/4) hε
  -- Constant-tail of γ_ap_warm at p (= γ_ap.target).
  have h_ap_warm_tail : ∀ t ∈ Set.Icc (1 - 1/4 : ℝ) 1, γ_ap_warm.extend t = p := by
    intro t ⟨ht_lb, ht_ub⟩
    exact Path.smoothReparamConstantBoth_extend_eq_target γ_ap (1/4) hε t ht_lb ht_ub
  -- Constant-head of γ_pb_warm at p (= γ_pb.source).
  have h_pb_warm_head : ∀ t ∈ Set.Icc (0 : ℝ) (1/4), γ_pb_warm.extend t = p := by
    intro t ⟨ht_lb, ht_ub⟩
    exact Path.smoothReparamConstantBoth_extend_eq_source γ_pb (1/4) hε t ht_lb ht_ub
  -- Trans via trans_of_constant_join.
  set γ : Path a b := γ_ap_warm.trans γ_pb_warm with hγ_def
  have hγ_chartC1 : IsChartContDiffPath γ :=
    IsChartContDiffPath.trans_of_constant_join
      hγ_ap_warm_chartC1 hγ_pb_warm_chartC1
      (by norm_num : (0 : ℝ) < 1/4) (by norm_num : (1/4 : ℝ) ≤ 1) h_ap_warm_tail
      (by norm_num : (0 : ℝ) < 1/4) (by norm_num : (1/4 : ℝ) ≤ 1) h_pb_warm_head
  refine ⟨γ, hγ_chartC1, ?_, ?_⟩
  · -- Constant head at a on [0, 1/8]: γ.extend t = γ_ap_warm.extend(2t) (t ≤ 1/2), with
    -- 2t ∈ [0, 1/4], so γ_ap_warm.extend(2t) = a (constant head at γ_ap.source = a).
    refine ⟨1/8, by norm_num, ?_⟩
    intro t ⟨ht_lb, ht_ub⟩
    have ht_le_half : t ≤ 1/2 := by linarith
    have ht_unit : t ∈ unitInterval := ⟨ht_lb, by linarith⟩
    show γ.extend t = a
    rw [γ.extend_extends' ⟨t, ht_unit⟩]
    show (Path.trans γ_ap_warm γ_pb_warm).toFun ⟨t, ht_unit⟩ = a
    unfold Path.trans
    show (if t ≤ 1/2 then γ_ap_warm.extend (2 * t) else γ_pb_warm.extend (2 * t - 1)) = a
    rw [if_pos ht_le_half]
    exact Path.smoothReparamConstantBoth_extend_eq_source γ_ap (1/4) hε (2*t)
      (by linarith) (by linarith)
  · -- Constant tail at b on [1 - 1/8, 1]: γ.extend t = γ_pb_warm.extend(2t - 1) (t > 1/2), with
    -- 2t - 1 ∈ [1 - 1/4, 1], so γ_pb_warm.extend(2t - 1) = b (constant tail at γ_pb.target = b).
    refine ⟨1/8, by norm_num, ?_⟩
    intro t ⟨ht_lb, ht_ub⟩
    have ht_gt_half : 1/2 < t := by linarith
    have ht_unit : t ∈ unitInterval := ⟨by linarith, ht_ub⟩
    show γ.extend t = b
    rw [γ.extend_extends' ⟨t, ht_unit⟩]
    show (Path.trans γ_ap_warm γ_pb_warm).toFun ⟨t, ht_unit⟩ = b
    unfold Path.trans
    show (if t ≤ 1/2 then γ_ap_warm.extend (2 * t) else γ_pb_warm.extend (2 * t - 1)) = b
    rw [if_neg (not_le.mpr ht_gt_half)]
    exact Path.smoothReparamConstantBoth_extend_eq_target γ_pb (1/4) hε (2*t - 1)
      (by linarith) (by linarith)

/-- **Base chart-`C¹` existential.** Between any two points on a compact
connected smooth complex 1-manifold there exists a `Path` that is
`IsChartContDiffPath`.

Discharge body (Increment 7): chart-cover subdivision. Extract a continuous path
`γ₀` via `PathConnectedSpace.joined`, partition the unit interval into `n`
sub-intervals each mapping into a single chart (via `exists_uniform_chart_partition`),
build per-segment chart-`C¹` witnesses via `exists_chartContDiffPath_in_chart`,
and fold them together via `IsChartContDiffPath.trans_of_constant_join` using
`Nat.le_induction`.

The fold invariant maintains a constant-tail property on the accumulated path,
which is consumed at each fold step by `trans_of_constant_join`. -/
theorem exists_chartContDiffPath
    {X : Type} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (x₀ x : X) :
    ∃ γ : Path x₀ x, IsChartContDiffPath γ := by
  -- Step 1: topological path-connectedness gives a continuous `γ₀ : Path x₀ x`.
  haveI : LocPathConnectedSpace X :=
    ChartedSpace.locPathConnectedSpace (H := ℂ) (M := X)
  haveI : PathConnectedSpace X := pathConnectedSpace_iff_connectedSpace.mpr ‹_›
  let γ₀ : Path x₀ x := (PathConnectedSpace.joined x₀ x).somePath
  -- Step 2: refined Lebesgue-radius chart partition with chart-coord ball coverage.
  obtain ⟨n, hn, pickChart, radius, h_radius_pos, h_ball_subset, hcov⟩ :=
    JacobianChallenge.Periods.exists_uniform_chart_partition_with_ball γ₀.toContinuousMap
  -- Step 3: Build the fold via `Nat.le_induction`. Invariant:
  --   P(k) = there is an accumulated `Path x₀ (γ₀ (divFinIcc n hn k _))` that is
  --          `IsChartContDiffPath` AND constant on some `[1 - ε, 1]` at its endpoint.
  suffices fold : ∀ (k : ℕ) (hk : k ≤ n),
      ∃ (acc : Path x₀ (γ₀ (JacobianChallenge.Periods.divFinIcc n hn k hk))),
        JacobianChallenge.TraceDegree.IsChartContDiffPath acc ∧
        ∃ ε > 0, ε ≤ 1 ∧
          ∀ t ∈ Set.Icc (1 - ε) (1 : ℝ),
            acc.extend t = γ₀ (JacobianChallenge.Periods.divFinIcc n hn k hk) by
    -- Extract the witness at k = n, then cast endpoint to x.
    obtain ⟨acc_n, h_acc_n_chartC1, _⟩ := fold n (le_refl n)
    have h_target : x = γ₀ (JacobianChallenge.Periods.divFinIcc n hn n (le_refl n)) := by
      rw [JacobianChallenge.Periods.divFinIcc_self]; exact γ₀.target.symm
    exact ⟨acc_n.cast rfl h_target, h_acc_n_chartC1.cast rfl h_target⟩
  -- The fold induction itself. Use plain Nat induction; pass `k ≤ n` via the closure.
  intro k
  induction k with
  | zero =>
    intro _
    -- P(0): use Path.refl x₀ (cast to the right type).
    have h_src : γ₀ (JacobianChallenge.Periods.divFinIcc n hn 0 (Nat.zero_le n)) = x₀ := by
      rw [JacobianChallenge.Periods.divFinIcc_zero]; exact γ₀.source
    refine ⟨(Path.refl x₀).cast rfl h_src,
            (JacobianChallenge.TraceDegree.IsChartContDiffPath.refl x₀).cast rfl h_src,
            1, by norm_num, le_refl _, ?_⟩
    -- After cast, the extend is still constantly x₀ = γ₀(0).
    intro t _
    show ((Path.refl x₀).cast rfl h_src).extend t = _
    rw [Path.extend_cast]
    show (Path.refl x₀).extend t = γ₀ (JacobianChallenge.Periods.divFinIcc n hn 0 (Nat.zero_le n))
    rw [Path.refl_extend]
    exact h_src.symm
  | succ k ih =>
    intro hkn
    -- P(k+1): apply trans_of_constant_join with the IH and a per-segment δ_k.
    have hk_le_n : k ≤ n := Nat.le_of_succ_le hkn
    obtain ⟨acc_k, h_acc_k_chartC1, η_k, hη_k_pos, hη_k_le, h_acc_k_tail⟩ := ih hk_le_n
    -- Step 1: get the segment index `i : Fin n`.
    have hk_lt : k < n := Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hkn
    let i : Fin n := ⟨k, hk_lt⟩
    -- Step 2: extract the two endpoint memberships in chartAt ℂ (pickChart i).source.
    have hk_le : k ≤ n := le_of_lt hk_lt
    have hk1_le : k + 1 ≤ n := hkn
    have hn_pos : (0 : ℝ) < n := by exact_mod_cast hn
    have h_ival : (i : ℝ) = (k : ℝ) := by show ((⟨k, hk_lt⟩ : Fin n) : ℝ) = (k : ℝ); rfl
    have h_a_cov := hcov i (JacobianChallenge.Periods.divFinIcc n hn k hk_le)
      (by rw [JacobianChallenge.Periods.divFinIcc_val, h_ival])
      (by rw [JacobianChallenge.Periods.divFinIcc_val, h_ival,
              div_le_div_iff_of_pos_right hn_pos]; exact_mod_cast Nat.le_succ k)
    have h_b_cov := hcov i (JacobianChallenge.Periods.divFinIcc n hn (k+1) hk1_le)
      (by rw [JacobianChallenge.Periods.divFinIcc_val, h_ival,
              div_le_div_iff_of_pos_right hn_pos]; exact_mod_cast Nat.le_succ k)
      (by rw [JacobianChallenge.Periods.divFinIcc_val, h_ival]; push_cast; rfl)
    -- Step 3: get δ_k from the discharged `exists_chartContDiffPath_in_chart`.
    obtain ⟨δ_k, h_δ_k_chartC1, ⟨ε_head, hε_head_pos, h_δ_k_head⟩,
            ⟨ε_tail, hε_tail_pos, h_δ_k_tail⟩⟩ :=
      exists_chartContDiffPath_in_chart (pickChart i)
        (γ₀ (JacobianChallenge.Periods.divFinIcc n hn k hk_le))
        (γ₀ (JacobianChallenge.Periods.divFinIcc n hn (k+1) hk1_le))
        (radius i) (h_radius_pos i) (h_ball_subset i)
        h_a_cov.1 h_b_cov.1 h_a_cov.2 h_b_cov.2
    -- Step 4: cast acc_k's endpoint to match δ_k's source.
    have h_endpoint_eq :
        γ₀ (JacobianChallenge.Periods.divFinIcc n hn k hk_le) =
        γ₀ (JacobianChallenge.Periods.divFinIcc n hn k (Nat.le_of_succ_le hkn)) := rfl
    -- Step 5: build acc_{k+1} := acc_k.trans δ_k.
    let acc_new : Path x₀ (γ₀ (JacobianChallenge.Periods.divFinIcc n hn (k+1) hkn)) :=
      acc_k.trans δ_k
    -- Step 6: ε clamping for trans_of_constant_join.
    set εL : ℝ := min η_k 1 with hεL_def
    set εR : ℝ := min ε_head 1 with hεR_def
    have hεL_pos : 0 < εL := lt_min hη_k_pos (by norm_num : (0:ℝ) < 1)
    have hεL_le : εL ≤ 1 := min_le_right _ _
    have hεR_pos : 0 < εR := lt_min hε_head_pos (by norm_num : (0:ℝ) < 1)
    have hεR_le : εR ≤ 1 := min_le_right _ _
    have h_acc_k_tail' : ∀ t ∈ Set.Icc (1 - εL) (1 : ℝ),
        acc_k.extend t = γ₀ (JacobianChallenge.Periods.divFinIcc n hn k hk_le) := by
      intro t ⟨ht_lb, ht_ub⟩
      apply h_acc_k_tail t
      refine ⟨?_, ht_ub⟩
      have : εL ≤ η_k := min_le_left _ _
      linarith
    have h_δ_k_head' : ∀ t ∈ Set.Icc (0 : ℝ) εR,
        δ_k.extend t = γ₀ (JacobianChallenge.Periods.divFinIcc n hn k hk_le) := by
      intro t ⟨ht_lb, ht_ub⟩
      apply h_δ_k_head t
      refine ⟨ht_lb, ?_⟩
      have : εR ≤ ε_head := min_le_left _ _
      linarith
    have h_acc_new_chartC1 :
        JacobianChallenge.TraceDegree.IsChartContDiffPath acc_new :=
      JacobianChallenge.TraceDegree.IsChartContDiffPath.trans_of_constant_join
        h_acc_k_chartC1 h_δ_k_chartC1
        hεL_pos hεL_le h_acc_k_tail'
        hεR_pos hεR_le h_δ_k_head'
    -- Step 7: ε_tail clamping for the new constant-tail invariant.
    -- We need εT < 1 (strict) so that [1 - εT/2, 1] ⊆ (1/2, 1], avoiding the t = 1/2 boundary
    -- where the trans-formula switches branches.
    set εT : ℝ := min ε_tail (1/2 : ℝ) with hεT_def
    have hεT_pos : 0 < εT := lt_min hε_tail_pos (by norm_num : (0:ℝ) < 1/2)
    have hεT_le_half : εT ≤ 1/2 := min_le_right _ _
    have hεT_le_one : εT ≤ 1 := le_trans hεT_le_half (by norm_num)
    have h_acc_new_tail : ∀ t ∈ Set.Icc (1 - εT / 2) (1 : ℝ),
        acc_new.extend t = γ₀ (JacobianChallenge.Periods.divFinIcc n hn (k+1) hkn) := by
      intro t ⟨ht_lb, ht_ub⟩
      -- For t ∈ [1 - εT/2, 1] (and εT ≤ 1/2), 1/2 < t ≤ 1.
      have ht_ge_half : 1/2 < t := by
        have : εT / 2 < 1 / 2 := by linarith
        linarith
      have ht_unit : t ∈ unitInterval := ⟨by linarith, ht_ub⟩
      -- acc_new = acc_k.trans δ_k. Use Path.trans's extend formula.
      show acc_new.extend t = γ₀ (JacobianChallenge.Periods.divFinIcc n hn (k+1) hkn)
      have hext :
          (acc_k.trans δ_k).extend t = δ_k.extend (2 * t - 1) := by
        rw [(acc_k.trans δ_k).extend_extends' ⟨t, ht_unit⟩]
        show (Path.trans acc_k δ_k).toFun ⟨t, ht_unit⟩ = δ_k.extend (2*t - 1)
        unfold Path.trans
        show (if t ≤ 1/2 then acc_k.extend (2 * t) else δ_k.extend (2 * t - 1)) =
              δ_k.extend (2*t - 1)
        rw [if_neg (not_le.mpr ht_ge_half)]
      show (acc_k.trans δ_k).extend t = _
      rw [hext]
      -- Apply δ_k's constant tail: 2t - 1 ∈ [1 - ε_tail, 1].
      apply h_δ_k_tail
      refine ⟨?_, by linarith⟩
      have : εT ≤ ε_tail := min_le_left _ _
      linarith
    exact ⟨acc_new, h_acc_new_chartC1, εT / 2, by linarith, by linarith, h_acc_new_tail⟩

/-- **Strengthened existential**: chart-`C¹` path with a constant tail.

Discharge: take a base chart-`C¹` path `γ₀` from `exists_chartContDiffPath`,
reparametrize via `Path.smoothReparamConstantTail` with `ε = 1/2`. The
result is `IsChartContDiffPath` (preservation lemma) and is constantly
`x` on `[1/2, 1]` (by the reparam's extend formula on the tail). -/
theorem exists_chartContDiffPath_constantTail
    {X : Type} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (x₀ x : X) :
    ∃ γ : Path x₀ x, IsChartContDiffPath γ ∧
      ∃ ε > 0, ∀ t ∈ Set.Icc (1 - ε) (1 : ℝ), γ.extend t = x := by
  obtain ⟨γ₀, hγ₀⟩ := exists_chartContDiffPath x₀ x
  have hε : (0 : ℝ) < (1 / 2 : ℝ) ∧ (1 / 2 : ℝ) < 1 := ⟨by norm_num, by norm_num⟩
  refine ⟨γ₀.smoothReparamConstantTail (1 / 2) hε,
          hγ₀.smoothReparamConstantTail (1 / 2) hε,
          1 / 2, by norm_num, ?_⟩
  intro t ht
  obtain ⟨ht_lb, ht_ub⟩ := ht
  exact Path.smoothReparamConstantTail_extend_eq_target γ₀ (1 / 2) hε t ht_lb ht_ub

end JacobianChallenge.Periods
