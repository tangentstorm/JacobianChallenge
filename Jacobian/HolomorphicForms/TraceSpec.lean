import Jacobian.HolomorphicForms.Defs
import Jacobian.HolomorphicForms.ChartedSpaceComplexPoints
import Jacobian.HolomorphicForms.CompactRiemannSurface
import Jacobian.HolomorphicForms.SectionFiberNorm
import Jacobian.HolomorphicForms.HolomorphicMap
import Jacobian.HolomorphicForms.BranchedCover
import Jacobian.HolomorphicForms.ToFunApplyVec
import Jacobian.HolomorphicForms.PullbackBundled
import Jacobian.TraceDegree.TraceDefinition
import Jacobian.Periods.TrivializationContinuousLinearMapAt
import Jacobian.Blueprint.Sec02.BranchedDegreeFromHolomorphic
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Complex.CauchyIntegral

/-!
# Trace form specification interface

This file contains the minimal trace object and regular-value
specification needed by both the analytic degree API and the bundled
trace API.  It deliberately does not import `TraceDegree.AnalyticDegree`,
so the degree layer can package trace laws without creating an import
cycle.
-/

namespace JacobianChallenge.HolomorphicForms

open scoped Manifold ContDiff Topology Classical
open JacobianChallenge.HolomorphicForms
open JacobianChallenge.HolomorphicForms.SectionFiberNorm
open JacobianChallenge.Periods

variable {X Y : Type} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X]
  [IsManifold 𝓘(ℂ, ℂ) (⊤ : WithTop ℕ∞) X]
  [StableChartAt ℂ X]
variable {Y : Type} [TopologicalSpace Y] [T2Space Y] [CompactSpace Y]
  [ConnectedSpace Y] [ChartedSpace ℂ Y]
  [IsManifold 𝓘(ℂ, ℂ) (⊤ : WithTop ℕ∞) Y]
  [StableChartAt ℂ Y]

/--
**Trace construction data.** Packages the global bundled trace form
`traceForm` of a holomorphic 1-form `η` along a smooth map `f : X → Y`
between compact Riemann surfaces, together with the two specifications
that determine it:

* `regular_spec` — at every regular value of every compatible
  branched-cover datum, the global form agrees with the finite local
  fiber sum `traceAtRegularValue`;
* `map_zero_spec` — when the input form is zero, the global form is
  zero.

The analytic content of producing such data (holomorphic extension of
the finite local fiber sum across the finite branch locus, plus the
identification at the regular values) is supplied by the single narrow
construction provider `traceFormsConstructionData_provider`.
-/
structure TraceFormsConstructionData
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (⊤ : WithTop ℕ∞) f)
    (η : HolomorphicOneForm ℂ X) where
  /-- The global bundled trace form of `η` along `f`. -/
  traceForm : HolomorphicOneForm ℂ Y
  /--
At every regular value of any compatible branched-cover datum on
  `f`, the global form agrees with the finite local fiber sum.
-/
  regular_spec :
    ∀ (hbc : BranchedCoverData X Y f) (_hcompat : hbc.RamificationIndexCompatible)
      (y : Y) (hy : isRegularValue hbc y),
      traceForm.toFun y = traceAtRegularValue hbc (fun x => η.toFun x) y hy
  /-- The zero input form maps to the zero global form. -/
  map_zero_spec : η = 0 → traceForm = 0

omit [T2Space X] [CompactSpace X] [ConnectedSpace X] [StableChartAt ℂ X]
  [IsManifold 𝓘(ℂ, ℂ) ω X]
  [T2Space Y] [CompactSpace Y] [ConnectedSpace Y]
  [IsManifold 𝓘(ℂ, ℂ) ω Y] [StableChartAt ℂ Y] in

private theorem cotangentPushforward_zero
    (f : X → Y) (x : X) :
    cotangentPushforward f x (0 : CotangentSpace ℂ X x) = 0 := by
  unfold cotangentPushforward
  by_cases h : Nonempty (IsIso (mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) f x))
  · simp only [dif_pos h]
    exact ContinuousLinearMap.zero_comp _
  · simp only [dif_neg h]

omit [T2Space X] [CompactSpace X] [ConnectedSpace X] [StableChartAt ℂ X]
  [IsManifold 𝓘(ℂ, ℂ) ω X]
  [T2Space Y] [CompactSpace Y] [ConnectedSpace Y]
  [IsManifold 𝓘(ℂ, ℂ) ω Y] [StableChartAt ℂ Y] in

private theorem traceAtRegularValue_zero
    {f : X → Y} (hbc : BranchedCoverData X Y f)
    (y : Y) (hy : isRegularValue hbc y) :
    traceAtRegularValue hbc (fun _ : X => (0 : CotangentModelFiber ℂ)) y hy = 0 := by
  classical
  unfold traceAtRegularValue
  refine Finset.sum_eq_zero ?_
  rintro ⟨x, _⟩ _
  exact cotangentPushforward_zero f x

/--
**Construction data for the zero input form.** Fully proved.

When `η = 0`, the trace is the zero form on `Y`, and both fields are
immediate:

* `regular_spec` reduces every summand of the finite fiber sum to
  `cotangentPushforward f x 0 = 0`;
* `map_zero_spec` is `rfl` since the global form is already zero.

This is the strictly smaller "zero-input" leaf split out of the original
construction provider.
-/
private noncomputable def traceFormsConstructionData_zero
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (⊤ : WithTop ℕ∞) f) :
    TraceFormsConstructionData f hf (0 : HolomorphicOneForm ℂ X) where
  traceForm := 0
  regular_spec := by
    intro hbc _hcompat y hy
    -- LHS is (0 : HolomorphicOneForm ℂ Y).toFun y = 0
    -- RHS is traceAtRegularValue over (fun x => (0 : HolomorphicOneForm ℂ X).toFun x)
    have hzero_toFun : ∀ x : X, (0 : HolomorphicOneForm ℂ X).toFun x = 0 := by
      intro x
      change ((0 : HolomorphicOneForm ℂ X) : ∀ y, _) x = 0
      simp
    have hLHS : (0 : HolomorphicOneForm ℂ Y).toFun y = 0 := by
      change ((0 : HolomorphicOneForm ℂ Y) : ∀ y, _) y = 0
      simp
    rw [hLHS]
    have hcongr :
        (fun x : X => (0 : HolomorphicOneForm ℂ X).toFun x) =
          (fun _ : X => (0 : CotangentModelFiber ℂ)) := by
      funext x
      exact hzero_toFun x
    rw [hcongr]
    exact (traceAtRegularValue_zero hbc y hy).symm
  map_zero_spec _ := rfl

/--
**Construction data for a constant map.** Fully proved.

* If `y ≠ y₀`, then the fiber `f ⁻¹' {y}` is empty, so the finite local
  fiber sum is the empty sum, which is zero;
* If `y = y₀`, the existence of a `BranchedCoverData` at a regular
  value of a constant map contradicts perfectness of the target: by
  `hbc.local_bijective_unramified` at any unramified preimage `x`,
  there are open sets `U ⊆ X`, `V ⊆ Y` with `f` bijective from `U` to
  `V`. But for constant `f` this forces `V = {y₀}`, contradicting
  `IsOpen V` since the target charted ℂ-space `Y` is perfect (no
  isolated points).

This is the strictly smaller "constant-map" leaf split out of the
original construction provider.
-/
private noncomputable def traceFormsConstructionData_constant
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (⊤ : WithTop ℕ∞) f)
    (η : HolomorphicOneForm ℂ X) (hconst : ∃ y₀, ∀ x, f x = y₀)
    (hη : η ≠ 0) :
    TraceFormsConstructionData f hf η where
  traceForm := 0
  regular_spec := by
    classical
    intro hbc _hcompat y hy
    obtain ⟨y₀, hfy₀⟩ := hconst
    have hLHS : (0 : HolomorphicOneForm ℂ Y).toFun y = 0 := by
      change ((0 : HolomorphicOneForm ℂ Y) : ∀ y, _) y = 0
      simp
    rw [hLHS]
    -- Case split on y = y₀.
    by_cases hy_eq : y = y₀
    · -- y = y₀: derive contradiction via local_bijective_unramified.
      exfalso
      -- Pick any x : X (X is nonempty from ConnectedSpace).
      let x : X := Classical.arbitrary X
      have hx_fiber : x ∈ f ⁻¹' {y} := by
        show f x = y
        rw [hy_eq, hfy₀ x]
      have hx_ram : hbc.ramificationIndex x = 1 := hy x hx_fiber
      -- f x = y, so f x is in V; local bijection forces V = {y}.
      obtain ⟨U, V, hUopen, hVopen, hxU, hfxV, hbij⟩ :=
        hbc.local_bijective_unramified x hx_ram
      -- f '' U = V (BijOn) and f is constant equal to y on U.
      have hfU_eq : f '' U = {y} := by
        ext z
        constructor
        · rintro ⟨x', _, rfl⟩
          show f x' = y
          rw [hy_eq, hfy₀ x']
        · intro hz
          refine ⟨x, hxU, ?_⟩
          show f x = z
          rw [Set.mem_singleton_iff.mp hz, hy_eq, hfy₀ x]
      have hV_eq : V = ({y} : Set Y) := hbij.image_eq ▸ hfU_eq
      -- V open and V = {y}: singleton {y} would be open in Y.
      have hV_singleton_open : IsOpen ({y} : Set Y) := hV_eq ▸ hVopen
      -- But Y is perfect: no isolated points.
      rw [isOpen_singleton_iff_punctured_nhds] at hV_singleton_open
      haveI : Nontrivial Y := by
        obtain ⟨p, q, hpq⟩ := exists_two_distinct_points_of_chartedSpaceComplex (X := Y)
        exact ⟨⟨p, q, hpq⟩⟩
      haveI : PerfectSpace Y := inferInstance
      have hY_perfect : (𝓝[≠] y).NeBot := PerfectSpace.not_isolated y
      exact hY_perfect.ne hV_singleton_open
    · -- y ≠ y₀: the fiber is empty, so the sum is zero.
      have hfiber_empty : f ⁻¹' {y} = ∅ := by
        ext x
        simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_empty_iff_false,
          iff_false]
        intro hfx
        apply hy_eq
        rw [← hfx, hfy₀ x]
      show (0 : CotangentSpace ℂ Y y) =
        ((hbc.finite_fiber y).toFinset).attach.sum
          (fun x => cotangentPushforward f x.1 (η.toFun x.1))
      have htoFinset_empty : (hbc.finite_fiber y).toFinset = (∅ : Finset X) := by
        rw [Set.Finite.toFinset_eq_empty]
        exact hfiber_empty
      rw [htoFinset_empty, Finset.attach_empty, Finset.sum_empty]
  map_zero_spec h := absurd h hη

/- The target-side branch locus (image of ramification points) is finite. -/
omit [T2Space X] [CompactSpace X] [ConnectedSpace X] [ChartedSpace ℂ X]
  [IsManifold 𝓘(ℂ, ℂ) ω X] [StableChartAt ℂ X]
  [T2Space Y] [CompactSpace Y] [ConnectedSpace Y] [ChartedSpace ℂ Y]
  [IsManifold 𝓘(ℂ, ℂ) ω Y] [StableChartAt ℂ Y] in
theorem branchLocus_finite
    {f : X → Y} (h : BranchedCoverData X Y f) :
    {y : Y | ¬ isRegularValue h y}.Finite := by
  have hram : {x : X | h.ramificationIndex x ≠ 1}.Finite := h.ramified_finite
  have h_eq : {y : Y | ¬ isRegularValue h y} = f '' {x : X | h.ramificationIndex x ≠ 1} := by
    ext y; constructor
    · intro hy
      simp [isRegularValue] at hy
      obtain ⟨x, hx, hx_ram⟩ := hy
      exact ⟨x, hx_ram, hx⟩
    · rintro ⟨x, hx_ram, rfl⟩
      simp [isRegularValue]
      exact ⟨x, rfl, hx_ram⟩
  rw [h_eq]
  exact hram.image f

theorem dense_compl_of_finite_of_perfect
    {Z : Type*} [TopologicalSpace Z] [T1Space Z] [PerfectSpace Z]
    {s : Set Z} (hs : s.Finite) :
    Dense (sᶜ : Set Z) := by
  classical
  let F := hs.toFinset
  have hF : (F : Set Z) = s := hs.coe_toFinset
  rw [← hF]
  induction F using Finset.induction_on with
  | empty =>
      simp
  | insert a F _ha ih =>
      have hsingle : Dense ({a}ᶜ : Set Z) := dense_compl_singleton a
      have hFopen : IsOpen ((F : Set Z)ᶜ) := F.finite_toSet.isClosed.isOpen_compl
      have hinter : Dense ({a}ᶜ ∩ (F : Set Z)ᶜ : Set Z) :=
        hsingle.inter_of_isOpen_right ih hFopen
      have hset : (insert a (F : Set Z))ᶜ = ({a}ᶜ ∩ (F : Set Z)ᶜ : Set Z) := by
        ext z
        simp
      simpa [Finset.coe_insert, hset] using hinter

/- The regular locus is dense in Y. -/
omit [T2Space X] [CompactSpace X] [ConnectedSpace X] [ChartedSpace ℂ X]
  [IsManifold 𝓘(ℂ, ℂ) ω X] [StableChartAt ℂ X]
  [CompactSpace Y] [IsManifold 𝓘(ℂ, ℂ) ω Y] [StableChartAt ℂ Y] in
theorem regularLocus_dense
    {f : X → Y} (h : BranchedCoverData X Y f) :
    Dense (regularLocus h) := by
  haveI : Nontrivial Y := by
    obtain ⟨p, q, hpq⟩ := exists_two_distinct_points_of_chartedSpaceComplex (X := Y)
    exact ⟨⟨p, q, hpq⟩⟩
  haveI : PerfectSpace Y := inferInstance
  have hbranch : Dense ({y : Y | ¬ isRegularValue h y}ᶜ : Set Y) :=
    dense_compl_of_finite_of_perfect (branchLocus_finite h)
  simpa [regularLocus, Set.compl_setOf] using hbranch

/-!
### Trace-form holomorphic extension providers (Part A)

1. **holomorphicity on the regular locus** — already in the project
   as `localTraceAtRegularValue_holomorphic` (Provider 1);
2. **local boundedness near branch values** — the trace function is
   locally bounded near each branch value (Provider 2);
3. **generic removable singularity → global holomorphic section** —
   Riemann's removable singularity theorem, stated purely about
   `Y`-valued functions defined on a cofinite open set whose finite
   complement is the boundedness set (Provider 3);
4. **BCD-invariance of the local trace** — a set-theoretic fact that
   `traceAtRegularValue hbc … y …` depends only on `f, η, y` (not
   on the BCD chosen), via `Set.Finite.toFinset_inj` (Provider 4).
-/

omit [T2Space X] [CompactSpace X] [StableChartAt ℂ X]
  [T2Space Y] [CompactSpace Y] [ConnectedSpace Y] [StableChartAt ℂ Y] in
/--
**Provider (1).** *Trace holomorphic on the regular locus.* At
every regular value `y` of `hbc`, the local trace function
`localTraceAtRegularValue` (a chart-local realization of the finite
fibre sum, defined in a neighbourhood of `y`) is holomorphic at `y`.

Mathematically: at a regular value `y`, every preimage `x ∈ f⁻¹(y)`
is unramified, so `f` has a holomorphic local inverse near `y`, and
the cotangent pushforward of `η` along this inverse is locally
holomorphic. Summing finitely many holomorphic functions gives a
holomorphic function.
-/
theorem traceAtRegularValue_locally_holomorphic_on_regular_locus
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (⊤ : WithTop ℕ∞) f)
    (η : HolomorphicOneForm ℂ X)
    (hbc : BranchedCoverData X Y f)
    (hcompat : hbc.RamificationIndexCompatible)
    (y : Y) (hy : isRegularValue hbc y) :
    IsHolomorphicAt (localTraceAtRegularValue hbc
      (isHolomorphic_of_contMDiff hf
        (hasLocalKfoldRamification_of_contMDiff hf)) η y hy) y :=
  localTraceAtRegularValue_holomorphic hbc hcompat
    (isHolomorphic_of_contMDiff hf
      (hasLocalKfoldRamification_of_contMDiff hf)) η y hy

omit [T2Space X] [CompactSpace X] [IsManifold 𝓘(ℂ, ℂ) ω X] [StableChartAt ℂ X]
  [T2Space Y] [CompactSpace Y] [ConnectedSpace Y] [IsManifold 𝓘(ℂ, ℂ) ω Y]
  [StableChartAt ℂ Y] in
/--
**Local-inverse preimage of any nhd is a nhd.** The single
continuity-like consequence we need: for any open `W ∋ x`, the preimage
`(h.localInverseAt x hx) ⁻¹' W` is a `𝓝 (f x)`-set.

Proof sketch: the BCD's `localInverseAt` agrees on a neighborhood of `f x`
with an analytic local inverse `analyticInv` (constructed from the
analytic-inverse-function theorem applied to `chartLocalAt f x` whose
derivative at `chartAt ℂ x x` is nonzero because the ramification index
is 1). The analytic local inverse is genuinely continuous at `f x`
because it is the composition `(chartAt x).symm ∘ r ∘ chartAt(f x)`,
where `r` is analytic on a neighborhood of `chartAt(f x)(f x)`. By
combining the Tendsto from analytic continuity with the eventually-equality,
the preimage of any open `W ∋ x` is a neighborhood of `f x`.
-/
private theorem localInverseAt_preimage_mem_nhds
    {f : X → Y} (h : BranchedCoverData X Y f)
    (hcompat : h.RamificationIndexCompatible)
    (hHol : IsHolomorphic f)
    (x : X) (hx : h.ramificationIndex x = 1)
    {W : Set X} (hW_open : IsOpen W) (hxW : x ∈ W) :
    h.localInverseAt x hx ⁻¹' W ∈ 𝓝 (f x) := by
  classical
  obtain ⟨U, V, hUopen, hVopen, hxU, hfxV, hbij, _hright_branch, hleft_branch⟩ :=
    h.localInverse_is_inverse hx
  have hramAt : mapAnalyticOrderAt f x = 1 := by
    rw [← h.ramificationIndex_eq_mapAnalyticOrderAt hcompat (hHol.holomorphicAt x)]
    exact hx
  have hderiv : deriv (chartLocalAt f x) (chartAt ℂ x x) ≠ 0 := by
    have h_order : analyticOrderAt
        (fun t => chartLocalAt f x t - chartLocalAt f x (chartAt ℂ x x))
        (chartAt ℂ x x) = 1 := by
      convert hramAt using 1
      unfold mapAnalyticOrderAt
      simp +decide [analyticOrderNatAt]
    have h_deriv_an : AnalyticAt ℂ
        (fun t => chartLocalAt f x t - chartLocalAt f x (chartAt ℂ x x))
        (chartAt ℂ x x) :=
      (hHol.holomorphicAt x).sub analyticAt_const
    have h_deriv_order : analyticOrderAt
        (deriv (fun t => chartLocalAt f x t - chartLocalAt f x (chartAt ℂ x x)))
        (chartAt ℂ x x) = 0 := by
      have := AnalyticAt.analyticOrderAt_deriv_add_one h_deriv_an
      aesop
    rw [analyticOrderAt_eq_zero] at h_deriv_order
    rcases h_deriv_order with hzero | hnezero
    · exfalso; exact hzero (AnalyticAt.deriv h_deriv_an)
    · simpa [deriv_sub_const] using hnezero
  let analyticInv : Y → X := (hHol.holomorphicAt x).localInverse hderiv
  let F : ℂ → ℂ := chartLocalAt f x
  let z₀ : ℂ := chartAt ℂ x x
  let w₀ : ℂ := chartAt ℂ (f x) (f x)
  let r : ℂ → ℂ :=
    (hHol.holomorphicAt x).hasStrictDerivAt.localInverse F
      (deriv F z₀) z₀ hderiv
  have hFz₀ : F z₀ = w₀ := by simp [F, z₀, w₀]
  have hr_z₀ : r w₀ = z₀ := by
    dsimp [r]
    rw [← hFz₀]
    exact (HasStrictDerivAt.eventually_left_inverse
      (f := F) (f' := deriv F z₀) (a := z₀)
      (hf := (hHol.holomorphicAt x).hasStrictDerivAt) (hf' := hderiv)).self_of_nhds
  have hlocalInv_tendsto : Filter.Tendsto analyticInv (𝓝 (f x)) (𝓝 x) := by
    have hr_an : AnalyticAt ℂ r w₀ := by
      dsimp [r, F, z₀, w₀]
      simpa [F, z₀, w₀, hFz₀] using
        (hHol.holomorphicAt x).analyticAt_localInverse hderiv
    have hr_tendsto : Filter.Tendsto r (𝓝 w₀) (𝓝 z₀) := by
      simpa [ContinuousAt, hr_z₀] using hr_an.continuousAt
    have hchart_tendsto : Filter.Tendsto (fun y : Y => chartAt ℂ (f x) y)
        (𝓝 (f x)) (𝓝 w₀) := by
      simpa [w₀] using (chartAt ℂ (f x)).continuousAt (mem_chart_source ℂ (f x))
    have hsymm_tendsto : Filter.Tendsto (fun z => (chartAt ℂ x).symm z)
        (𝓝 z₀) (𝓝 x) := by
      have hcont := (chartAt ℂ x).continuousAt_symm
        ((chartAt ℂ x).map_source (mem_chart_source ℂ x))
      change Filter.Tendsto (fun z => (chartAt ℂ x).symm z) (𝓝 z₀)
        (𝓝 ((chartAt ℂ x).symm z₀)) at hcont
      simpa [z₀, (chartAt ℂ x).left_inv (mem_chart_source ℂ x)] using hcont
    have hcomp := hsymm_tendsto.comp (hr_tendsto.comp hchart_tendsto)
    simpa [analyticInv, IsHolomorphicAt.localInverse, r, F, z₀, w₀] using hcomp
  have hanalyticInv_mem_U : ∀ᶠ y in 𝓝 (f x), analyticInv y ∈ U :=
    hlocalInv_tendsto.eventually (hUopen.mem_nhds hxU)
  have hanalyticInv_right : ∀ᶠ y in 𝓝 (f x), f (analyticInv y) = y := by
    have hright_z : ∀ᶠ z in 𝓝 w₀, F (r z) = z := by
      dsimp [r]
      simpa [F, z₀, w₀, hFz₀] using
        (HasStrictDerivAt.eventually_right_inverse
          (f := F) (f' := deriv F z₀) (a := z₀)
          (hf := (hHol.holomorphicAt x).hasStrictDerivAt) (hf' := hderiv))
    have hchart_tendsto : Filter.Tendsto (fun y : Y => chartAt ℂ (f x) y)
        (𝓝 (f x)) (𝓝 w₀) := by
      simpa [w₀] using (chartAt ℂ (f x)).continuousAt (mem_chart_source ℂ (f x))
    have hright_y : ∀ᶠ y in 𝓝 (f x), F (r (chartAt ℂ (f x) y)) =
        chartAt ℂ (f x) y :=
      hchart_tendsto.eventually hright_z
    have hy_source : ∀ᶠ y in 𝓝 (f x), y ∈ (chartAt ℂ (f x)).source :=
      (chartAt ℂ (f x)).open_source.mem_nhds (mem_chart_source ℂ (f x))
    have hf_analyticInv_source : ∀ᶠ y in 𝓝 (f x),
        f (analyticInv y) ∈ (chartAt ℂ (f x)).source := by
      have htendsto : Filter.Tendsto (fun y => f (analyticInv y)) (𝓝 (f x)) (𝓝 (f x)) :=
        Filter.Tendsto.comp hHol.continuous.continuousAt hlocalInv_tendsto
      exact htendsto.eventually
        ((chartAt ℂ (f x)).open_source.mem_nhds (mem_chart_source ℂ (f x)))
    filter_upwards [hright_y, hy_source, hf_analyticInv_source] with y hy_eq hy_src hfy_src
    have hchart : chartAt ℂ (f x) (f (analyticInv y)) = chartAt ℂ (f x) y := by
      simpa [analyticInv, IsHolomorphicAt.localInverse, F, r, z₀, w₀] using hy_eq
    exact (chartAt ℂ (f x)).injOn hfy_src hy_src hchart
  have heq : ∀ᶠ y in 𝓝 (f x), analyticInv y = h.localInverseAt x hx y := by
    filter_upwards [hanalyticInv_mem_U, hanalyticInv_right] with y hy_an_U hy_an_right
    have hleft := hleft_branch (analyticInv y) hy_an_U
    rw [hy_an_right] at hleft
    exact hleft.symm
  have hW_nhd : W ∈ 𝓝 x := hW_open.mem_nhds hxW
  have hanalyticInv_in_W : ∀ᶠ y in 𝓝 (f x), analyticInv y ∈ W :=
    hlocalInv_tendsto.eventually hW_nhd
  filter_upwards [hanalyticInv_in_W, heq] with y hy_an_W hy_eq
  show h.localInverseAt x hx y ∈ W
  rw [← hy_eq]; exact hy_an_W

omit [T2Space Y] [CompactSpace Y] [ConnectedSpace Y]
  [IsManifold 𝓘(ℂ, ℂ) ω Y] [StableChartAt ℂ Y] in
/--
**Local helper: continuity from `IsHolomorphicAt` for maps into
`CotangentModelFiber ℂ`.** The chart on `CotangentModelFiber ℂ` is the
homeomorphism `cotangentFiberIso : (ℂ →L[ℂ] ℂ) ≃L[ℂ] ℂ`, with global
source. From `IsHolomorphicAt g p` (i.e. the chart-local pullback
`cotangentFiberIso ∘ g ∘ (chartAt ℂ p).symm` is analytic at
`chartAt ℂ p p`) we extract `ContinuousAt g p` by precomposing with
the continuous chart map at `p` and postcomposing with the continuous
inverse `cotangentFiberIso.symm`.
-/
private theorem IsHolomorphicAt.continuousAt_cotangentModelFiber
    {p : Y} {g : Y → CotangentModelFiber ℂ}
    (hg : IsHolomorphicAt g p) : ContinuousAt g p := by
  -- `chartLocalAt g p` is analytic, hence continuous, at `chartAt ℂ p p`.
  have h_chart_cont :
      ContinuousAt (chartLocalAt g p) (chartAt ℂ p p) :=
    hg.continuousAt
  -- `chartAt ℂ p` is continuous at `p` (chart source is a nhd).
  have h_chartAt_p_cont : ContinuousAt (chartAt ℂ p) p :=
    (chartAt ℂ p).continuousAt (mem_chart_source ℂ p)
  -- Composition: `chartLocalAt g p ∘ chartAt ℂ p` is continuous at `p`.
  have h_comp_cont :
      ContinuousAt (chartLocalAt g p ∘ chartAt ℂ p) p :=
    h_chart_cont.comp h_chartAt_p_cont
  -- On the chart source of `p`, this composition equals
  -- `cotangentFiberIso ∘ g`.
  have h_source_nhd : (chartAt ℂ p).source ∈ 𝓝 p :=
    (chartAt ℂ p).open_source.mem_nhds (mem_chart_source ℂ p)
  have h_eventually_eq :
      ∀ᶠ q in 𝓝 p,
        (chartLocalAt g p ∘ chartAt ℂ p) q = cotangentFiberIso (g q) := by
    filter_upwards [h_source_nhd] with q hq
    -- chartLocalAt g p = chartAt ℂ (g p) ∘ g ∘ (chartAt ℂ p).symm
    -- evaluated at chartAt ℂ p q.
    -- (chartAt ℂ p).symm (chartAt ℂ p q) = q since q in source.
    show chartAt ℂ (g p) (g ((chartAt ℂ p).symm (chartAt ℂ p q))) =
      cotangentFiberIso (g q)
    rw [(chartAt ℂ p).left_inv hq]
    -- chartAt ℂ (g p) on CotangentModelFiber ℂ is cotangentFiberIso.
    rfl
  -- Conclude `cotangentFiberIso ∘ g` is continuous at `p`.
  have h_iso_g_cont : ContinuousAt (fun q => cotangentFiberIso (g q)) p :=
    h_comp_cont.congr h_eventually_eq
  -- `cotangentFiberIso.symm` is continuous on `CotangentModelFiber ℂ`.
  have h_symm_cont :
      Continuous (fun w : ℂ => cotangentFiberIso.symm w) :=
    cotangentFiberIso.symm.continuous
  -- Compose: `cotangentFiberIso.symm ∘ cotangentFiberIso ∘ g = g`.
  have h_back :
      ContinuousAt
        (fun q => cotangentFiberIso.symm (cotangentFiberIso (g q))) p :=
    h_symm_cont.continuousAt.comp h_iso_g_cont
  -- Simplify using `cotangentFiberIso.symm_apply_apply`.
  have h_eq : (fun q => cotangentFiberIso.symm (cotangentFiberIso (g q))) = g := by
    funext q
    exact cotangentFiberIso.symm_apply_apply (g q)
  rw [h_eq] at h_back
  exact h_back

omit [T2Space X] [CompactSpace X] [StableChartAt ℂ X]
  [T2Space Y] [CompactSpace Y] [ConnectedSpace Y] [StableChartAt ℂ Y] in
/--
**Strictly narrower fiber-point helper (Provider 2 internal),
unramified leaf.** When `x₀` is unramified (ramification index 1),
the local inverse of `f` near `x₀` makes the partial sum over
preimages of `y` in `W₀ ∩ U₀` a single term, equal to the
holomorphic function `localPullbackAt hbc hHol η x₀ hx₀_ram y`.
Boundedness on a small `Y`-nhd of `y₀` follows from
continuity at `y₀`.
-/
private theorem unramifiedFiberPoint_partialTrace_locally_bounded
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (⊤ : WithTop ℕ∞) f)
    (η : HolomorphicOneForm ℂ X)
    (hbc : BranchedCoverData X Y f)
    (hcompat : hbc.RamificationIndexCompatible)
    (y₀ : Y) (x₀ : X) (hx₀_fiber : f x₀ = y₀)
    (hx₀_ram : hbc.ramificationIndex x₀ = 1)
    (W₀ : Set X) (hW₀_open : IsOpen W₀) (hxW₀ : x₀ ∈ W₀) :
    ∃ (V : Set Y) (W : Set X) (M : ℝ),
      IsOpen V ∧ y₀ ∈ V ∧ IsOpen W ∧ x₀ ∈ W ∧ W ⊆ W₀ ∧
      ∀ y ∈ V, ∀ (hy : isRegularValue hbc y),
        ‖((((hbc.finite_fiber y).toFinset.filter (· ∈ W)).attach.sum
            (fun x => (cotangentPushforward f x.1 (η.toFun x.1) :
              CotangentModelFiber ℂ)) : CotangentModelFiber ℂ))‖ ≤ M := by
  classical
  have hHol : IsHolomorphic f :=
    isHolomorphic_of_contMDiff hf (hasLocalKfoldRamification_of_contMDiff hf)
  -- Step 1: extract local bijection (U₀, V₀).
  obtain ⟨U₀, V₀, hU₀_open, hV₀_open, hxU₀, hfxV₀, hbij, hright, hleft⟩ :=
    hbc.localInverse_is_inverse hx₀_ram
  -- Step 2: W := W₀ ∩ U₀: open, x₀ ∈ W, W ⊆ W₀ and W ⊆ U₀.
  set W : Set X := W₀ ∩ U₀ with hW_def
  have hW_open : IsOpen W := hW₀_open.inter hU₀_open
  have hxW : x₀ ∈ W := ⟨hxW₀, hxU₀⟩
  have hW_sub_W₀ : W ⊆ W₀ := fun _ h => h.1
  have hW_sub_U₀ : W ⊆ U₀ := fun _ h => h.2
  -- Step 3: localInverseAt preimage of W is a Y-nhd of f x₀ = y₀.
  have hWpre_nhd : hbc.localInverseAt x₀ hx₀_ram ⁻¹' W ∈ 𝓝 (f x₀) :=
    localInverseAt_preimage_mem_nhds hbc hcompat hHol x₀ hx₀_ram hW_open hxW
  obtain ⟨V₁, hV₁_sub, hV₁_open, hV₁_mem⟩ := mem_nhds_iff.mp hWpre_nhd
  -- V₁ is open Y-set, f x₀ ∈ V₁, V₁ ⊆ preimage of W.
  -- Step 4: the localPullbackAt is continuous at y₀ = f x₀.
  have h_pullbackHol : IsHolomorphicAt
      (localPullbackAt hbc hHol η x₀ hx₀_ram) (f x₀) :=
    localPullbackAt_holomorphic hbc hcompat hHol η x₀ hx₀_ram
  have h_pullbackCont : ContinuousAt
      (localPullbackAt hbc hHol η x₀ hx₀_ram) (f x₀) :=
    h_pullbackHol.continuousAt_cotangentModelFiber
  -- Step 5: define M as ‖value at y₀‖ + 1 and extract bound.
  set M : ℝ := ‖localPullbackAt hbc hHol η x₀ hx₀_ram (f x₀)‖ + 1 with hM_def
  have hM_nhd : ∀ᶠ y in 𝓝 (f x₀),
      ‖localPullbackAt hbc hHol η x₀ hx₀_ram y‖ ≤ M := by
    have h_norm_cont : ContinuousAt
        (fun y => ‖localPullbackAt hbc hHol η x₀ hx₀_ram y‖) (f x₀) :=
      continuous_norm.continuousAt.comp h_pullbackCont
    have h_lt : (fun y => ‖localPullbackAt hbc hHol η x₀ hx₀_ram y‖) (f x₀) < M := by
      simp [hM_def]
    exact h_norm_cont.eventually_lt_const h_lt |>.mono (fun y => le_of_lt)
  obtain ⟨V₂, hV₂_sub, hV₂_open, hV₂_mem⟩ := mem_nhds_iff.mp hM_nhd
  -- Step 6: assemble V := V₀ ∩ V₁ ∩ V₂.
  set V : Set Y := V₀ ∩ V₁ ∩ V₂ with hV_def
  have hV_open : IsOpen V := (hV₀_open.inter hV₁_open).inter hV₂_open
  have hy₀_V : y₀ ∈ V := by
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [← hx₀_fiber]; exact hfxV₀
    · rw [← hx₀_fiber]; exact hV₁_mem
    · rw [← hx₀_fiber]; exact hV₂_mem
  refine ⟨V, W, M, hV_open, hy₀_V, hW_open, hxW, hW_sub_W₀, ?_⟩
  intro y hy_V hy_reg
  -- The single-summand reduction: T.filter (· ∈ W) = {localInverseAt x₀ hx₀_ram y}.
  set T : Finset X := (hbc.finite_fiber y).toFinset with hT_def
  set xy : X := hbc.localInverseAt x₀ hx₀_ram y with hxy_def
  have hy_V₀ : y ∈ V₀ := hy_V.1.1
  have hy_V₁ : y ∈ V₁ := hy_V.1.2
  have hy_V₂ : y ∈ V₂ := hy_V.2
  -- f xy = y (since y ∈ V₀ and `hright`).
  have hfxy : f xy = y := hright y hy_V₀
  -- xy ∈ W (since y ∈ V₁ ⊆ preimage of W).
  have hxyW : xy ∈ W := hV₁_sub hy_V₁
  -- xy ∈ T (since f xy = y means xy ∈ f ⁻¹' {y}).
  have hxyT : xy ∈ T := by
    rw [hT_def, Set.Finite.mem_toFinset]
    exact hfxy
  -- T.filter (· ∈ W) = {xy} as a Finset.
  have hfilter_eq : T.filter (· ∈ W) = ({xy} : Finset X) := by
    apply Finset.ext
    intro x'
    simp only [Finset.mem_filter, Finset.mem_singleton]
    constructor
    · rintro ⟨hx'T, hx'W⟩
      have hfx' : f x' = y := by
        rw [hT_def, Set.Finite.mem_toFinset] at hx'T
        exact hx'T
      have hx'U₀ : x' ∈ U₀ := hW_sub_U₀ hx'W
      have hLI : hbc.localInverseAt x₀ hx₀_ram (f x') = x' := hleft x' hx'U₀
      rw [hfx'] at hLI
      exact hLI.symm
    · intro hx'_eq
      refine ⟨?_, ?_⟩
      · rw [hx'_eq]; exact hxyT
      · rw [hx'_eq]; exact hxyW
  -- Compute the sum: it's a single summand, equal to
  -- localPullbackAt h hHol η x₀ hx₀_ram y.
  have hM_bound : ‖localPullbackAt hbc hHol η x₀ hx₀_ram y‖ ≤ M :=
    hV₂_sub hy_V₂
  -- Type-stable summand using CotangentModelFiber ℂ (avoid dependent types).
  let v : X → CotangentModelFiber ℂ := fun x =>
    cotangentPushforward f x (η.toFun x)
  -- The v-sum equals localPullbackAt.
  have hv_sum_eq :
      ((T.filter (· ∈ W)).attach.sum (fun x => v x.1) :
        CotangentModelFiber ℂ) =
        localPullbackAt hbc hHol η x₀ hx₀_ram y := by
    rw [show (T.filter (· ∈ W)).attach.sum (fun x => v x.1) =
          (T.filter (· ∈ W)).sum v from Finset.sum_attach _ v]
    rw [hfilter_eq, Finset.sum_singleton]
    rfl
  have hbound_v : ‖((T.filter (· ∈ W)).attach.sum (fun x => v x.1) :
        CotangentModelFiber ℂ)‖ ≤ M :=
    (congrArg norm hv_sum_eq).le.trans hM_bound
  -- Convert the goal to the v-sum form.
  convert hbound_v

/--
**Pure `k`-element-sum boundedness helper for the ramified leaf.**

Given the kfold-ramification chart-local data (a chart-nhd `U_kfold`
of `x₀` and Y-nhd `V_kfold` of `y₀` such that every `y ∈ V_kfold`
with `y ≠ y₀` has a Finset `s_y` of exactly `k` unramified
preimages of `y` in `U_kfold`, exhausting all preimages of `y` in
`U_kfold`), this provides an open `Y`-nhd `V`, an open `X`-nhd
`W ⊆ W₀ ∩ U_kfold` of `x₀`, and a uniform bound `M` on the partial
sum over preimages in `W` for regular `y ∈ V, y ≠ y₀`.

The hypothesis explicitly carries the kfold-ramification structure,
making the obligation strictly chart-local: it only depends on the
kfold chart data and the input form `η`, not on the global properties
of `f` or `hbc`.

This is the genuinely deep roots-of-unity cancellation step. The
chart-local form `w = z^k + …` makes the `k` preimages
`z_j ≈ w^{1/k} ζ^j` (with `ζ = e^{2πi/k}`), each contributing a
cotangent pushforward whose leading term has fractional `w`-power
`w^{(1-k)/k}` that individually blows up as `y → y₀`. Summing over
the `k` preimages cancels these fractional powers (roots-of-unity
summing to 0 except in multiples of `k`), leaving a clean power
series in `w` whose leading coefficient provides the bound.

This is the sole remaining sorry for the ramified leaf, isolated
as a single chart-local analytic statement.
-/
private theorem ramifiedKfoldSum_locally_bounded
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (⊤ : WithTop ℕ∞) f)
    (η : HolomorphicOneForm ℂ X)
    (hbc : BranchedCoverData X Y f)
    (hcompat : hbc.RamificationIndexCompatible)
    (y₀ : Y) (x₀ : X) (hx₀_fiber : f x₀ = y₀)
    (k : ℕ) (hk_pos : 0 < k) (hk_ram : k = hbc.ramificationIndex x₀)
    (U_kfold : Set X) (hU_kfold_open : IsOpen U_kfold) (hxU_kfold : x₀ ∈ U_kfold)
    (V_kfold : Set Y) (hV_kfold_open : IsOpen V_kfold) (hy₀V_kfold : y₀ ∈ V_kfold)
    (h_kfold_data : ∀ y ∈ V_kfold, y ≠ y₀ →
      ∃ s : Finset X, s.card = k ∧ (↑s : Set X) ⊆ U_kfold ∧
        (∀ x' ∈ s, f x' = y ∧ hbc.ramificationIndex x' = 1) ∧
        (∀ x' ∈ U_kfold, f x' = y → x' ∈ s))
    (W₀ : Set X) (hW₀_open : IsOpen W₀) (hxW₀ : x₀ ∈ W₀) :
    ∃ (V : Set Y) (W : Set X) (M : ℝ),
      IsOpen V ∧ y₀ ∈ V ∧ IsOpen W ∧ x₀ ∈ W ∧ W ⊆ W₀ ∧
      ∀ y ∈ V, y ≠ y₀ → ∀ (hy : isRegularValue hbc y),
        ‖((((hbc.finite_fiber y).toFinset.filter (· ∈ W)).attach.sum
            (fun x => (cotangentPushforward f x.1 (η.toFun x.1) :
              CotangentModelFiber ℂ)) : CotangentModelFiber ℂ))‖ ≤ M := by
  sorry

/--
**Strictly narrower fiber-point helper (Provider 2 internal),
ramified leaf, `y ≠ y₀` case.** When `x₀` is ramified of index
`n ≥ 2`, the local coordinate form `w = z^n + …` makes the `n`
cotangent pushforwards at the preimages of `y` near `y₀ = f x₀` have
leading terms with fractional `w`-powers `w^{(1-n)/n}` that
individually blow up. The sum over the `n` roots-of-unity preimages
cancels these fractional powers, leaving a clean power series in
`w` whose leading coefficient provides a chart-local bound.

The hypothesis `y ≠ y₀` is essential: at `y = y₀ = f x₀`, the
preimages collapse to `x₀` itself (no `n`-fold splitting), and the
sum is not given by the same formula. (The `y = y₀` case is
vacuous in the broader `ramifiedFiberPoint_partialTrace_locally_bounded`
because `y₀` is not a regular value when `x₀` is ramified.)

This is now a sorry-free reduction to the strictly narrower
`ramifiedKfoldSum_locally_bounded`: apply `local_kfold_ramified` to
identify the partial sum over preimages in `W₀ ∩ U_kfold` with the
`k`-element Finset of unramified preimages of `y` produced by the
kfold structure, then delegate the pure boundedness obligation.
-/
private theorem ramifiedNonY₀FiberPoint_partialTrace_locally_bounded
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (⊤ : WithTop ℕ∞) f)
    (η : HolomorphicOneForm ℂ X)
    (hbc : BranchedCoverData X Y f)
    (hcompat : hbc.RamificationIndexCompatible)
    (y₀ : Y) (x₀ : X) (hx₀_fiber : f x₀ = y₀)
    (hx₀_ram : hbc.ramificationIndex x₀ ≠ 1)
    (W₀ : Set X) (hW₀_open : IsOpen W₀) (hxW₀ : x₀ ∈ W₀) :
    ∃ (V : Set Y) (W : Set X) (M : ℝ),
      IsOpen V ∧ y₀ ∈ V ∧ IsOpen W ∧ x₀ ∈ W ∧ W ⊆ W₀ ∧
      ∀ y ∈ V, y ≠ y₀ → ∀ (hy : isRegularValue hbc y),
        ‖((((hbc.finite_fiber y).toFinset.filter (· ∈ W)).attach.sum
            (fun x => (cotangentPushforward f x.1 (η.toFun x.1) :
              CotangentModelFiber ℂ)) : CotangentModelFiber ℂ))‖ ≤ M := by
  -- Extract the kfold-ramification structure at x₀ from IsHolomorphic.
  have hHol : IsHolomorphic f :=
    isHolomorphic_of_contMDiff hf (hasLocalKfoldRamification_of_contMDiff hf)
  let k : ℕ := hbc.ramificationIndex x₀
  have hk_pos : 0 < k := hbc.ramificationIndex_pos x₀
  have hk_ram_eq : k = mapAnalyticOrderAt f x₀ :=
    hbc.ramificationIndex_eq_mapAnalyticOrderAt hcompat (hHol.holomorphicAt x₀)
  obtain ⟨U_kfold, hU_kfold_open, hxU_kfold, V_kfold, hV_kfold_open,
    hfxV_kfold, h_kfold_raw⟩ :=
    hHol.local_kfold_ramified hk_pos hk_ram_eq.symm
  have hy₀V_kfold : y₀ ∈ V_kfold := hx₀_fiber ▸ hfxV_kfold
  -- Convert mapAnalyticOrderAt-typed kfold_data to hbc.ramificationIndex-typed.
  have h_kfold_data : ∀ y ∈ V_kfold, y ≠ y₀ →
      ∃ s : Finset X, s.card = k ∧ (↑s : Set X) ⊆ U_kfold ∧
        (∀ x' ∈ s, f x' = y ∧ hbc.ramificationIndex x' = 1) ∧
        (∀ x' ∈ U_kfold, f x' = y → x' ∈ s) := by
    intro y hyV hyne
    have hyne' : y ≠ f x₀ := by rw [hx₀_fiber]; exact hyne
    obtain ⟨s, hs_card, hs_sub, hs_data, hs_exhaust⟩ :=
      h_kfold_raw y hyV hyne'
    refine ⟨s, hs_card, hs_sub, ?_, hs_exhaust⟩
    intro x' hx's
    refine ⟨(hs_data x' hx's).1, ?_⟩
    -- mapAnalyticOrderAt f x' = 1 ⇒ ramificationIndex x' = 1.
    have hx'_hol : IsHolomorphicAt f x' := hHol.holomorphicAt x'
    rw [hbc.ramificationIndex_eq_mapAnalyticOrderAt hcompat hx'_hol]
    exact (hs_data x' hx's).2
  -- Apply the kfold-sum bound helper.
  exact ramifiedKfoldSum_locally_bounded f hf η hbc hcompat y₀ x₀ hx₀_fiber
    k hk_pos rfl U_kfold hU_kfold_open hxU_kfold V_kfold hV_kfold_open
    hy₀V_kfold h_kfold_data W₀ hW₀_open hxW₀

/--
**Strictly narrower fiber-point helper (Provider 2 internal),
ramified leaf, dispatcher.** Refines the `ramifiedNonY₀` narrower
helper to the broader signature accepted by
`fiberPoint_partialTrace_locally_bounded`'s dispatcher. The case
`y = y₀` is vacuous: if `y` were regular and equal to `y₀ = f x₀`,
then by `isRegularValue` we'd get `hbc.ramificationIndex x₀ = 1`,
contradicting `hx₀_ram`. The case `y ≠ y₀` is delegated to
`ramifiedNonY₀FiberPoint_partialTrace_locally_bounded`.

Sorry-free.
-/
private theorem ramifiedFiberPoint_partialTrace_locally_bounded
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (⊤ : WithTop ℕ∞) f)
    (η : HolomorphicOneForm ℂ X)
    (hbc : BranchedCoverData X Y f)
    (hcompat : hbc.RamificationIndexCompatible)
    (y₀ : Y) (x₀ : X) (hx₀_fiber : f x₀ = y₀)
    (hx₀_ram : hbc.ramificationIndex x₀ ≠ 1)
    (W₀ : Set X) (hW₀_open : IsOpen W₀) (hxW₀ : x₀ ∈ W₀) :
    ∃ (V : Set Y) (W : Set X) (M : ℝ),
      IsOpen V ∧ y₀ ∈ V ∧ IsOpen W ∧ x₀ ∈ W ∧ W ⊆ W₀ ∧
      ∀ y ∈ V, ∀ (hy : isRegularValue hbc y),
        ‖((((hbc.finite_fiber y).toFinset.filter (· ∈ W)).attach.sum
            (fun x => (cotangentPushforward f x.1 (η.toFun x.1) :
              CotangentModelFiber ℂ)) : CotangentModelFiber ℂ))‖ ≤ M := by
  obtain ⟨V', W', M', hV'_open, hy₀_V', hW'_open, hxW', hW'_sub, hbound'⟩ :=
    ramifiedNonY₀FiberPoint_partialTrace_locally_bounded f hf η hbc hcompat
      y₀ x₀ hx₀_fiber hx₀_ram W₀ hW₀_open hxW₀
  refine ⟨V', W', M', hV'_open, hy₀_V', hW'_open, hxW', hW'_sub, ?_⟩
  intro y hy_V hy_reg
  by_cases hy_eq : y = y₀
  · -- `y = y₀`: regularity contradicts ramification of x₀.
    exfalso
    apply hx₀_ram
    have hx₀_fib_y : x₀ ∈ f ⁻¹' {y} := by
      rw [Set.mem_preimage, Set.mem_singleton_iff, hx₀_fiber, hy_eq]
    exact hy_reg x₀ hx₀_fib_y
  · -- `y ≠ y₀`: delegate to the narrower helper.
    exact hbound' y hy_V hy_eq hy_reg

/--
**Strictly narrower fiber-point helper (Provider 2 internal),
dispatcher.** Branches on whether `x₀` is unramified or ramified
and delegates to the appropriate leaf. Sorry-free.
-/
private theorem fiberPoint_partialTrace_locally_bounded
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (⊤ : WithTop ℕ∞) f)
    (η : HolomorphicOneForm ℂ X)
    (hbc : BranchedCoverData X Y f)
    (hcompat : hbc.RamificationIndexCompatible)
    (y₀ : Y) (x₀ : X) (hx₀_fiber : f x₀ = y₀)
    (W₀ : Set X) (hW₀_open : IsOpen W₀) (hxW₀ : x₀ ∈ W₀) :
    ∃ (V : Set Y) (W : Set X) (M : ℝ),
      IsOpen V ∧ y₀ ∈ V ∧ IsOpen W ∧ x₀ ∈ W ∧ W ⊆ W₀ ∧
      ∀ y ∈ V, ∀ (hy : isRegularValue hbc y),
        ‖((((hbc.finite_fiber y).toFinset.filter (· ∈ W)).attach.sum
            (fun x => (cotangentPushforward f x.1 (η.toFun x.1) :
              CotangentModelFiber ℂ)) : CotangentModelFiber ℂ))‖ ≤ M := by
  by_cases hx₀_ram : hbc.ramificationIndex x₀ = 1
  · exact unramifiedFiberPoint_partialTrace_locally_bounded f hf η hbc hcompat
      y₀ x₀ hx₀_fiber hx₀_ram W₀ hW₀_open hxW₀
  · exact ramifiedFiberPoint_partialTrace_locally_bounded f hf η hbc hcompat
      y₀ x₀ hx₀_fiber hx₀_ram W₀ hW₀_open hxW₀

/--
**Provider (2).** *Trace locally bounded near branch values.* At
every branch value `y₀` (a non-regular value) of `hbc`, there is a
neighbourhood of `y₀` and a real bound `M` such that the
chart-local finite-fibre sum is bounded by `M` on the neighbourhood
(intersected with the regular locus).

Mathematically: in a chart-local neighbourhood of a branch value
`y₀`, the preimage `f⁻¹(y₀)` is a finite set; each unramified
preimage contributes a locally bounded (in fact holomorphic) term;
each ramified preimage contributes a term whose chart-local
expansion has the form of a holomorphic 1-form pulled back through
a finite-order branched cover, which is bounded because the input
`η` is holomorphic (not meromorphic). The ramified-preimage
contribution is `0` because the cotangent pushforward at a ramified
point is `0` (the `mfderiv` is not an isomorphism there).

This is now a sorry-free combinatorial assembly of the strictly
narrower per-fiber-point helper
`fiberPoint_partialTrace_locally_bounded`: separate the finite fiber
`f⁻¹{y₀}` by T2 disjoint open nhds, apply the helper at each fiber
point, then assemble via `eventually_fiber_subset_of_compact_T2`
(properness of `f` on the compact source forces nearby fibers to lie
in the union of these chart-neighbourhoods, so the regular-value
trace decomposes as a finite disjoint sum of partial-sum
contributions each bounded by the helper).

The hypotheses are exactly the inputs consumed by Provider (3),
plus `hcompat`, which is already in scope at the unique call site
(`traceForm_extension_per_BCD`).
-/
theorem traceAtRegularValue_locally_bounded_near_branch_values
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (⊤ : WithTop ℕ∞) f)
    (η : HolomorphicOneForm ℂ X)
    (hbc : BranchedCoverData X Y f)
    (hcompat : hbc.RamificationIndexCompatible)
    (y₀ : Y) (_hy₀ : ¬ isRegularValue hbc y₀) :
    ∃ (U : Set Y) (M : ℝ), IsOpen U ∧ y₀ ∈ U ∧
      ∀ y ∈ U, ∀ hy : isRegularValue hbc y,
        ‖traceAtRegularValue hbc (fun x => η.toFun x) y hy‖ ≤ M := by
  classical
  set S : Finset X := (hbc.finite_fiber y₀).toFinset with hS_def
  have hfiber_eq : ∀ {x : X}, x ∈ S ↔ x ∈ f ⁻¹' {y₀} := by
    intro x; rw [hS_def, Set.Finite.mem_toFinset]
  have hHol : IsHolomorphic f :=
    isHolomorphic_of_contMDiff hf (hasLocalKfoldRamification_of_contMDiff hf)
  -- T2 separation: pairwise disjoint open nhds of points in S.
  have hS_fin : (S : Set X).Finite := S.finite_toSet
  obtain ⟨W₀, hW₀_local, hW₀_disj⟩ := hS_fin.exists_pairwiseDisjoint_open_nhds
  -- For each x ∈ S, apply the per-fiber-point helper.
  have hper_x : ∀ x ∈ S, ∃ (V_x : Set Y) (W_x : Set X) (M_x : ℝ),
      IsOpen V_x ∧ y₀ ∈ V_x ∧ IsOpen W_x ∧ x ∈ W_x ∧ W_x ⊆ W₀ x ∧
      ∀ y ∈ V_x, ∀ (hy : isRegularValue hbc y),
        ‖((((hbc.finite_fiber y).toFinset.filter (· ∈ W_x)).attach.sum
            (fun x' => (cotangentPushforward f x'.1 (η.toFun x'.1) :
              CotangentModelFiber ℂ)) : CotangentModelFiber ℂ))‖ ≤ M_x := by
    intro x hxS
    have hx_fiber : f x = y₀ := (hfiber_eq.mp hxS)
    exact fiberPoint_partialTrace_locally_bounded f hf η hbc hcompat y₀ x hx_fiber
      (W₀ x) (hW₀_local x hxS).1 (hW₀_local x hxS).2
  -- Choose V_x, W_x, M_x using `choose`.
  choose! V_x W_x M_x hV_x_open hy₀_in_V_x hW_x_open hxW_x hW_x_sub_W₀ hbound
    using hper_x
  -- Pairwise disjointness of W_x.
  have hW_x_disj : ∀ x₁ ∈ S, ∀ x₂ ∈ S, x₁ ≠ x₂ → Disjoint (W_x x₁) (W_x x₂) := by
    intro x₁ hx₁ x₂ hx₂ hne
    exact (hW₀_disj hx₁ hx₂ hne).mono (hW_x_sub_W₀ x₁ hx₁) (hW_x_sub_W₀ x₂ hx₂)
  -- V_int := ⋂ x ∈ S, V_x x.
  have hV_int_nhds : (⋂ x ∈ (S : Set X), V_x x) ∈ 𝓝 y₀ := by
    refine (Filter.biInter_finset_mem S).mpr ?_
    intro x hxS
    exact (hV_x_open x hxS).mem_nhds (hy₀_in_V_x x hxS)
  -- Ω := ⋃ x ∈ S, W_x x.
  let Ω : Set X := ⋃ x ∈ (S : Set X), W_x x
  have hΩ_open : IsOpen Ω :=
    isOpen_biUnion (fun x hxS => hW_x_open x hxS)
  have hFiber_sub_Ω : f ⁻¹' {y₀} ⊆ Ω := by
    intro x hx_fib
    have hxS : x ∈ S := hfiber_eq.mpr hx_fib
    exact Set.mem_biUnion (Finset.mem_coe.mpr hxS) (hxW_x x hxS)
  have hFiber_eventually : ∀ᶠ y' in 𝓝 y₀, f ⁻¹' {y'} ⊆ Ω :=
    eventually_fiber_subset_of_compact_T2 hHol.continuous hΩ_open hFiber_sub_Ω
  -- Combine into a single open V ∋ y₀.
  obtain ⟨V_fiber, hV_fiber_sub, hV_fiber_open, hy₀_in_V_fiber⟩ :=
    mem_nhds_iff.mp hFiber_eventually
  obtain ⟨V_int_open, hV_int_open_sub, hV_int_open_isOpen, hy₀_in_V_int_open⟩ :=
    mem_nhds_iff.mp hV_int_nhds
  set V : Set Y := V_fiber ∩ V_int_open with hV_def
  have hV_open : IsOpen V := hV_fiber_open.inter hV_int_open_isOpen
  have hy₀_V : y₀ ∈ V := ⟨hy₀_in_V_fiber, hy₀_in_V_int_open⟩
  -- The bound: sum of all per-fiber-point bounds.
  refine ⟨V, ∑ x ∈ S, M_x x, hV_open, hy₀_V, ?_⟩
  intro y hy_V hy_reg
  have hy_fib : f ⁻¹' {y} ⊆ Ω := hV_fiber_sub hy_V.1
  have hy_in_V_x : ∀ x ∈ S, y ∈ V_x x := by
    intro x hxS
    have hy_int : y ∈ ⋂ x ∈ (S : Set X), V_x x := hV_int_open_sub hy_V.2
    exact (Set.mem_iInter₂.mp hy_int) x (Finset.mem_coe.mpr hxS)
  -- Decompose (hbc.finite_fiber y).toFinset by which W_x x contains the preimage.
  -- For each preimage x' ∈ fiber(y), x' ∈ Ω, so exactly one x ∈ S has x' ∈ W_x x.
  set T : Finset X := (hbc.finite_fiber y).toFinset with hT_def
  -- Type-stable summand using CotangentModelFiber ℂ.
  let v : X → CotangentModelFiber ℂ := fun x =>
    cotangentPushforward f x (η.toFun x)
  have hT_decomp_sum :
      (T.attach.sum (fun x => v x.1) : CotangentModelFiber ℂ) =
        ∑ x₀ ∈ S, ((T.filter (· ∈ W_x x₀)).attach.sum
          (fun x' => v x'.1) : CotangentModelFiber ℂ) := by
    -- Step 1: reduce both sides' attach sums to ordinary sums.
    have hLHS : T.attach.sum (fun x => v x.1) = T.sum v :=
      Finset.sum_attach T v
    have hRHS : ∀ x₀ ∈ S,
        ((T.filter (· ∈ W_x x₀)).attach.sum (fun x' => v x'.1) :
          CotangentModelFiber ℂ) =
        (T.filter (· ∈ W_x x₀)).sum v :=
      fun x₀ _ => Finset.sum_attach (T.filter (· ∈ W_x x₀)) v
    rw [hLHS]
    rw [show (∑ x₀ ∈ S, ((T.filter (· ∈ W_x x₀)).attach.sum (fun x' => v x'.1) :
            CotangentModelFiber ℂ)) =
          ∑ x₀ ∈ S, (T.filter (· ∈ W_x x₀)).sum v from
      Finset.sum_congr rfl hRHS]
    -- Step 2: T = ⋃ x₀ ∈ S, T.filter (· ∈ W_x x₀), disjoint union.
    -- Use sum_biUnion in reverse.
    symm
    rw [← Finset.sum_biUnion]
    · -- The big-union equals T.
      apply Finset.sum_congr ?_ (fun _ _ => rfl)
      ext x'
      simp only [Finset.mem_biUnion, Finset.mem_filter]
      constructor
      · rintro ⟨_, _, hx'T, _⟩; exact hx'T
      · intro hx'T
        have hx'_fib : x' ∈ f ⁻¹' {y} := (Set.Finite.mem_toFinset _).mp hx'T
        have hx'_Ω : x' ∈ Ω := hy_fib hx'_fib
        rcases Set.mem_iUnion₂.mp hx'_Ω with ⟨x₀, hx₀S_coe, hx'W⟩
        exact ⟨x₀, Finset.mem_coe.mp hx₀S_coe, hx'T, hx'W⟩
    · -- Pairwise disjointness of filters.
      intro x₁ hx₁ x₂ hx₂ hne
      simp only [Function.onFun, Finset.disjoint_left, Finset.mem_filter]
      rintro x' ⟨_, hx'W₁⟩ ⟨_, hx'W₂⟩
      exact (Set.disjoint_iff.mp
        (hW_x_disj x₁ hx₁ x₂ hx₂ hne)) ⟨hx'W₁, hx'W₂⟩
  -- Now bound the trace via triangle inequality + per-fiber-point bound.
  show ‖traceAtRegularValue hbc (fun x => η.toFun x) y hy_reg‖ ≤ ∑ x ∈ S, M_x x
  -- traceAtRegularValue unfolds to T.attach.sum.
  have htrace_eq :
      (traceAtRegularValue hbc (fun x => η.toFun x) y hy_reg :
        CotangentModelFiber ℂ) =
        T.attach.sum (fun x => v x.1) := by
    unfold traceAtRegularValue
    rfl
  rw [show ‖traceAtRegularValue hbc (fun x => η.toFun x) y hy_reg‖ =
      ‖(T.attach.sum (fun x => v x.1) : CotangentModelFiber ℂ)‖ from
    congrArg norm htrace_eq]
  rw [hT_decomp_sum]
  refine (norm_sum_le _ _).trans ?_
  refine Finset.sum_le_sum ?_
  intro x₀ hx₀S
  exact hbound x₀ hx₀S y (hy_in_V_x x₀ hx₀S) hy_reg

omit [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]
  [StableChartAt ℂ X] [T2Space Y] [CompactSpace Y] [ConnectedSpace Y]
  [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ, ℂ) ω Y] [StableChartAt ℂ Y] in
/--
**One-dimensional Riemann removable-singularity provider (sub-helper).**

Given an analytic function `φ : ℂ → ℂ` on a punctured neighbourhood
`s \ {c}` of `c : ℂ` that is bounded on that punctured nhd,
Riemann's removable singularity theorem produces an analytic
extension `φ_ext` to a full nhd of `c`, agreeing with `φ` on the
punctured nhd.

This is the pure 1D classical complex-analysis content, intended
to be directly answerable by Mathlib's
`Mathlib.Analysis.Complex.RemovableSingularity`:
* `analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt`,
* `tendsto_limUnder_of_differentiable_on_punctured_nhds_of_bounded_under`,
* `differentiableOn_update_limUnder_of_bddAbove`.

Provided here as a `private` 1D sub-lemma used by
`removableSingularity_at_branchPoint`'s chart-local transposition.
-/
private theorem removableSingularity_oneD_punctured_disc
    (φ : ℂ → ℂ) (c : ℂ)
    (_s : Set ℂ) (_hs_nhds : _s ∈ 𝓝 c)
    (_hφ_hol : ∀ z ∈ _s, z ≠ c → AnalyticAt ℂ φ z)
    (M : ℝ) (_hφ_bnd : ∀ z ∈ _s, z ≠ c → ‖φ z‖ ≤ M) :
    ∃ (φ_ext : ℂ → ℂ) (s' : Set ℂ),
      s' ∈ 𝓝 c ∧ s' ⊆ _s ∧ AnalyticAt ℂ φ_ext c ∧
      ∀ z ∈ s', z ≠ c → φ_ext z = φ z := by
  classical
  -- φ is differentiable on _s \ {c}.
  have hdiff : DifferentiableOn ℂ φ (_s \ {c}) := by
    intro z hz
    have hz_ne : z ≠ c := by
      intro hzc; exact hz.2 hzc
    exact ((_hφ_hol z hz.1 hz_ne).differentiableAt).differentiableWithinAt
  -- ‖φ‖ is bounded above on _s \ {c} by M.
  have hbnd : BddAbove (norm ∘ φ '' (_s \ {c})) := by
    refine ⟨M, ?_⟩
    rintro x ⟨z, ⟨hz_in_s, hz_not_c⟩, rfl⟩
    have hz_ne : z ≠ c := fun hzc => hz_not_c hzc
    exact _hφ_bnd z hz_in_s hz_ne
  -- Apply Riemann's removable singularity theorem (bounded version).
  have hext_diff :
      DifferentiableOn ℂ
        (Function.update φ c (limUnder (𝓝[≠] c) φ)) _s :=
    Complex.differentiableOn_update_limUnder_of_bddAbove _hs_nhds hdiff hbnd
  -- The updated function is analytic at c (1D Cauchy: DifferentiableOn → AnalyticAt).
  set φ_ext : ℂ → ℂ := Function.update φ c (limUnder (𝓝[≠] c) φ) with hφ_ext_def
  have hAnalyticAt : AnalyticAt ℂ φ_ext c := hext_diff.analyticAt _hs_nhds
  refine ⟨φ_ext, _s, _hs_nhds, Set.Subset.rfl, hAnalyticAt, ?_⟩
  -- Agreement: φ_ext z = φ z for z ≠ c.
  intro z _ hz_ne
  show Function.update φ c (limUnder (𝓝[≠] c) φ) z = φ z
  exact Function.update_of_ne hz_ne _ _

omit [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]
  [StableChartAt ℂ X] in
/--
**Per-branch-point Riemann removable-singularity provider.**

Given a function `g : Y → CotangentModelFiber ℂ` holomorphic on
`regular` (with finite complement) and locally bounded on a
neighborhood `U` of a branch point `y₀ ∈ regularᶜ`, Riemann's
removable singularity theorem produces a function `g_y₀` that is
holomorphic at `y₀` and agrees with `g` on a small `Y`-nhd of `y₀`
intersected with `regular`.

Mathematically: in chart-local coordinates around `y₀`, the function
`cotangentFiberIso ∘ g ∘ chart.symm` is a `ℂ`-valued holomorphic
function on a punctured disc around `chart y₀` (since the only
non-regular point in a small `Y`-nhd of `y₀` is `y₀` itself, by
finiteness of `regularᶜ`) and is bounded there. Riemann's classical
removable singularity theorem extends this to a holomorphic function
on the full disc, which translates back to `g_y₀` holomorphic at `y₀`.

The chart-local transposition is now sorry-free: the entire analytic
content has been reduced to the strictly narrower 1D sub-lemma
`removableSingularity_oneD_punctured_disc` via
* `StableChartAt ℂ Y` (chart agrees with `chartAt ℂ y₀` near `y₀`),
* `singletonChartedSpace_chartAt_eq` (the chart on
  `CotangentModelFiber ℂ` is `cotangentFiberIso`),
* operator-norm bound `‖cotangentFiberIso w‖ ≤ ‖cotangentFiberIso‖ * ‖w‖`,
* `AnalyticAt.congr` / `apply_symm_apply` / `symm_apply_apply`.
-/
private theorem removableSingularity_at_branchPoint
    (regular : Set Y) (hOpen : IsOpen regular)
    (hFiniteCompl : regularᶜ.Finite)
    (g : Y → CotangentModelFiber ℂ)
    (hHol : ∀ y ∈ regular, IsHolomorphicAt (fun y' : Y => g y') y)
    (y₀ : Y) (hy₀_branch : y₀ ∈ regularᶜ)
    (U : Set Y) (hU_open : IsOpen U) (hy₀_U : y₀ ∈ U) (M : ℝ)
    (hbound : ∀ y ∈ U ∩ regular, ‖g y‖ ≤ M) :
    ∃ (g_y₀ : Y → CotangentModelFiber ℂ) (V : Set Y),
      IsOpen V ∧ y₀ ∈ V ∧ V ⊆ U ∧
      IsHolomorphicAt g_y₀ y₀ ∧
      ∀ y ∈ V ∩ regular, g_y₀ y = g y := by
  classical
  -- Set up chart at y₀ and refine the open nhd to exclude other branch points.
  set chart := chartAt ℂ y₀ with hchart_def
  set c : ℂ := chart y₀ with hc_def
  have hy₀_chart_src : y₀ ∈ chart.source := mem_chart_source ℂ y₀
  -- Other branch points (regularᶜ \ {y₀}) form a finite (hence closed) set.
  set otherBranches : Set Y := regularᶜ \ {y₀} with hotherBranches_def
  have hotherBranches_finite : otherBranches.Finite := hFiniteCompl.diff
  have hotherBranches_closed : IsClosed otherBranches :=
    hotherBranches_finite.isClosed
  -- Refined open nhd of y₀ inside U ∩ chart.source minus other branch points.
  set U' : Set Y := U ∩ chart.source ∩ otherBranchesᶜ with hU'_def
  have hU'_open : IsOpen U' :=
    (hU_open.inter chart.open_source).inter hotherBranches_closed.isOpen_compl
  have hy₀_U' : y₀ ∈ U' := by
    refine ⟨⟨hy₀_U, hy₀_chart_src⟩, ?_⟩
    intro hcontra
    exact hcontra.2 rfl
  have hU'_sub_src : U' ⊆ chart.source :=
    fun y hy => hy.1.2
  have hU'_sub_U : U' ⊆ U := fun y hy => hy.1.1
  -- s = chart '' U', open in ℂ, nhd of c.
  set s : Set ℂ := chart '' U' with hs_def
  have hs_open : IsOpen s := chart.isOpen_image_of_subset_source hU'_open hU'_sub_src
  have hc_mem_s : c ∈ s := ⟨y₀, hy₀_U', rfl⟩
  have hs_nhds : s ∈ 𝓝 c := hs_open.mem_nhds hc_mem_s
  -- φ : ℂ → ℂ, the chart-local form of g at y₀.
  set φ : ℂ → ℂ := fun z => cotangentFiberIso (g (chart.symm z)) with hφ_def
  -- Analyticity of φ on s \ {c}. For z ∈ s with z ≠ c, let y := chart.symm z.
  -- y ∈ U', y ≠ y₀ (chart-injective), and y ∉ otherBranches, so y ∈ regular.
  -- Then chartLocalAt g y = φ near z (via StableChartAt), giving AnalyticAt φ z.
  have hφ_hol : ∀ z ∈ s, z ≠ c → AnalyticAt ℂ φ z := by
    intro z hz_in_s hz_ne_c
    obtain ⟨y, hy_U', hy_chart⟩ := hz_in_s
    -- y ∈ chart.source.
    have hy_src : y ∈ chart.source := hU'_sub_src hy_U'
    -- y ≠ y₀, because chart y ≠ chart y₀.
    have hy_ne_y₀ : y ≠ y₀ := by
      intro h
      apply hz_ne_c
      rw [← hy_chart, h]
    -- y ∉ otherBranches.
    have hy_not_other : y ∉ otherBranches := hy_U'.2
    -- y ∈ regular: y is not in regularᶜ \ {y₀} and y ≠ y₀, so y ∉ regularᶜ.
    have hy_reg : y ∈ regular := by
      by_contra hy_not_reg
      apply hy_not_other
      exact ⟨hy_not_reg, hy_ne_y₀⟩
    -- StableChartAt: chartAt ℂ y = chartAt ℂ y₀ = chart.
    have hchart_y_eq : chartAt ℂ y = chart := by
      have := StableChartAt.chartAt_eq_of_mem_source (H := ℂ) (M := Y) y₀ y hy_src
      exact this
    -- IsHolomorphicAt g y means AnalyticAt ℂ (chartLocalAt g y) (chartAt ℂ y y).
    have hg_hol_y : IsHolomorphicAt g y := hHol y hy_reg
    -- chartLocalAt g y = cotangentFiberIso ∘ g ∘ (chartAt ℂ y).symm.
    -- Under hchart_y_eq, this equals cotangentFiberIso ∘ g ∘ chart.symm = φ.
    -- And (chartAt ℂ y) y = chart y = z.
    have hg_hol_y' : AnalyticAt ℂ (chartLocalAt g y) (chartAt ℂ y y) := hg_hol_y
    -- Rewrite using hchart_y_eq.
    have hchart_loc_eq :
        chartLocalAt g y = fun q => chartAt ℂ (g y) (g (chart.symm q)) := by
      unfold chartLocalAt
      funext q
      simp [hchart_y_eq, Function.comp]
    have h_point_eq : chartAt ℂ y y = z := by
      rw [hchart_y_eq, ← hy_chart]
    rw [hchart_loc_eq, h_point_eq] at hg_hol_y'
    -- chartAt ℂ (g y) = cotangentFiberIso (singleton chart on CotangentModelFiber ℂ).
    -- So chartLocalAt g y q = cotangentFiberIso (g (chart.symm q)) = φ q.
    have hchart_target_eq :
        (fun q => chartAt ℂ (g y) (g (chart.symm q))) = φ := by
      funext q
      show chartAt ℂ (g y) (g (chart.symm q)) = cotangentFiberIso (g (chart.symm q))
      rfl
    rw [hchart_target_eq] at hg_hol_y'
    exact hg_hol_y'
  -- Boundedness of φ on s \ {c}.
  -- ‖φ z‖ = ‖cotangentFiberIso (g y)‖ ≤ ‖cotangentFiberIso‖ * ‖g y‖ ≤ ‖cotangentFiberIso‖ * M.
  set Miso : ℝ := ‖(cotangentFiberIso : (ℂ →L[ℂ] ℂ) →L[ℂ] ℂ)‖ with hMiso_def
  have hMiso_nonneg : 0 ≤ Miso :=
    norm_nonneg (cotangentFiberIso : (ℂ →L[ℂ] ℂ) →L[ℂ] ℂ)
  set M' : ℝ := Miso * M + 1 with hM'_def
  have hφ_bnd : ∀ z ∈ s, z ≠ c → ‖φ z‖ ≤ M' := by
    intro z hz_in_s hz_ne_c
    obtain ⟨y, hy_U', hy_chart⟩ := hz_in_s
    have hy_src : y ∈ chart.source := hU'_sub_src hy_U'
    have hy_ne_y₀ : y ≠ y₀ := by
      intro h; apply hz_ne_c; rw [← hy_chart, h]
    have hy_not_other : y ∉ otherBranches := hy_U'.2
    have hy_reg : y ∈ regular := by
      by_contra hy_not_reg
      apply hy_not_other
      exact ⟨hy_not_reg, hy_ne_y₀⟩
    have hy_U : y ∈ U := hU'_sub_U hy_U'
    have hbnd_y : ‖g y‖ ≤ M := hbound y ⟨hy_U, hy_reg⟩
    -- ‖φ z‖ = ‖cotangentFiberIso (g y)‖.
    have hφz_eq : φ z = cotangentFiberIso (g y) := by
      show cotangentFiberIso (g (chart.symm z)) = cotangentFiberIso (g y)
      rw [← hy_chart, chart.left_inv hy_src]
    rw [hφz_eq]
    -- Use ‖cotangentFiberIso (g y)‖ ≤ ‖cotangentFiberIso‖ * ‖g y‖.
    have h_op_bnd : ‖cotangentFiberIso (g y)‖ ≤ Miso * ‖g y‖ :=
      (cotangentFiberIso : (ℂ →L[ℂ] ℂ) →L[ℂ] ℂ).le_opNorm (g y)
    have h_mul_bnd : Miso * ‖g y‖ ≤ Miso * M :=
      mul_le_mul_of_nonneg_left hbnd_y hMiso_nonneg
    have h_total : ‖cotangentFiberIso (g y)‖ ≤ Miso * M :=
      h_op_bnd.trans h_mul_bnd
    linarith
  -- Apply the 1D removable-singularity helper.
  obtain ⟨φ_ext, s', hs'_nhds, hs'_sub, hφ_ext_an, hφ_ext_eq⟩ :=
    removableSingularity_oneD_punctured_disc φ c s hs_nhds hφ_hol M' hφ_bnd
  -- Define g_y₀ on chart.source and 0 elsewhere.
  let g_y₀ : Y → CotangentModelFiber ℂ := fun y =>
    if hy : y ∈ chart.source then cotangentFiberIso.symm (φ_ext (chart y))
    else (0 : CotangentModelFiber ℂ)
  -- Extract an open subset s'_open ⊆ s' that is a nhd of c.
  -- Since s' ∈ 𝓝 c, ∃ open T ⊆ s' with c ∈ T.
  obtain ⟨s'_open, hs'_open_sub, hs'_open_isOpen, hc_mem_s'_open⟩ :=
    mem_nhds_iff.mp hs'_nhds
  -- V = chart ⁻¹' s'_open ∩ U'. This is open (preimage of open under continuous chart
  -- restricted to source, intersected with open U' which ⊆ source).
  set V : Set Y := chart.source ∩ chart ⁻¹' s'_open ∩ U' with hV_def
  have hV_open : IsOpen V := by
    have h1 : IsOpen (chart.source ∩ chart ⁻¹' s'_open) :=
      chart.continuousOn.isOpen_inter_preimage chart.open_source hs'_open_isOpen
    exact h1.inter hU'_open
  have hy₀_V : y₀ ∈ V := by
    refine ⟨⟨hy₀_chart_src, ?_⟩, hy₀_U'⟩
    show chart y₀ ∈ s'_open
    rw [← hc_def]; exact hc_mem_s'_open
  have hV_sub_U : V ⊆ U := fun y hy => hU'_sub_U hy.2
  refine ⟨g_y₀, V, hV_open, hy₀_V, hV_sub_U, ?_, ?_⟩
  · -- IsHolomorphicAt g_y₀ y₀: chartLocalAt g_y₀ y₀ is analytic at c.
    -- Show chartLocalAt g_y₀ y₀ =ᶠ[𝓝 c] φ_ext, then apply
    -- AnalyticAt.congr (φ_ext is analytic at c).
    show AnalyticAt ℂ (chartLocalAt g_y₀ y₀) (chartAt ℂ y₀ y₀)
    -- Need a nhd of c where chartLocalAt g_y₀ y₀ q = φ_ext q.
    -- For q in chart.target, chart.symm q ∈ chart.source, so
    -- g_y₀ (chart.symm q) = cotangentFiberIso.symm (φ_ext (chart (chart.symm q)))
    --                     = cotangentFiberIso.symm (φ_ext q).
    -- Then chartLocalAt g_y₀ y₀ q = chartAt ℂ (g_y₀ y₀) (g_y₀ (chart.symm q))
    --                             = cotangentFiberIso (cotangentFiberIso.symm (φ_ext q))
    --                             = φ_ext q.
    have h_target_nhd : chart.target ∈ 𝓝 c := by
      have hc_target : c ∈ chart.target := by
        rw [hc_def]; exact chart.map_source hy₀_chart_src
      exact chart.open_target.mem_nhds hc_target
    have h_ev_eq : chartLocalAt g_y₀ y₀ =ᶠ[𝓝 (chart y₀)] φ_ext := by
      have : chart y₀ = c := by rw [hc_def]
      rw [this]
      filter_upwards [h_target_nhd] with q hq_target
      have hsymm_src : chart.symm q ∈ chart.source := chart.map_target hq_target
      have hright_inv : chart (chart.symm q) = q := chart.right_inv hq_target
      show chartAt ℂ (g_y₀ y₀) (g_y₀ (chart.symm q)) = φ_ext q
      have h_gy_eq : g_y₀ (chart.symm q) = cotangentFiberIso.symm (φ_ext q) := by
        show (if hy : chart.symm q ∈ chart.source then
                cotangentFiberIso.symm (φ_ext (chart (chart.symm q)))
              else (0 : CotangentModelFiber ℂ)) =
              cotangentFiberIso.symm (φ_ext q)
        rw [dif_pos hsymm_src, hright_inv]
      rw [h_gy_eq]
      show cotangentFiberIso (cotangentFiberIso.symm (φ_ext q)) = φ_ext q
      exact cotangentFiberIso.apply_symm_apply (φ_ext q)
    exact hφ_ext_an.congr h_ev_eq.symm
  · -- Agreement: g_y₀ y = g y for y ∈ V ∩ regular.
    intro y hyV
    obtain ⟨⟨⟨hy_src, hy_pre⟩, hy_U'⟩, hy_reg⟩ := hyV
    -- chart y ∈ s'_open ⊆ s'.
    have hy_s' : chart y ∈ s' := hs'_open_sub hy_pre
    -- chart y ≠ c since y ≠ y₀ (because y ∈ regular, y₀ ∉ regular).
    have hy_ne_y₀ : y ≠ y₀ := by
      intro h; rw [h] at hy_reg; exact hy₀_branch hy_reg
    have hchart_ne_c : chart y ≠ c := by
      intro h
      apply hy_ne_y₀
      have hinj := chart.injOn
      exact hinj hy_src hy₀_chart_src (by rw [h, hc_def])
    have hext_eq : φ_ext (chart y) = φ (chart y) :=
      hφ_ext_eq (chart y) hy_s' hchart_ne_c
    -- φ (chart y) = cotangentFiberIso (g (chart.symm (chart y))) = cotangentFiberIso (g y).
    have hφ_chart_y : φ (chart y) = cotangentFiberIso (g y) := by
      show cotangentFiberIso (g (chart.symm (chart y))) = cotangentFiberIso (g y)
      rw [chart.left_inv hy_src]
    -- g_y₀ y = cotangentFiberIso.symm (φ_ext (chart y))
    --       = cotangentFiberIso.symm (cotangentFiberIso (g y)) = g y.
    show (if hy : y ∈ chart.source then cotangentFiberIso.symm (φ_ext (chart y))
          else (0 : CotangentModelFiber ℂ)) = g y
    rw [dif_pos hy_src, hext_eq, hφ_chart_y]
    exact cotangentFiberIso.symm_apply_apply (g y)

omit [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]
  [StableChartAt ℂ X] in
/--
**Pointwise gluing of per-branch-point local extensions into a
globally-holomorphic function.**

Given the holomorphic function `g` on the open dense `regular` set,
together with per-branch-point local extensions `g_y₀` (each
holomorphic at its branch point `y₀` and agreeing with `g` on a nhd
of `y₀` intersected with `regular`), this helper produces a single
function `g_ext : Y → CotangentModelFiber ℂ` that is `IsHolomorphicAt`
at every point of `Y` and agrees with `g` on `regular`.

Mathematically: define `g_ext y := if y ∈ regular then g y else
g_{y₀ y} y` where `y₀ y` is the unique branch point (or any one, by
choice). Holomorphicity at `y ∈ regular` follows from `hHol`; at a
branch point `y₀`, from the local extension's `IsHolomorphicAt g_y₀
y₀` combined with the eq-on-`V ∩ regular` clause (which identifies
`g_ext` with `g_y₀` on a punctured nhd of `y₀`).

This isolates the **pointwise function-level** gluing obligation —
the per-branch-point selection via `Classical.choice` plus the local
holomorphicity verification — deferred as a single `sorry`.
-/
private theorem globalHolomorphicFunction_from_local_extensions
    (regular : Set Y) (hOpen : IsOpen regular) (hDense : Dense regular)
    (hFiniteCompl : regularᶜ.Finite)
    (g : Y → CotangentModelFiber ℂ)
    (hHol : ∀ y ∈ regular, IsHolomorphicAt (fun y' : Y => g y') y)
    (extensions : ∀ y₀ ∈ regularᶜ,
      ∃ (g_y₀ : Y → CotangentModelFiber ℂ) (V : Set Y),
        IsOpen V ∧ y₀ ∈ V ∧ IsHolomorphicAt g_y₀ y₀ ∧
        ∀ y ∈ V ∩ regular, g_y₀ y = g y) :
    ∃ g_ext : Y → CotangentModelFiber ℂ,
      (∀ y : Y, IsHolomorphicAt g_ext y) ∧
      ∀ y ∈ regular, g_ext y = g y := by
  classical
  -- Define g_ext via dite, selecting g on regular and the chosen local
  -- extension at each branch point.
  let g_ext : Y → CotangentModelFiber ℂ := fun y =>
    if hy : y ∈ regular then g y
    else (extensions y hy).choose y
  refine ⟨g_ext, ?_, ?_⟩
  · -- Pointwise holomorphicity.
    intro y
    by_cases hy_reg : y ∈ regular
    · -- Case: y ∈ regular.
      -- g_ext = g on the open set `regular`, a nhd of y.
      have h_eventually : g_ext =ᶠ[𝓝 y] g := by
        have : regular ∈ 𝓝 y := hOpen.mem_nhds hy_reg
        filter_upwards [this] with z hz_reg
        show g_ext z = g z
        simp [g_ext, hz_reg]
      exact (hHol y hy_reg).congr_of_eventuallyEq h_eventually.symm
    · -- Case: y ∈ regularᶜ. Extract the chosen extension witness.
      have hy_branch : y ∈ regularᶜ := hy_reg
      set ext_data := (extensions y hy_branch).choose_spec.choose_spec
      let g_y := (extensions y hy_branch).choose
      let V_y := (extensions y hy_branch).choose_spec.choose
      have hV_y_open : IsOpen V_y := ext_data.1
      have hy_V_y : y ∈ V_y := ext_data.2.1
      have hg_y_hol : IsHolomorphicAt g_y y := ext_data.2.2.1
      have hg_y_eq : ∀ z ∈ V_y ∩ regular, g_y z = g z := ext_data.2.2.2
      -- Refine V_y to exclude other branch points besides y.
      set otherBranches : Set Y := regularᶜ \ {y} with hotherBranches_def
      have hotherBranches_finite : otherBranches.Finite :=
        hFiniteCompl.diff
      have hotherBranches_closed : IsClosed otherBranches :=
        hotherBranches_finite.isClosed
      set V_y' : Set Y := V_y ∩ otherBranchesᶜ with hV_y'_def
      have hV_y'_open : IsOpen V_y' :=
        hV_y_open.inter hotherBranches_closed.isOpen_compl
      have hy_V_y' : y ∈ V_y' := by
        refine ⟨hy_V_y, ?_⟩
        intro h_other
        exact h_other.2 rfl
      -- On V_y', g_ext = g_y.
      have h_eventually : g_ext =ᶠ[𝓝 y] g_y := by
        have : V_y' ∈ 𝓝 y := hV_y'_open.mem_nhds hy_V_y'
        filter_upwards [this] with z hz_V_y'
        show g_ext z = g_y z
        by_cases hz_reg : z ∈ regular
        · -- z ∈ V_y ∩ regular, so g_y z = g z by hg_y_eq.
          have : g_y z = g z := hg_y_eq z ⟨hz_V_y'.1, hz_reg⟩
          simp [g_ext, hz_reg, this]
        · -- z ∈ regularᶜ. Since z ∈ V_y' = V_y ∩ otherBranchesᶜ, z ∉ otherBranches.
          -- z ∈ regularᶜ ∧ z ∉ otherBranches = regularᶜ \ {y}, so z = y.
          have hz_branch : z ∈ regularᶜ := hz_reg
          have hz_not_other : z ∉ otherBranches := hz_V_y'.2
          have hz_eq_y : z = y := by
            by_contra hz_ne
            exact hz_not_other ⟨hz_branch, hz_ne⟩
          -- Substitute z = y; then both sides have the same Classical.choose term.
          subst hz_eq_y
          -- After subst, g_ext z and g_y z are both `(extensions z _).choose z`.
          -- Use simp to unfold the let bindings.
          simp only [g_ext]
          rw [dif_neg hz_reg]
      exact hg_y_hol.congr_of_eventuallyEq h_eventually.symm
  · -- Equality on regular.
    intro y hy_reg
    show g_ext y = g y
    simp [g_ext, hy_reg]

omit [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]
  [StableChartAt ℂ X] in
/--
**Manifold-level `ContMDiff` from pointwise `IsHolomorphicAt`
(scaffolding helper).**

Given a function `g_ext : Y → CotangentModelFiber ℂ` with pointwise
`IsHolomorphicAt`, this packages the project-local chart-local
analyticity into Mathlib's manifold-level `ContMDiff` formalism via:

* `IsHolomorphicAt.continuousAt_cotangentModelFiber` (already in this
  file) — pointwise continuity at each `y`, which assembles to global
  `Continuous g_ext` via `continuous_iff_continuousAt`;
* `ContMDiff.of_isHolomorphic_and_continuous` (in `HolomorphicMap.lean`)
  — promotes `∀ p, IsHolomorphicAt f p` + `Continuous f` to
  `ContMDiff 𝓘(ℂ) 𝓘(ℂ) ⊤ f`.

Note: the result type is `ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ⊤ g_ext`, not
`ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, CotangentModelFiber ℂ) ⊤`, because
`CotangentModelFiber ℂ` is charted on `ℂ` via the singleton chart
`cotangentFiberIso : (ℂ →L[ℂ] ℂ) ≃L[ℂ] ℂ`, so its manifold model is
`ℂ` (not `ℂ →L[ℂ] ℂ`).

This isolates the clean Mathlib-shape composition as a reusable
named lemma, in preparation for the bundle-section
`ContMDiff` proof.
-/
private theorem contMDiff_of_pointwiseHolomorphic
    (g_ext : Y → CotangentModelFiber ℂ)
    (hg_ext_hol : ∀ y : Y, IsHolomorphicAt g_ext y) :
    ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (⊤ : WithTop ℕ∞) g_ext := by
  have hcont : Continuous g_ext :=
    continuous_iff_continuousAt.mpr fun y =>
      (hg_ext_hol y).continuousAt_cotangentModelFiber
  exact ContMDiff.of_isHolomorphic_and_continuous hg_ext_hol hcont

omit [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]
  [StableChartAt ℂ X] in
/--
**Bundle-section `ContMDiff` from pointwise holomorphicity (strictly
narrower sub-helper).**

Given a function `g_ext : Y → CotangentModelFiber ℂ` that is
`IsHolomorphicAt` at every point of `Y`, the corresponding section
of the cotangent bundle (viewed via the section/total-space
embedding required by `ContMDiffSection`) is `ContMDiff` of class
`⊤`.

This is the pure bundle-`ContMDiff` content used by
`holomorphicOneForm_of_pointwiseHolomorphic`. It isolates the
transposition from project-local `IsHolomorphicAt` (chart-local
analyticity of `cotangentFiberIso ∘ g_ext ∘ (chartAt ℂ y).symm`)
into Mathlib's bundle smoothness formalism via `contMDiffAt_section`
and the trivialization of the cotangent bundle. The exact
statement reproduces the `contMDiff_toFun` field of
`ContMDiffSection` for the `HolomorphicOneForm` abbreviation.
-/
private theorem bundleSection_contMDiff_of_pointwiseHolomorphic
    (g_ext : Y → CotangentModelFiber ℂ)
    (hg_ext_hol : ∀ y : Y, IsHolomorphicAt g_ext y) :
    ContMDiff (𝓘(ℂ, ℂ)) ((𝓘(ℂ, ℂ)).prod 𝓘(ℂ, CotangentModelFiber ℂ))
      (⊤ : WithTop ℕ∞)
      (fun y : Y =>
        (Bundle.TotalSpace.mk' (E := CotangentSpace ℂ Y) (CotangentModelFiber ℂ)
          y (g_ext y) :
          Bundle.TotalSpace (CotangentModelFiber ℂ) (CotangentSpace ℂ Y))) := by
  sorry

omit [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]
  [StableChartAt ℂ X] in
/--
**Bundle-section packaging: pointwise holomorphicity → `HolomorphicOneForm`.**

Given a function `g_ext : Y → CotangentModelFiber ℂ` that is
`IsHolomorphicAt` at every point of `Y`, this helper packages it
into a `HolomorphicOneForm ℂ Y` whose underlying function `τ.toFun`
equals `g_ext` pointwise.

This is now a sorry-free reduction to the strictly narrower
bundle-section `ContMDiff` sub-helper
`bundleSection_contMDiff_of_pointwiseHolomorphic`. The
`HolomorphicOneForm` is constructed via the `ContMDiffSection`
constructor with `toFun := g_ext` (relying on the defeq
`CotangentSpace ℂ Y y = CotangentModelFiber ℂ` coming from
`TangentSpace 𝓘(ℂ, ℂ) y = ℂ` and `Bundle.Trivial Y ℂ y = ℂ`); the
agreement `τ.toFun y = g_ext y` then holds by `rfl`.
-/
private theorem holomorphicOneForm_of_pointwiseHolomorphic
    (g_ext : Y → CotangentModelFiber ℂ)
    (hg_ext_hol : ∀ y : Y, IsHolomorphicAt g_ext y) :
    ∃ τ : HolomorphicOneForm ℂ Y, ∀ y : Y, τ.toFun y = g_ext y :=
  ⟨⟨g_ext,
    bundleSection_contMDiff_of_pointwiseHolomorphic g_ext hg_ext_hol⟩,
    fun _ => rfl⟩

omit [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]
  [StableChartAt ℂ X] in
/--
**Global assembly of a holomorphic 1-form from per-branch-point
local extensions.**

Given the holomorphic function `g` on the open dense `regular` set,
together with per-branch-point local extensions `g_y₀` (each
holomorphic at its branch point `y₀` and agreeing with `g` on a nhd
of `y₀` intersected with `regular`), this provider glues them into a
single global `HolomorphicOneForm ℂ Y` whose `toFun` agrees with `g`
on `regular`.

This is now a sorry-free reduction to two strictly narrower providers:
* `globalHolomorphicFunction_from_local_extensions` (pointwise
  function-level gluing into a globally `IsHolomorphicAt` function);
* `holomorphicOneForm_of_pointwiseHolomorphic` (bundle-section
  packaging of a pointwise-holomorphic function as a
  `HolomorphicOneForm`).
-/
private theorem assemble_holomorphicOneForm_from_local_extensions
    (regular : Set Y) (hOpen : IsOpen regular) (hDense : Dense regular)
    (hFiniteCompl : regularᶜ.Finite)
    (g : Y → CotangentModelFiber ℂ)
    (hHol : ∀ y ∈ regular, IsHolomorphicAt (fun y' : Y => g y') y)
    (extensions : ∀ y₀ ∈ regularᶜ,
      ∃ (g_y₀ : Y → CotangentModelFiber ℂ) (V : Set Y),
        IsOpen V ∧ y₀ ∈ V ∧ IsHolomorphicAt g_y₀ y₀ ∧
        ∀ y ∈ V ∩ regular, g_y₀ y = g y) :
    ∃ τ : HolomorphicOneForm ℂ Y, ∀ y ∈ regular, τ.toFun y = g y := by
  -- Step 1: pointwise gluing into a globally holomorphic function.
  obtain ⟨g_ext, hg_ext_hol, hg_ext_eq⟩ :=
    globalHolomorphicFunction_from_local_extensions regular hOpen hDense
      hFiniteCompl g hHol extensions
  -- Step 2: bundle-section packaging.
  obtain ⟨τ, hτ⟩ := holomorphicOneForm_of_pointwiseHolomorphic g_ext hg_ext_hol
  -- Combine: τ.toFun y = g_ext y = g y for y ∈ regular.
  refine ⟨τ, ?_⟩
  intro y hy_reg
  rw [hτ y]
  exact hg_ext_eq y hy_reg

omit [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]
  [StableChartAt ℂ X] in
/--
**Provider (3).** *Generic removable-singularity provider for
holomorphic 1-forms.*

For any function `g : Y → CotangentModelFiber ℂ` that is
* holomorphic at every point of `regular` (an *open* dense subset of
  `Y` whose complement is `finite`), and
* locally bounded near every point of `regularᶜ`,

Riemann's removable singularity theorem produces a global
`HolomorphicOneForm ℂ Y` whose `toFun` agrees with `g` on `regular`.

This is the substantive classical analytic content — pure complex analysis
on `Y`, no reference to the source `X` or to the trace map. The
hypotheses are exactly the data produced by Providers (1) and (2)
when specialized to the trace function. Note that the conclusion
quantifies over a single open set `regular` and does not mention
branched-cover data, so it is strictly smaller than
`traceForm_global_extension` (which quantifies over *all* BCDs).

This is now a sorry-free combinatorial reduction to two strictly
narrower providers:
* `removableSingularity_at_branchPoint` (per-branch-point Riemann
  removable singularity);
* `assemble_holomorphicOneForm_from_local_extensions` (global bundle
  section gluing).
-/
theorem holomorphicOneForm_of_regularLocus_holomorphic_branchLocus_bounded
    (regular : Set Y) (hOpen : IsOpen regular) (hDense : Dense regular)
    (hFiniteCompl : regularᶜ.Finite)
    (g : Y → CotangentModelFiber ℂ)
    (hHol : ∀ y ∈ regular,
      IsHolomorphicAt (fun y' : Y => g y') y)
    (hBounded : ∀ y₀ ∈ regularᶜ,
      ∃ (U : Set Y) (M : ℝ), IsOpen U ∧ y₀ ∈ U ∧
        ∀ y ∈ U ∩ regular, ‖g y‖ ≤ M) :
    ∃ τ : HolomorphicOneForm ℂ Y,
      ∀ y ∈ regular, τ.toFun y = g y := by
  -- For each branch point, extract local bound data + apply per-point
  -- removable singularity to get a local extension.
  have extensions : ∀ y₀ ∈ regularᶜ,
      ∃ (g_y₀ : Y → CotangentModelFiber ℂ) (V : Set Y),
        IsOpen V ∧ y₀ ∈ V ∧ IsHolomorphicAt g_y₀ y₀ ∧
        ∀ y ∈ V ∩ regular, g_y₀ y = g y := by
    intro y₀ hy₀_branch
    obtain ⟨U, M, hU_open, hy₀_U, hbound⟩ := hBounded y₀ hy₀_branch
    obtain ⟨g_y₀, V, hV_open, hy₀_V, _hV_sub_U, hg_y₀_hol, hg_y₀_eq⟩ :=
      removableSingularity_at_branchPoint regular hOpen hFiniteCompl g hHol
        y₀ hy₀_branch U hU_open hy₀_U M hbound
    exact ⟨g_y₀, V, hV_open, hy₀_V, hg_y₀_hol, hg_y₀_eq⟩
  -- Assemble the global holomorphic form.
  exact assemble_holomorphicOneForm_from_local_extensions regular hOpen hDense
    hFiniteCompl g hHol extensions

omit [T2Space X] [CompactSpace X] [ConnectedSpace X] [StableChartAt ℂ X]
  [T2Space Y] [CompactSpace Y] [ConnectedSpace Y] [IsManifold 𝓘(ℂ, ℂ) ω Y]
  [StableChartAt ℂ Y] in
/--
**Provider (4).** *BCD-invariance of the local fibre trace.*

The local fibre sum `traceAtRegularValue hbc (fun x => η.toFun x) y hy`
depends only on `f`, `η`, and `y`, not on the choice of `hbc`. This
is purely set-theoretic: the relevant `Finset` is
`(hbc.finite_fiber y).toFinset`, and the witness of finiteness is a
`Subsingleton`, so two different `BranchedCoverData` produce the same
underlying Finset; the cotangent pushforward summands depend only on
the point in the fibre, not on `hbc`.
-/
theorem traceAtRegularValue_BCD_invariance
    {f : X → Y} (η : HolomorphicOneForm ℂ X)
    (hbc hbc' : BranchedCoverData X Y f) (y : Y)
    (hy : isRegularValue hbc y) (hy' : isRegularValue hbc' y) :
    traceAtRegularValue hbc (fun x => η.toFun x) y hy =
      traceAtRegularValue hbc' (fun x => η.toFun x) y hy' := by
  classical
  unfold traceAtRegularValue
  -- Both `finite_fiber` witnesses are proofs of the same proposition
  -- `(f ⁻¹' {y}).Finite`, hence equal by `Subsingleton`.
  have hsub : hbc.finite_fiber y = hbc'.finite_fiber y :=
    Subsingleton.elim _ _
  congr 1

/--
**Trace-locus pointwise holomorphic auxiliary for Provider (3).**

Provider (1) gives holomorphicity of `localTraceAtRegularValue` (a
chart-local representative). Provider (3) consumes pointwise
holomorphicity of the `dite`-extended global fibre sum. Bridging the
two is the chart-local identification of `localTraceAtRegularValue`
with the global pointwise `traceAtRegularValue`.
-/
theorem regularLocus_dite_trace_holomorphicAt
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (⊤ : WithTop ℕ∞) f)
    (η : HolomorphicOneForm ℂ X)
    (hbc : BranchedCoverData X Y f)
    (hcompat : hbc.RamificationIndexCompatible) :
    ∀ y ∈ regularLocus hbc,
      IsHolomorphicAt (fun y' : Y =>
        open Classical in
        if hy' : isRegularValue hbc y' then
          traceAtRegularValue hbc (fun x => η.toFun x) y' hy'
        else (0 : CotangentModelFiber ℂ)) y := by
  classical
  intro y hy_reg
  have hy : isRegularValue hbc y := hy_reg
  have hHol : IsHolomorphic f :=
    isHolomorphic_of_contMDiff hf (hasLocalKfoldRamification_of_contMDiff hf)
  have hloc_holo : IsHolomorphicAt
      (localTraceAtRegularValue hbc hHol η y hy) y :=
    localTraceAtRegularValue_holomorphic hbc hcompat hHol η y hy
  refine hloc_holo.congr_of_eventuallyEq ?_
  have hRegOpen : IsOpen (regularLocus hbc) := by
    have hfin : ({y : Y | ¬ isRegularValue hbc y}).Finite :=
      branchLocus_finite hbc
    have hC : IsClosed ({y : Y | ¬ isRegularValue hbc y}) := hfin.isClosed
    have hco : IsOpen ({y : Y | ¬ isRegularValue hbc y}ᶜ) := hC.isOpen_compl
    convert hco using 1
    ext z; simp [regularLocus]
  have hReg_mem : regularLocus hbc ∈ 𝓝 y := hRegOpen.mem_nhds hy_reg
  set S : Finset X := (hbc.finite_fiber y).toFinset with hS_def
  have hfiber_eq : ∀ {x : X}, x ∈ S ↔ x ∈ f ⁻¹' {y} := by
    intro x; rw [hS_def, Set.Finite.mem_toFinset]
  -- T2 separation gives raw pairwise disjoint nhds W₀ x.
  have hS_fin : (S : Set X).Finite := S.finite_toSet
  obtain ⟨W₀, hW₀_local, hW₀_disj⟩ := hS_fin.exists_pairwiseDisjoint_open_nhds
  -- For each x ∈ S, ramification index = 1, so the BCD provides U₀ x, V₀ x
  -- with f bijective from U₀ x to V₀ x and inverse identities. Build
  -- `W x := W₀ x ∩ U₀ x`: open, contains x (since x ∈ U₀ x and x ∈ W₀ x),
  -- pairwise disjoint (W₀'s are), and inside U₀ x so `hleft` applies for any
  -- x' ∈ W x giving `localInverseAt x hx_ram (f x') = x'`.
  -- Then use continuity of localInverseAt x at f x = y to find a Y-nhd V₁ x
  -- such that localInverseAt x hx_ram(V₁ x) ⊆ W x.
  have hper_x : ∀ x : X, x ∈ S → ∃ (Wx : Set X) (V₁ : Set Y),
        IsOpen Wx ∧ IsOpen V₁ ∧ x ∈ Wx ∧ y ∈ V₁ ∧
        (∀ x₁ ∈ S, ∀ x₂ ∈ S, x₁ ≠ x₂ → x = x₁ ∨ x = x₂ → True) ∧
        (∀ hx_ram : hbc.ramificationIndex x = 1,
          (∀ z ∈ V₁, f (hbc.localInverseAt x hx_ram z) = z ∧
                      hbc.localInverseAt x hx_ram z ∈ Wx) ∧
          (∀ x' ∈ Wx, hbc.localInverseAt x hx_ram (f x') = x')) ∧
        Wx ⊆ W₀ x := by
    intro x hxS
    have hx_fiber : x ∈ f ⁻¹' {y} := hfiber_eq.mp hxS
    have hx_ram : hbc.ramificationIndex x = 1 := hy x hx_fiber
    obtain ⟨U₀, V₀, hU₀_open, hV₀_open, hxU₀, hfxV₀, _hbij, hright, hleft⟩ :=
      hbc.localInverse_is_inverse hx_ram
    have hfx_eq : f x = y := hx_fiber
    -- Wx := W₀ x ∩ U₀: open, x ∈ Wx, Wx ⊆ U₀, Wx ⊆ W₀ x.
    let Wx : Set X := W₀ x ∩ U₀
    have hWx_open : IsOpen Wx := (hW₀_local x hxS).1.inter hU₀_open
    have hxWx : x ∈ Wx := ⟨(hW₀_local x hxS).2, hxU₀⟩
    have hWx_sub_U₀ : Wx ⊆ U₀ := fun _ h => h.2
    have hWx_sub_W₀ : Wx ⊆ W₀ x := fun _ h => h.1
    have hWx_pre : hbc.localInverseAt x hx_ram ⁻¹' Wx ∈ 𝓝 (f x) :=
      localInverseAt_preimage_mem_nhds hbc hcompat hHol x hx_ram hWx_open hxWx
    -- Get an open V₁'' ⊆ preimage of Wx, containing f x.
    obtain ⟨V₁'', hV₁''_sub, hV₁''_open, hyV₁''⟩ := mem_nhds_iff.mp hWx_pre
    refine ⟨Wx, V₀ ∩ V₁'', hWx_open, hV₀_open.inter hV₁''_open, hxWx, ?_, ?_, ?_, hWx_sub_W₀⟩
    · -- y ∈ V₀ ∩ V₁''
      refine ⟨?_, ?_⟩
      · rw [← hfx_eq]; exact hfxV₀
      · rw [← hfx_eq]; exact hyV₁''
    · intros; trivial
    · intro hx_ram'
      refine ⟨?_, ?_⟩
      · intro z ⟨hz_V₀, hz_V₁''⟩
        have h_eq_ram : hx_ram' = hx_ram := rfl
        refine ⟨?_, ?_⟩
        · rw [h_eq_ram]; exact hright z hz_V₀
        · rw [h_eq_ram]; exact hV₁''_sub hz_V₁''
      · intro x' hx'Wx
        have h_eq_ram : hx_ram' = hx_ram := rfl
        rw [h_eq_ram]
        exact hleft x' (hWx_sub_U₀ hx'Wx)
  -- Choose Wx, V₁ etc.
  choose! Wx V₁ hWx_open hV₁_open hxWx hyV₁ _hdisj_trivial hWx_inv hWx_sub_W₀
    using hper_x
  -- Pairwise disjointness of Wx (using hWx_sub_W₀).
  have hWx_disj : ∀ x₁ ∈ S, ∀ x₂ ∈ S, x₁ ≠ x₂ → Disjoint (Wx x₁) (Wx x₂) := by
    intro x₁ hx₁ x₂ hx₂ hne
    exact (hW₀_disj hx₁ hx₂ hne).mono (hWx_sub_W₀ x₁ hx₁) (hWx_sub_W₀ x₂ hx₂)
  -- V := ⋂ x ∈ S, V₁ x. Open nhd of y.
  have hV_int_nhds : (⋂ x ∈ (S : Set X), V₁ x) ∈ 𝓝 y := by
    refine (Filter.biInter_finset_mem S).mpr ?_
    intro x hxS
    exact (hV₁_open x hxS).mem_nhds (hyV₁ x hxS)
  -- Ω := ⋃ x ∈ S, Wx x. Open set in X containing fiber(y).
  let Ω : Set X := ⋃ x ∈ (S : Set X), Wx x
  have hΩ_open : IsOpen Ω :=
    isOpen_biUnion (fun x hxS => hWx_open x hxS)
  have hFiber_sub_Ω : f ⁻¹' {y} ⊆ Ω := by
    intro x hx_fib
    have hxS : x ∈ S := hfiber_eq.mpr hx_fib
    exact Set.mem_biUnion (Finset.mem_coe.mpr hxS) (hxWx x hxS)
  have hFiber_eventually : ∀ᶠ y' in 𝓝 y, f ⁻¹' {y'} ⊆ Ω :=
    eventually_fiber_subset_of_compact_T2 hHol.continuous hΩ_open hFiber_sub_Ω
  filter_upwards [hFiber_eventually, hV_int_nhds, hReg_mem] with
    y' hy'_fib hy'_V hy'_regset
  have hy'_reg : isRegularValue hbc y' := hy'_regset
  show localTraceAtRegularValue hbc hHol η y hy y' = _
  rw [dif_pos hy'_reg]
  have hx_ram_of_S : ∀ x ∈ S, hbc.ramificationIndex x = 1 := by
    intro x hxS; exact hy x (hfiber_eq.mp hxS)
  -- The local-inverse bijection φ.
  let φ : ∀ x : X, x ∈ S → X := fun x hxS =>
    hbc.localInverseAt x (hx_ram_of_S x hxS) y'
  have hy'_in_V₁ : ∀ x ∈ S, y' ∈ V₁ x := by
    intro x hxS
    exact (Set.mem_iInter₂.mp hy'_V) x (Finset.mem_coe.mpr hxS)
  have hφ_f : ∀ x : X, ∀ hxS : x ∈ S, f (φ x hxS) = y' := by
    intro x hxS
    have := ((hWx_inv x hxS) (hx_ram_of_S x hxS)).1 y' (hy'_in_V₁ x hxS)
    exact this.1
  have hφ_in_Wx : ∀ x : X, ∀ hxS : x ∈ S, φ x hxS ∈ Wx x := by
    intro x hxS
    have := ((hWx_inv x hxS) (hx_ram_of_S x hxS)).1 y' (hy'_in_V₁ x hxS)
    exact this.2
  have hφ_toFinset : ∀ x : X, ∀ hxS : x ∈ S,
      φ x hxS ∈ (hbc.finite_fiber y').toFinset := by
    intro x hxS
    rw [Set.Finite.mem_toFinset]
    exact hφ_f x hxS
  have hφ_inj : ∀ x₁ : X, ∀ hx₁ : x₁ ∈ S, ∀ x₂ : X, ∀ hx₂ : x₂ ∈ S,
      φ x₁ hx₁ = φ x₂ hx₂ → x₁ = x₂ := by
    intro x₁ hx₁ x₂ hx₂ heq
    by_contra hne
    have hdisj : Disjoint (Wx x₁) (Wx x₂) := hWx_disj x₁ hx₁ x₂ hx₂ hne
    have h1 : φ x₁ hx₁ ∈ Wx x₁ := hφ_in_Wx x₁ hx₁
    have h2 : φ x₂ hx₂ ∈ Wx x₂ := hφ_in_Wx x₂ hx₂
    rw [heq] at h1
    exact (Set.disjoint_iff.mp hdisj) ⟨h1, h2⟩
  have hφ_surj : ∀ x' ∈ (hbc.finite_fiber y').toFinset,
      ∃ (x : X) (hxS : x ∈ S), φ x hxS = x' := by
    intro x' hx'
    have hx'_fib : x' ∈ f ⁻¹' {y'} :=
      (Set.Finite.mem_toFinset _).mp hx'
    have hx'_in_Ω : x' ∈ Ω := hy'_fib hx'_fib
    rcases Set.mem_iUnion₂.mp hx'_in_Ω with ⟨x, hxS_coe, hx'_in_Wx⟩
    have hxS : x ∈ S := Finset.mem_coe.mp hxS_coe
    refine ⟨x, hxS, ?_⟩
    -- φ x hxS = localInverseAt x (hx_ram_of_S x hxS) y'.
    -- We need this = x'.  Since x' ∈ Wx x and f x' = y', and (Wx x, V₁ x) is
    -- a "section" pair with the left-inverse identity on Wx x:
    --   localInverseAt x hx_ram (f x') = x'  (from hWx_inv x hxS hx_ram .2).
    -- And f x' = y', so localInverseAt x hx_ram y' = x', as needed.
    have hfx' : f x' = y' := hx'_fib
    have hLI := ((hWx_inv x hxS) (hx_ram_of_S x hxS)).2 x' hx'_in_Wx
    -- hLI : hbc.localInverseAt x (hx_ram_of_S x hxS) (f x') = x'.
    show hbc.localInverseAt x (hx_ram_of_S x hxS) y' = x'
    rw [← hfx']; exact hLI
  -- Use Finset.sum_nbij' with i, j inverses.
  unfold localTraceAtRegularValue traceAtRegularValue
  -- choose: hφ_surj_choice extracts the unique x ∈ S from a fiber-point x'.
  -- For each x' ∈ fiber(y'), pick (xOfFib x', hxOfFib_mem) such that φ xOfFib x' (...) = x'.
  let xOfFib : ∀ x' : X, x' ∈ (hbc.finite_fiber y').toFinset → X :=
    fun x' hx' => (hφ_surj x' hx').choose
  let xOfFib_mem : ∀ x' : X, ∀ hx' : x' ∈ (hbc.finite_fiber y').toFinset,
      xOfFib x' hx' ∈ S := fun x' hx' => (hφ_surj x' hx').choose_spec.choose
  have xOfFib_eq : ∀ x' : X, ∀ hx' : x' ∈ (hbc.finite_fiber y').toFinset,
      φ (xOfFib x' hx') (xOfFib_mem x' hx') = x' :=
    fun x' hx' => (hφ_surj x' hx').choose_spec.choose_spec
  refine Finset.sum_bij'
    (i := fun (z : { x // x ∈ S }) (_ : z ∈ S.attach) =>
      (⟨φ z.1 z.2, hφ_toFinset z.1 z.2⟩ :
        { x // x ∈ (hbc.finite_fiber y').toFinset }))
    (j := fun (z' : { x // x ∈ (hbc.finite_fiber y').toFinset })
        (_ : z' ∈ (hbc.finite_fiber y').toFinset.attach) =>
      (⟨xOfFib z'.1 z'.2, xOfFib_mem z'.1 z'.2⟩ : { x // x ∈ S }))
    ?_ ?_ ?_ ?_ ?_
  · intro z _; exact Finset.mem_attach _ _
  · intro z' _; exact Finset.mem_attach _ _
  · intro z _
    apply Subtype.ext
    show xOfFib (φ z.1 z.2) (hφ_toFinset z.1 z.2) = z.1
    have hee := xOfFib_eq (φ z.1 z.2) (hφ_toFinset z.1 z.2)
    have hxof_S := xOfFib_mem (φ z.1 z.2) (hφ_toFinset z.1 z.2)
    exact hφ_inj _ hxof_S _ z.2 hee
  · intro z' _
    apply Subtype.ext
    show φ (xOfFib z'.1 z'.2) (xOfFib_mem z'.1 z'.2) = z'.1
    exact xOfFib_eq z'.1 z'.2
  · intro z _
    show localPullbackAt hbc hHol η z.1 (hy z.1 ((Set.Finite.mem_toFinset _).mp z.2)) y' =
      cotangentPushforward f (φ z.1 z.2) (η.toFun (φ z.1 z.2))
    unfold localPullbackAt
    rfl


private theorem traceForm_extension_per_BCD
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (⊤ : WithTop ℕ∞) f)
    (η : HolomorphicOneForm ℂ X)
    (hbc : BranchedCoverData X Y f)
    (hcompat : hbc.RamificationIndexCompatible) :
    ∃ τ : HolomorphicOneForm ℂ Y,
      ∀ (y : Y) (hy : isRegularValue hbc y),
        τ.toFun y = traceAtRegularValue hbc (fun x => η.toFun x) y hy := by
  classical
  have hOpen : IsOpen (regularLocus hbc) := by
    have hfin : ({y : Y | ¬ isRegularValue hbc y}).Finite :=
      branchLocus_finite hbc
    have hC : IsClosed ({y : Y | ¬ isRegularValue hbc y}) := hfin.isClosed
    have hco : IsOpen ({y : Y | ¬ isRegularValue hbc y}ᶜ) := hC.isOpen_compl
    convert hco using 1
    ext y; simp [regularLocus]
  have hDense : Dense (regularLocus hbc) := regularLocus_dense hbc
  have hCompl : (regularLocus hbc)ᶜ.Finite := by
    have h := branchLocus_finite hbc
    have heq : (regularLocus hbc)ᶜ = ({y : Y | ¬ isRegularValue hbc y}) := by
      ext y; simp [regularLocus]
    rw [heq]; exact h
  let g : Y → CotangentModelFiber ℂ := fun y' =>
    if hy' : isRegularValue hbc y' then
      traceAtRegularValue hbc (fun x => η.toFun x) y' hy'
    else (0 : CotangentModelFiber ℂ)
  have hHol : ∀ y ∈ regularLocus hbc,
      IsHolomorphicAt (fun y' : Y => g y') y :=
    regularLocus_dite_trace_holomorphicAt f hf η hbc hcompat
  have hBdd : ∀ y₀ ∈ (regularLocus hbc)ᶜ,
      ∃ (U : Set Y) (M : ℝ), IsOpen U ∧ y₀ ∈ U ∧
        ∀ y ∈ U ∩ regularLocus hbc, ‖g y‖ ≤ M := by
    intro y₀ hy₀
    have hy₀_branch : ¬ isRegularValue hbc y₀ := by
      have : y₀ ∉ regularLocus hbc := hy₀
      simpa [regularLocus] using this
    obtain ⟨U, M, hU_open, hy₀_in_U, hbound⟩ :=
      traceAtRegularValue_locally_bounded_near_branch_values f hf η hbc hcompat y₀
        hy₀_branch
    refine ⟨U, M, hU_open, hy₀_in_U, ?_⟩
    rintro y ⟨hyU, hyReg⟩
    have hyReg' : isRegularValue hbc y := hyReg
    have hg : g y = traceAtRegularValue hbc (fun x => η.toFun x) y hyReg' := by
      show (if hy' : isRegularValue hbc y then
              traceAtRegularValue hbc (fun x => η.toFun x) y hy'
            else (0 : CotangentModelFiber ℂ)) = _
      rw [dif_pos hyReg']
    rw [hg]
    exact hbound y hyU hyReg'
  obtain ⟨τ, hτ⟩ :=
    holomorphicOneForm_of_regularLocus_holomorphic_branchLocus_bounded
      (regularLocus hbc) hOpen hDense hCompl g hHol hBdd
  refine ⟨τ, ?_⟩
  intro y hy
  have hyReg : y ∈ regularLocus hbc := hy
  rw [hτ y hyReg]
  show (if hy' : isRegularValue hbc y then
          traceAtRegularValue hbc (fun x => η.toFun x) y hy'
        else (0 : CotangentModelFiber ℂ)) = _
  rw [dif_pos hy]

omit [T2Space X] [CompactSpace X] [ConnectedSpace X] [StableChartAt ℂ X]
  [T2Space Y] [CompactSpace Y] [ConnectedSpace Y] [StableChartAt ℂ Y] in
/--
**Auxiliary (analytic continuation across canonical-BCD branch
values).** If `τ : HolomorphicOneForm ℂ Y` matches the canonical
fibre trace on `regularLocus hbc0`, and if `y` is a branch value of
the canonical BCD `hbc0` but a regular value of some other BCD
`hbc`, then `τ.toFun y = traceAtRegularValue hbc … y …`.

Both sides are continuous functions of `y` on a chart-local
neighbourhood of `y` (for τ, by holomorphicity of the section; for
the right-hand side, by the chart-local trivialisation of the
finite fibre sum at unramified preimages). On the dense joint
regular locus around `y`, they coincide pointwise via Provider (4),
so they coincide at `y` by continuity.
-/
theorem traceForm_extension_at_branch_of_canonical_BCD
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (⊤ : WithTop ℕ∞) f)
    (η : HolomorphicOneForm ℂ X)
    (hbc0 hbc : BranchedCoverData X Y f)
    (hcompat0 : hbc0.RamificationIndexCompatible)
    (hcompat : hbc.RamificationIndexCompatible)
    (y : Y) (hy0_branch : ¬ isRegularValue hbc0 y)
    (hy_reg : isRegularValue hbc y)
    (τ : HolomorphicOneForm ℂ Y)
    (_hτ : ∀ (y' : Y) (hy' : isRegularValue hbc0 y'),
        τ.toFun y' = traceAtRegularValue hbc0 (fun x => η.toFun x) y' hy') :
    τ.toFun y = traceAtRegularValue hbc (fun x => η.toFun x) y hy_reg := by
  -- The hypotheses are contradictory: any branch point of hbc0 must be a branch
  -- point of every compatible BCD (both equal mapAnalyticOrderAt f).
  exfalso
  -- Unfold ¬ isRegularValue to extract a ramified preimage.
  unfold isRegularValue at hy0_branch
  push_neg at hy0_branch
  obtain ⟨x, hx_mem, hx_ram⟩ := hy0_branch
  -- IsHolomorphicAt at x, from contMDiff f.
  have hfx : IsHolomorphicAt f x :=
    (isHolomorphicBasic_of_contMDiff hf).holomorphicAt x
  -- Compatibility on both BCDs identifies ramificationIndex with mapAnalyticOrderAt.
  have h0 : hbc0.ramificationIndex x = mapAnalyticOrderAt f x := hcompat0 x hfx
  have h1 : hbc.ramificationIndex x = mapAnalyticOrderAt f x := hcompat x hfx
  -- hy_reg says hbc.ramificationIndex x = 1.
  have hreg : hbc.ramificationIndex x = 1 := hy_reg x hx_mem
  -- Combine: hbc0.ramificationIndex x = 1 but also ≠ 1. Contradiction.
  exact hx_ram (h0.trans (h1.symm.trans hreg))

/--
**Narrow classical leaf: trace-form holomorphic extension.** For a
nonconstant smooth map `f : X → Y` between compact Riemann surfaces
and a nonzero holomorphic 1-form `η` on `X`, there exists a global
holomorphic 1-form `τ` on `Y` whose pointwise values agree with the
finite local fibre sum `traceAtRegularValue` at every regular value
of every compatible branched-cover datum.

The first three are combined in the private helper
`traceForm_extension_per_BCD` to produce a τ tied to the canonical
BCD; the fourth lifts agreement to *all* BCDs at any regular value
of `hbc0`; the auxiliary lifts to regular values not regular for
`hbc0` via analytic continuation.
-/
theorem traceForm_global_extension
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (⊤ : WithTop ℕ∞) f)
    (η : HolomorphicOneForm ℂ X) (_hη : η ≠ 0)
    (hnonconst : ¬ ∃ y₀, ∀ x, f x = y₀) :
    ∃ τ : HolomorphicOneForm ℂ Y,
      ∀ (hbc : BranchedCoverData X Y f) (_hcompat : hbc.RamificationIndexCompatible)
        (y : Y) (hy : isRegularValue hbc y),
        τ.toFun y = traceAtRegularValue hbc (fun x => η.toFun x) y hy := by
  classical
  set hkfold := hasLocalKfoldRamification_of_contMDiff hf
  set hw := hasWeightedFiberConservation_of_contMDiff hf
  set hHol := isHolomorphic_of_contMDiff hf hkfold
  set hbc0 := JacobianChallenge.Blueprint.branchedCoverData_of_nonconstant_holomorphic
    hHol hw hnonconst with hbc0_def
  have hcompat0 :=
    JacobianChallenge.Blueprint.branchedCoverData_of_nonconstant_holomorphic_compatible
      hHol hw hnonconst
  -- For one fixed BCD `hbc0`, the per-BCD provider gives τ.
  obtain ⟨τ, hτ0⟩ := traceForm_extension_per_BCD f hf η hbc0 hcompat0
  refine ⟨τ, ?_⟩
  intro hbc hcompat y hy
  by_cases hy0 : isRegularValue hbc0 y
  · rw [hτ0 y hy0]
    exact (traceAtRegularValue_BCD_invariance η hbc0 hbc y hy0 hy).symm
  · exact traceForm_extension_at_branch_of_canonical_BCD f hf η hbc0 hbc
      hcompat0 hcompat y hy0 hy τ hτ0

/--
**Narrow trace construction provider (nonconstant nonzero case).**

The remaining classical content lives entirely inside the strictly
smaller leaf `traceForm_global_extension`.
-/
noncomputable def traceFormsConstructionData_nonconstant_nonzero_provider
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (⊤ : WithTop ℕ∞) f)
    (η : HolomorphicOneForm ℂ X) (hη : η ≠ 0)
    (hnonconst : ¬ ∃ y₀, ∀ x, f x = y₀) :
    TraceFormsConstructionData f hf η :=
  let hext := traceForm_global_extension (f := f) (hf := hf) η hη hnonconst
  { traceForm := hext.choose
    regular_spec := hext.choose_spec
    map_zero_spec := fun hzero => (hη hzero).elim }

/--
**The trace construction provider.** Three-way case split:

* `η = 0` — fully proved via `traceFormsConstructionData_zero`;
* `η ≠ 0` and `f` constant — fully proved via
  `traceFormsConstructionData_constant`;
* `η ≠ 0` and `f` nonconstant — delegates to the strictly narrower
  analytic leaf
  `traceFormsConstructionData_nonconstant_nonzero_provider`.
-/
noncomputable def traceFormsConstructionData_provider
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (⊤ : WithTop ℕ∞) f)
    (η : HolomorphicOneForm ℂ X) :
    TraceFormsConstructionData f hf η := by
  classical
  by_cases hη : η = 0
  · -- Zero-input case: fully proved. Cast the η-specialized data back to η.
    cases hη
    exact traceFormsConstructionData_zero f hf
  · by_cases hconst : ∃ y₀, ∀ x, f x = y₀
    · exact traceFormsConstructionData_constant f hf η hconst hη
    · exact traceFormsConstructionData_nonconstant_nonzero_provider f hf η hη hconst


noncomputable def traceFormsBundled
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (⊤ : WithTop ℕ∞) f)
    (η : HolomorphicOneForm ℂ X) : HolomorphicOneForm ℂ Y :=
  (traceFormsConstructionData_provider f hf η).traceForm

-- The linear trace map `traceFormsBundledLM` is defined later in this
-- file, after the identity principle `holomorphicOneForm_ext_on`.

/- **Identity principle for holomorphic 1-forms.**
Two holomorphic 1-forms that agree on a dense set of a connected Riemann
surface are equal everywhere. -/
omit [ConnectedSpace Y] in
theorem holomorphicOneForm_ext_on
    {s : Set Y} (hs : Dense s)
    {ω₁ ω₂ : HolomorphicOneForm ℂ Y} (h : ∀ y ∈ s, ω₁.toFun y = ω₂.toFun y) :
    ω₁ = ω₂ := by
  apply ContMDiffSection.ext
  intro y
  let δ : HolomorphicOneForm ℂ Y := ω₁ - ω₂
  have hcont : Continuous (ContMDiffSection.fiberNorm δ) :=
    holomorphicOneForm_fiberNorm_continuous Y δ
  have hzero_on : Set.EqOn (ContMDiffSection.fiberNorm δ) (fun _ : Y => (0 : ℝ)) s := by
    intro z hz
    have hzfun : δ.toFun z = 0 := by
      dsimp [δ]
      change ((ω₁ - ω₂ : HolomorphicOneForm ℂ Y) : ∀ y, _) z = 0
      rw [ContMDiffSection.coe_sub]
      exact sub_eq_zero.mpr (h z hz)
    simp [ContMDiffSection.fiberNorm, hzfun]
  have hzero_all : ContMDiffSection.fiberNorm δ = fun _ : Y => (0 : ℝ) :=
    Continuous.ext_on hs hcont continuous_const hzero_on
  have hyzero : δ.toFun y = 0 := by
    have hn : ‖δ.toFun y‖ = 0 := by
      simpa [ContMDiffSection.fiberNorm] using congrFun hzero_all y
    exact norm_eq_zero.mp hn
  dsimp [δ] at hyzero
  change ((ω₁ - ω₂ : HolomorphicOneForm ℂ Y) : ∀ y, _) y = 0 at hyzero
  rw [ContMDiffSection.coe_sub] at hyzero
  exact sub_eq_zero.mp hyzero

/--
Minimal trace input used by local linearity and regular-value
assemblies.  This separates the specification needed downstream from
the construction of the global bundled trace form.
-/
structure TraceFormsRegularSpec
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (⊤ : WithTop ℕ∞) f) where
  /-- Trace sends the zero form to zero. -/
  map_zero : traceFormsBundled f hf 0 = 0
  /-- At regular values, trace agrees with the finite local fiber sum. -/
  apply_fun_regular :
    ∀ (hbc : BranchedCoverData X Y f) (_hcompat : hbc.RamificationIndexCompatible)
      (η : HolomorphicOneForm ℂ X)
      (y : Y) (hy : isRegularValue hbc y),
      (traceFormsBundled f hf η).toFun y =
        traceAtRegularValue hbc (fun x => η.toFun x) y hy

/--
Private helper: in the constant-map case, the construction-data
provider for any input form `η` reduces to
`traceFormsConstructionData_constant` (or
`traceFormsConstructionData_zero` if `η = 0`); in either case, the
resulting `traceForm` is the zero form on `Y`.
-/
theorem traceFormsBundled_eq_zero_of_constant
    {f : X → Y} {hf : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (⊤ : WithTop ℕ∞) f}
    (η : HolomorphicOneForm ℂ X) (hconst : ∃ y₀, ∀ x, f x = y₀) :
    traceFormsBundled f hf η = 0 := by
  classical
  by_cases hη : η = 0
  · subst hη
    change (traceFormsConstructionData_provider f hf (0 : HolomorphicOneForm ℂ X)).traceForm = 0
    exact (traceFormsConstructionData_provider f hf 0).map_zero_spec rfl
  · change (traceFormsConstructionData_provider f hf η).traceForm = 0
    rw [show traceFormsConstructionData_provider f hf η =
      traceFormsConstructionData_constant f hf η hconst hη from by
        unfold traceFormsConstructionData_provider
        simp [hη, hconst]]
    rfl

/--
The linear trace map on holomorphic 1-forms.

Linearity is proved by the standard "dense agreement at regular values"
trick: in the constant-map case both sides are zero
(`traceFormsBundled_eq_zero_of_constant`); in the nonconstant case, the
constructed trace forms agree with `traceAtRegularValue` on the dense
regular locus of the canonical branched-cover datum, and
`traceAtRegularValue` is already linear (via `traceAtRegularValue_add`
and `traceAtRegularValue_smul`). The identity principle
(`holomorphicOneForm_ext_on (regularLocus_dense hbc)`) then promotes
agreement on the regular locus to agreement everywhere.
-/
noncomputable def traceFormsBundledLM
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (⊤ : WithTop ℕ∞) f) :
    HolomorphicOneForm ℂ X →ₗ[ℂ] HolomorphicOneForm ℂ Y where
  toFun η := traceFormsBundled f hf η
  map_add' η ζ := by
    classical
    by_cases hconst : ∃ y₀, ∀ x, f x = y₀
    · rw [traceFormsBundled_eq_zero_of_constant η hconst,
          traceFormsBundled_eq_zero_of_constant ζ hconst,
          traceFormsBundled_eq_zero_of_constant (η + ζ) hconst,
          add_zero]
    · set hkfold := hasLocalKfoldRamification_of_contMDiff hf
      set hw := hasWeightedFiberConservation_of_contMDiff hf
      set hHol := isHolomorphic_of_contMDiff hf hkfold
      set hbc := JacobianChallenge.Blueprint.branchedCoverData_of_nonconstant_holomorphic
        hHol hw hconst
      have hcompat :=
        JacobianChallenge.Blueprint.branchedCoverData_of_nonconstant_holomorphic_compatible
          hHol hw hconst
      apply holomorphicOneForm_ext_on (regularLocus_dense hbc)
      intro y hy
      have hη_reg := (traceFormsConstructionData_provider f hf η).regular_spec hbc hcompat y hy
      have hζ_reg := (traceFormsConstructionData_provider f hf ζ).regular_spec hbc hcompat y hy
      have hηζ_reg := (traceFormsConstructionData_provider f hf (η + ζ)).regular_spec hbc hcompat y hy
      change (traceFormsConstructionData_provider f hf (η + ζ)).traceForm.toFun y =
        ((traceFormsConstructionData_provider f hf η).traceForm +
          (traceFormsConstructionData_provider f hf ζ).traceForm).toFun y
      rw [hηζ_reg]
      change _ = ((traceFormsConstructionData_provider f hf η).traceForm.toFun +
          (traceFormsConstructionData_provider f hf ζ).traceForm.toFun) y
      simp only [Pi.add_apply]
      rw [hη_reg, hζ_reg]
      have h_eq : (fun x : X => (η + ζ).toFun x) =
          (fun x => η.toFun x + ζ.toFun x) := by
        funext x
        show ((η + ζ : HolomorphicOneForm ℂ X) : ∀ y, _) x = _
        rw [ContMDiffSection.coe_add]
        rfl
      rw [h_eq]
      exact traceAtRegularValue_add hbc (fun x => η.toFun x) (fun x => ζ.toFun x) y hy
  map_smul' k η := by
    classical
    by_cases hconst : ∃ y₀, ∀ x, f x = y₀
    · show traceFormsBundled f hf (k • η) = k • traceFormsBundled f hf η
      rw [traceFormsBundled_eq_zero_of_constant η hconst,
          traceFormsBundled_eq_zero_of_constant (k • η) hconst]
      have h0 : (k • (0 : HolomorphicOneForm ℂ Y)) = 0 := by
        apply ContMDiffSection.ext
        intro y
        change ((k • (0 : HolomorphicOneForm ℂ Y)) : ∀ z, _) y = _
        rw [ContMDiffSection.coe_smul]
        simp
      exact h0.symm
    · set hkfold := hasLocalKfoldRamification_of_contMDiff hf
      set hw := hasWeightedFiberConservation_of_contMDiff hf
      set hHol := isHolomorphic_of_contMDiff hf hkfold
      set hbc := JacobianChallenge.Blueprint.branchedCoverData_of_nonconstant_holomorphic
        hHol hw hconst
      have hcompat :=
        JacobianChallenge.Blueprint.branchedCoverData_of_nonconstant_holomorphic_compatible
          hHol hw hconst
      show traceFormsBundled f hf (k • η) = k • traceFormsBundled f hf η
      apply holomorphicOneForm_ext_on (regularLocus_dense hbc)
      intro y hy
      have hη_reg := (traceFormsConstructionData_provider f hf η).regular_spec hbc hcompat y hy
      have hkη_reg := (traceFormsConstructionData_provider f hf (k • η)).regular_spec hbc hcompat y hy
      change (traceFormsConstructionData_provider f hf (k • η)).traceForm.toFun y =
        (k • (traceFormsConstructionData_provider f hf η).traceForm).toFun y
      rw [hkη_reg]
      change _ = (k • (traceFormsConstructionData_provider f hf η).traceForm.toFun) y
      simp only [Pi.smul_apply]
      rw [hη_reg]
      have h_eq : (fun x : X => (k • η).toFun x) =
          (fun x => k • η.toFun x) := by
        funext x
        show ((k • η : HolomorphicOneForm ℂ X) : ∀ y, _) x = _
        rw [ContMDiffSection.coe_smul]
        rfl
      rw [h_eq]
      exact traceAtRegularValue_smul hbc k (fun x => η.toFun x) y hy

end JacobianChallenge.HolomorphicForms
