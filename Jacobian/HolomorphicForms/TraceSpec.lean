import Jacobian.HolomorphicForms.Defs
import Jacobian.HolomorphicForms.ChartedSpaceComplexPoints
import Jacobian.HolomorphicForms.CompactRiemannSurface
import Jacobian.HolomorphicForms.SectionFiberNorm
import Jacobian.HolomorphicForms.HolomorphicMap
import Jacobian.HolomorphicForms.BranchedCover
import Jacobian.HolomorphicForms.ToFunApplyVec
import Jacobian.HolomorphicForms.PullbackBundled
import Jacobian.HolomorphicForms.TangentSpaceComplexBridge
import Jacobian.TraceDegree.TraceDefinition
import Jacobian.Periods.TrivializationContinuousLinearMapAt
import Jacobian.Blueprint.Sec02.BranchedDegreeFromHolomorphic
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Geometry.Manifold.VectorBundle.Basic
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Topology.VectorBundle.Constructions
import Mathlib.Topology.VectorBundle.Hom
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.RingTheory.RootsOfUnity.Complex

/-!
# Trace form specification interface

This file contains the minimal trace object and regular-value
specification needed by both the analytic degree API and the bundled
trace API.  It deliberately does not import `TraceDegree.AnalyticDegree`,
so the degree layer can package trace laws without creating an import
cycle.
-/

namespace JacobianChallenge.HolomorphicForms

open scoped Manifold ContDiff Topology Classical NNReal ENNReal
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
      ∀ y ∈ V, ∀ (_hy : isRegularValue hbc y),
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

omit [T2Space X] [CompactSpace X] [ConnectedSpace X] [IsManifold 𝓘(ℂ, ℂ) ω X]
  [StableChartAt ℂ X] [T2Space Y] [CompactSpace Y] [ConnectedSpace Y]
  [IsManifold 𝓘(ℂ, ℂ) ω Y] [StableChartAt ℂ Y] in
/--
**Chart-local `z^k` form extraction (Commit A — sorry-free helper).**

Given a holomorphic `f : X → Y` between charted-on-`ℂ` spaces and a
point `x₀ : X` with `mapAnalyticOrderAt f x₀ = k ≥ 1`, this helper
exposes the chart-local power form: there exists an analytic function
`φ : ℂ → ℂ` with `φ z₀ = 0` (where `z₀ := chartAt ℂ x₀ x₀`),
`deriv φ z₀ ≠ 0`, and `chartLocalAt f x₀ z = c₀ + φ(z)^k` near `z₀`
(where `c₀ := chartAt ℂ (f x₀) (f x₀)`).

This packages Mathlib's `exists_local_power_form` for the project's
chart-local setup. It is the foundational step for the roots-of-unity
cancellation in `ramifiedKfoldSum_locally_bounded`: under this form,
the `k` preimages of a nearby chart-target point `c₀ + w` are exactly
`φ⁻¹(ζ_k^j ⋅ w^{1/k})` for `j = 0..k-1`.

This is **Commit A** in the 3-commit discharge of
`ramifiedKfoldSum_locally_bounded`. Commit B will use this `φ` to
compute the chart-pullback of `cotangentPushforward`; Commit C will
apply the roots-of-unity cancellation to bound the partial sum.
-/
private theorem chartLocal_zPow_form_of_ramified
    [IsManifold 𝓘(ℂ, ℂ) ω X] [IsManifold 𝓘(ℂ, ℂ) ω Y]
    {f : X → Y} {x₀ : X} (hf : IsHolomorphicAt f x₀)
    {k : ℕ} (hk : 0 < k) (hram : mapAnalyticOrderAt f x₀ = k) :
    ∃ φ : ℂ → ℂ,
      AnalyticAt ℂ φ (chartAt ℂ x₀ x₀) ∧
      φ (chartAt ℂ x₀ x₀) = 0 ∧
      deriv φ (chartAt ℂ x₀ x₀) ≠ 0 ∧
      ∀ᶠ z in 𝓝 (chartAt ℂ x₀ x₀),
        chartLocalAt f x₀ z - chartAt ℂ (f x₀) (f x₀) = φ z ^ k := by
  -- Set up the chart-local map shifted by c₀ so its order at z₀ is k.
  set z₀ := chartAt ℂ x₀ x₀ with hz₀_def
  set c₀ := chartAt ℂ (f x₀) (f x₀) with hc₀_def
  set g : ℂ → ℂ := fun z => chartLocalAt f x₀ z - c₀ with hg_def
  -- g is analytic at z₀.
  have hg_an : AnalyticAt ℂ g z₀ := by
    have h_chart_an : AnalyticAt ℂ (chartLocalAt f x₀) z₀ := hf
    exact h_chart_an.sub analyticAt_const
  -- g z₀ = 0.
  have hg_z₀ : g z₀ = 0 := by
    show chartLocalAt f x₀ z₀ - c₀ = 0
    -- chartLocalAt f x₀ z₀ = chartAt ℂ (f x₀) (f ((chartAt ℂ x₀).symm z₀))
    --                     = chartAt ℂ (f x₀) (f x₀) = c₀.
    have h_inv : (chartAt ℂ x₀).symm z₀ = x₀ := by
      show (chartAt ℂ x₀).symm (chartAt ℂ x₀ x₀) = x₀
      exact (chartAt ℂ x₀).left_inv (mem_chart_source ℂ x₀)
    show chartAt ℂ (f x₀) (f ((chartAt ℂ x₀).symm z₀)) - c₀ = 0
    rw [h_inv]
    show chartAt ℂ (f x₀) (f x₀) - c₀ = 0
    rw [hc₀_def]
    ring
  -- analyticOrderNatAt g z₀ = k.
  have hord_nat : analyticOrderNatAt g z₀ = k := by
    show analyticOrderNatAt
      (fun z => chartLocalAt f x₀ z - chartAt ℂ (f x₀) (f x₀)) z₀ = k
    simpa [mapAnalyticOrderAt, hz₀_def, hc₀_def] using hram
  -- analyticOrderAt g z₀ ≠ ⊤ (follows from k ≥ 1 and order = k).
  have hord_ne_top : analyticOrderAt g z₀ ≠ ⊤ := by
    intro htop
    have hnat : analyticOrderNatAt g z₀ = 0 := by
      simp [analyticOrderNatAt, htop]
    omega
  -- Apply exists_local_power_form.
  obtain ⟨φ, hφ_an, hφ_z₀, hφ_deriv, hφ_eq⟩ :=
    AnalyticLocalMapping.exists_local_power_form g z₀ k hk hg_an hg_z₀
      hord_nat hord_ne_top
  refine ⟨φ, hφ_an, hφ_z₀, hφ_deriv, ?_⟩
  filter_upwards [hφ_eq] with z hz
  show chartLocalAt f x₀ z - c₀ = φ z ^ k
  exact hz

omit [T2Space X] [CompactSpace X] [ConnectedSpace X] [IsManifold 𝓘(ℂ, ℂ) ω X]
  [StableChartAt ℂ X] [T2Space Y] [CompactSpace Y] [ConnectedSpace Y]
  [IsManifold 𝓘(ℂ, ℂ) ω Y] [StableChartAt ℂ Y] in
/--
**Chart-local derivative formula via chain rule (Commit B — sorry-free helper).**

Given the chart-local `z^k` form `chartLocalAt f x₀ z - c₀ = φ(z)^k`
(produced by `chartLocal_zPow_form_of_ramified`), the chain rule
yields the explicit derivative:

```
deriv (chartLocalAt f x₀) z = (k : ℂ) * φ(z)^(k - 1) * deriv φ z
```

on a neighbourhood of `z₀ := chartAt ℂ x₀ x₀`.

This formula is the chart-local expression of `mfderiv f x_j` at any
nearby preimage `x_j`; its inverse `(mfderiv)⁻¹` is the divergent
factor that `cotangentPushforward f x_j` post-composes with. The
explicit `k * φ^{k-1}` shape is exactly what the roots-of-unity
cancellation in Commit C will exploit.

This is **Commit B** in the 3-commit discharge of
`ramifiedKfoldSum_locally_bounded`. Combined with Commit A
(`chartLocal_zPow_form_of_ramified`), it provides the full chart-local
representation needed by Commit C.
-/
private theorem chartLocal_deriv_of_zPow_form
    {f : X → Y} {x₀ : X} {k : ℕ} (_hk : 0 < k)
    {φ : ℂ → ℂ} (hφ_an : AnalyticAt ℂ φ (chartAt ℂ x₀ x₀))
    (hφ_eq : ∀ᶠ z in 𝓝 (chartAt ℂ x₀ x₀),
      chartLocalAt f x₀ z - chartAt ℂ (f x₀) (f x₀) = φ z ^ k) :
    ∀ᶠ z in 𝓝 (chartAt ℂ x₀ x₀),
      deriv (chartLocalAt f x₀) z =
        (k : ℂ) * φ z ^ (k - 1) * deriv φ z := by
  -- Rewrite: chartLocalAt f x₀ z = c₀ + φ(z)^k near z₀, hence
  --   deriv (chartLocalAt f x₀) z = deriv (fun z => φ(z)^k) z
  --                               = k * φ(z)^{k-1} * deriv φ z.
  set z₀ := chartAt ℂ x₀ x₀ with hz₀_def
  -- φ is analytic on a nhd of z₀ (eventually_analyticAt).
  have hφ_eventually_an : ∀ᶠ z in 𝓝 z₀, AnalyticAt ℂ φ z := hφ_an.eventually_analyticAt
  -- The eventually-equation gives equal derivatives via Filter.EventuallyEq.deriv_eq.
  -- But we need to handle this pointwise: at each z in the small nhd, the eq holds
  -- ON A NHD of z, not just at z.
  filter_upwards [hφ_eq, hφ_eventually_an,
    eventually_mem_nhds_iff.mpr hφ_eq, eventually_mem_nhds_iff.mpr hφ_eventually_an]
    with z hz_eq hz_an hz_eq_nhd hz_an_nhd
  -- Use hz_eq_nhd : ∀ᶠ w in 𝓝 z, chartLocalAt f x₀ w - c₀ = φ w ^ k
  have h_eventually_eq :
      (fun w => chartLocalAt f x₀ w) =ᶠ[𝓝 z]
        (fun w => chartAt ℂ (f x₀) (f x₀) + φ w ^ k) := by
    filter_upwards [hz_eq_nhd] with w hw
    linear_combination hw
  rw [Filter.EventuallyEq.deriv_eq h_eventually_eq]
  -- Now compute deriv (fun w => c₀ + φ w ^ k) z.
  have hφ_diff : DifferentiableAt ℂ φ z := hz_an.differentiableAt
  rw [deriv_const_add, deriv_fun_pow hφ_diff k]

omit [T2Space X] [CompactSpace X] [ConnectedSpace X] [IsManifold 𝓘(ℂ, ℂ) ω X]
  [StableChartAt ℂ X] [T2Space Y] [CompactSpace Y] [ConnectedSpace Y]
  [IsManifold 𝓘(ℂ, ℂ) ω Y] [StableChartAt ℂ Y] in
/--
**Manifold derivative ↔ chart-local derivative bridge (Commit C1 —
sorry-free helper).**

For a smooth `f : X → Y` and `x` in the source of `chartAt ℂ x₀`
(so that `chartAt ℂ x = chartAt ℂ x₀` by `StableChartAt`), the
manifold derivative `mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) f x` coincides with
multiplication-by-deriv:

```
mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) f x =
  ContinuousLinearMap.toSpanSingleton ℂ
    (deriv (chartLocalAt f x₀) (chartAt ℂ x₀ x))
```

(after the `chart ℂ x = chart ℂ x₀` identification on the
domain side; the Y-side identification `chart ℂ (f x) = chart ℂ (f x₀)`
also requires `StableChartAt ℂ Y` and `f x ∈ (chart ℂ (f x₀)).source`).

This is **Commit C1** in the 4-commit C-sub-split discharge of
`ramifiedKfoldSum_locally_bounded`. It is the foundational
manifold-derivative bridge: combined with Commit B's chart-local
derivative formula, it identifies `mfderiv f x` with
`k * φ(z)^{k-1} * deriv φ z`, the explicit ramified-singular factor
in `cotangentPushforward`.
-/
private theorem mfderiv_eq_toSpanSingleton_chartLocal_deriv
    {f : X → Y} (hf : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (⊤ : WithTop ℕ∞) f)
    (x₀ : X) :
    ∀ᶠ x in 𝓝 x₀, mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) f x =
      ContinuousLinearMap.toSpanSingleton ℂ
        (deriv (chartLocalAt f x) (chartAt ℂ x x)) := by
  -- Reduce to MDifferentiableAt + mfderiv computation pointwise.
  have h_mdiff : ∀ x : X, MDifferentiableAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) f x := fun x => by
    have h_ne_zero : (⊤ : WithTop ℕ∞) ≠ 0 := by decide
    exact (hf.contMDiffAt).mdifferentiableAt h_ne_zero
  filter_upwards with x
  -- `mfderiv f x = fderiv ℂ (chartLocalAt f x) (chart x x)` by definition.
  rw [(h_mdiff x).mfderiv]
  -- writtenInExtChartAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) x f = chartLocalAt f x.
  show fderivWithin ℂ
    ((chartAt ℂ (f x)) ∘ f ∘ (chartAt ℂ x).symm)
    (Set.range 𝓘(ℂ, ℂ)) ((chartAt ℂ x) x) =
    ContinuousLinearMap.toSpanSingleton ℂ
      (deriv (chartLocalAt f x) (chartAt ℂ x x))
  -- range 𝓘(ℂ, ℂ) = univ; fderivWithin univ = fderiv.
  rw [ModelWithCorners.range_eq_univ, fderivWithin_univ]
  -- Goal: fderiv ℂ (chartLocalAt f x) (chart x x) =
  --   toSpanSingleton ℂ (deriv (chartLocalAt f x) (chart x x)).
  exact toSpanSingleton_deriv.symm

omit [T2Space X] [CompactSpace X] [ConnectedSpace X] [IsManifold 𝓘(ℂ, ℂ) ω X]
  [StableChartAt ℂ X] [T2Space Y] [CompactSpace Y] [ConnectedSpace Y]
  [IsManifold 𝓘(ℂ, ℂ) ω Y] [StableChartAt ℂ Y] in
/--
**Inverse uniqueness for `IsIso` (Commit C2 — local helper).**

Two `IsIso` witnesses for the same continuous linear map have equal
`inv` fields. Re-proved locally so the C2/C3/C4 cancellation chain
does not have to import `Jacobian.TraceDegree.PullbackBasis`.
-/
private theorem IsIso.inv_unique_local
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    {φ : E →L[ℂ] F} (h₁ h₂ : IsIso φ) : h₁.inv = h₂.inv := by
  calc h₁.inv
      = h₁.inv.comp (ContinuousLinearMap.id ℂ F) := by ext x; simp
    _ = h₁.inv.comp (φ.comp h₂.inv) := by rw [h₂.right_inv]
    _ = (h₁.inv.comp φ).comp h₂.inv := by
        ext x; simp [ContinuousLinearMap.comp_apply]
    _ = (ContinuousLinearMap.id ℂ E).comp h₂.inv := by rw [h₁.left_inv]
    _ = h₂.inv := by ext x; simp

omit [T2Space X] [CompactSpace X] [ConnectedSpace X] [IsManifold 𝓘(ℂ, ℂ) ω X]
  [StableChartAt ℂ X] [T2Space Y] [CompactSpace Y] [ConnectedSpace Y]
  [IsManifold 𝓘(ℂ, ℂ) ω Y] [StableChartAt ℂ Y] in
/--
**Explicit form of the `mfderiv` inverse at any holomorphic point
(Commit C2 — sorry-free helper).**

For any `IsIso` witness `hiso` of `mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) f x` where
`f` is holomorphic, the inverse equals the explicit
`toSpanSingleton ℂ ((deriv (chartLocalAt f x) (chartAt ℂ x x))⁻¹)`.
This combines the `mfderiv = toSpanSingleton ℂ a` identity (always
holds for holomorphic `f`) with the `inv_unique_local` lemma and the
explicit `IsIso` witness whose `inv` field is precisely the
`toSpanSingleton ℂ a⁻¹` form. The non-vanishing of `a` is derived from
the existence of `hiso` itself (a zero CLM has no inverse).

This is **Commit C2** in the 4-commit C-sub-split discharge of
`ramifiedKfoldSum_locally_bounded`. It is the explicit chart-local
inverse, which feeds the explicit single-summand formula in C2.1
(`cotangentPushforward_eq_comp_toSpanSingleton_inv`).
-/
private theorem mfderiv_isIso_inv_eq_toSpanSingleton_inv
    {f : X → Y} (hHol : IsHolomorphic f) (x : X)
    (hiso : IsIso (mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) f x)) :
    hiso.inv =
      (ContinuousLinearMap.toSpanSingleton ℂ
        ((deriv (chartLocalAt f x) (chartAt ℂ x x))⁻¹) :
        TangentSpace 𝓘(ℂ, ℂ) (f x) →L[ℂ] TangentSpace 𝓘(ℂ, ℂ) x) := by
  -- Replicate the explicit IsIso construction from
  -- `mfderiv_isIso_of_ramificationIndex_one`, then apply
  -- `inv_unique_local` to identify the two `.inv`s.
  -- Derive `a ≠ 0` from the existence of an IsIso witness for `mfderiv f x`:
  -- since `mfderiv f x = toSpanSingleton ℂ a`, the iso forces `a ≠ 0`
  -- (else `toSpanSingleton ℂ 0 = 0` has no inverse).
  -- First, the mfderiv ↔ toSpanSingleton identity (always holds, ramification-free).
  set a : ℂ := deriv (chartLocalAt f x) (chartAt ℂ x x) with ha_def
  have hFD : HasFDerivAt (chartLocalAt f x)
      (ContinuousLinearMap.toSpanSingleton ℂ a) (chartAt ℂ x x) :=
    (hHol.holomorphicAt x).hasStrictDerivAt.hasStrictFDerivAt.hasFDerivAt
  have hMF : HasMFDerivAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) f x
      (ContinuousLinearMap.toSpanSingleton ℂ a) := by
    refine ⟨hHol.continuous.continuousAt, ?_⟩
    have hFD' : HasFDerivWithinAt (chartLocalAt f x)
        (ContinuousLinearMap.toSpanSingleton ℂ a) Set.univ (chartAt ℂ x x) :=
      hFD.hasFDerivWithinAt
    simpa [writtenInExtChartAt, chartLocalAt, Function.comp_def] using hFD'
  have hmFD : mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) f x =
      ContinuousLinearMap.toSpanSingleton ℂ a := hMF.mfderiv
  -- `a ≠ 0`: from `hiso.right_inv`, applied to `(1 : TangentSpace ... (f x))`,
  -- and `hmFD : mfderiv f x = toSpanSingleton ℂ a`, we derive
  -- `a • (hiso.inv 1) = 1`. If `a = 0` this gives `0 = 1`, contradiction.
  have hderiv : a ≠ 0 := by
    intro ha0
    have hright := hiso.right_inv
    -- Apply `hright` at `(1 : TangentSpace 𝓘(ℂ, ℂ) (f x))`, treating the codomain
    -- side as ℂ (which it is, definitionally). The `set w := hiso.inv 1` abbreviation
    -- keeps the dependent `mfderiv` reference out of the `rw [hmFD]` motive.
    have happ := congr_arg (fun (m : TangentSpace 𝓘(ℂ, ℂ) (f x) →L[ℂ]
      TangentSpace 𝓘(ℂ, ℂ) (f x)) => m (1 : TangentSpace 𝓘(ℂ, ℂ) (f x))) hright
    simp only [ContinuousLinearMap.coe_comp', Function.comp_apply,
      ContinuousLinearMap.id_apply] at happ
    -- happ : (mfderiv f x) (hiso.inv 1) = 1.
    set w : ℂ := (hiso.inv (1 : TangentSpace 𝓘(ℂ, ℂ) (f x)) : ℂ) with hw_def
    -- happ : (mfderiv f x) w = 1, with w : ℂ; rewrite mfderiv f x = toSpanSingleton ℂ a.
    rw [hmFD] at happ
    -- happ : (toSpanSingleton ℂ a) w = 1, which is `w • a = 1` in ℂ by rfl.
    have happ' : w • a = (1 : ℂ) := happ
    rw [ha0, smul_zero] at happ'
    exact one_ne_zero happ'.symm
  -- Build the explicit IsIso witness whose .inv is `toSpanSingleton ℂ a⁻¹`.
  let isoExplicit : IsIso (mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) f x) :=
  { inv := (ContinuousLinearMap.toSpanSingleton ℂ (a⁻¹ : ℂ) :
      TangentSpace 𝓘(ℂ, ℂ) (f x) →L[ℂ] TangentSpace 𝓘(ℂ, ℂ) x),
    left_inv := by
      rw [hmFD]
      show ((ContinuousLinearMap.toSpanSingleton ℂ (a⁻¹ : ℂ)).comp
              (ContinuousLinearMap.toSpanSingleton ℂ a) :
              ℂ →L[ℂ] ℂ) = ContinuousLinearMap.id ℂ ℂ
      refine ContinuousLinearMap.ext fun r => ?_
      simp only [ContinuousLinearMap.comp_apply,
                 ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul,
                 ContinuousLinearMap.id_apply]
      rw [mul_assoc, mul_inv_cancel₀ hderiv, mul_one]
    right_inv := by
      rw [hmFD]
      show ((ContinuousLinearMap.toSpanSingleton ℂ a).comp
              (ContinuousLinearMap.toSpanSingleton ℂ (a⁻¹ : ℂ)) :
              ℂ →L[ℂ] ℂ) = ContinuousLinearMap.id ℂ ℂ
      refine ContinuousLinearMap.ext fun r => ?_
      simp only [ContinuousLinearMap.comp_apply,
                 ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul,
                 ContinuousLinearMap.id_apply]
      rw [mul_assoc, inv_mul_cancel₀ hderiv, mul_one] }
  -- Both `hiso` and `isoExplicit` are IsIso witnesses for the same CLM;
  -- their `.inv` fields agree.
  exact IsIso.inv_unique_local hiso isoExplicit

omit [T2Space X] [CompactSpace X] [StableChartAt ℂ X]
  [T2Space Y] [CompactSpace Y] [ConnectedSpace Y] [StableChartAt ℂ Y] in
/--
**Explicit chart-local form of `cotangentPushforward` at an unramified
preimage (Commit C2.1 — sorry-free helper).**

At a point `x` of ramification index `1`, the cotangent pushforward
of any cotangent vector `ωx ∈ T_x^* X` is the explicit composition
of `ωx` with `toSpanSingleton ℂ ((deriv (chartLocalAt f x) (chart x x))⁻¹)`:

```
cotangentPushforward f x ωx =
  ωx.comp (toSpanSingleton ℂ ((deriv (chartLocalAt f x) (chart x x))⁻¹))
```

This is the per-preimage chart-local representation that the C3 step
sums over the `k` roots-of-unity preimages `z_j = w^{1/k} ζ^j` of `y`
near `y₀`.
-/
private theorem cotangentPushforward_eq_comp_toSpanSingleton_inv
    {f : X → Y} (hbc : BranchedCoverData X Y f)
    (hcompat : hbc.RamificationIndexCompatible)
    (hHol : IsHolomorphic f)
    {x : X} (hx_unram : hbc.ramificationIndex x = 1)
    (ωx : CotangentSpace ℂ X x) :
    cotangentPushforward f x ωx =
      ωx.comp
        (ContinuousLinearMap.toSpanSingleton ℂ
          ((deriv (chartLocalAt f x) (chartAt ℂ x x))⁻¹) :
          TangentSpace 𝓘(ℂ, ℂ) (f x) →L[ℂ] TangentSpace 𝓘(ℂ, ℂ) x) := by
  classical
  have hiso : Nonempty (IsIso (mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) f x)) :=
    mfderiv_isIso_of_ramificationIndex_one hbc hcompat hHol hx_unram
  unfold cotangentPushforward
  simp only [dif_pos hiso]
  rw [mfderiv_isIso_inv_eq_toSpanSingleton_inv hHol x (Classical.choice hiso)]

omit [T2Space X] [CompactSpace X] [StableChartAt ℂ X]
  [T2Space Y] [CompactSpace Y] [ConnectedSpace Y] [StableChartAt ℂ Y] in
/--
**Single-summand explicit ℂ-scalar form (Commit C2.2 — sorry-free
corollary of C2.1).**

Evaluating `cotangentPushforward f x ωx` at `(1 : TangentSpace 𝓘(ℂ, ℂ) (f x))`
yields the explicit ℂ-scalar
`((deriv (chartLocalAt f x) (chart x x))⁻¹) • ωx 1`, i.e. the inverse of
the chart-local derivative scaling the cotangent vector's value at `1`.

This is the "single summand evaluated as a scalar" form that C3 will
sum over the `k` roots-of-unity preimages and apply the
`∑_j ζ^{jℓ} = 0` cancellation to.

Uses Milestone 1's scoped `Inv` / `Field` instances on
`TangentSpace 𝓘(ℂ, ℂ) (f x)` (= `ℂ` definitionally) so that the smul
chain `(toSpanSingleton ℂ a) 1 = a • 1 = a` typechecks transparently.
-/
private theorem cotangentPushforward_apply_one
    {f : X → Y} (hbc : BranchedCoverData X Y f)
    (hcompat : hbc.RamificationIndexCompatible)
    (hHol : IsHolomorphic f)
    {x : X} (hx_unram : hbc.ramificationIndex x = 1)
    (ωx : CotangentSpace ℂ X x) :
    (cotangentPushforward f x ωx) (1 : TangentSpace 𝓘(ℂ, ℂ) (f x)) =
      ((deriv (chartLocalAt f x) (chartAt ℂ x x))⁻¹) •
        ωx (1 : TangentSpace 𝓘(ℂ, ℂ) x) := by
  rw [cotangentPushforward_eq_comp_toSpanSingleton_inv hbc hcompat hHol hx_unram ωx]
  -- Goal: (ωx.comp (toSpanSingleton ℂ a⁻¹)) 1 = a⁻¹ • ωx 1.
  -- Unfold via `toSpanSingleton_apply`: `(toSpanSingleton ℂ a⁻¹) 1 = 1 • a⁻¹`.
  -- Then CLM-linearity: `ωx (1 • a⁻¹) = ωx ((a⁻¹ : ℂ) • (1 : TangentSpace …)) = a⁻¹ • ωx 1`.
  show ωx ((ContinuousLinearMap.toSpanSingleton ℂ
      ((deriv (chartLocalAt f x) (chartAt ℂ x x))⁻¹))
      (1 : TangentSpace 𝓘(ℂ, ℂ) (f x))) =
    ((deriv (chartLocalAt f x) (chartAt ℂ x x))⁻¹) •
      ωx (1 : TangentSpace 𝓘(ℂ, ℂ) x)
  rw [ContinuousLinearMap.toSpanSingleton_apply, one_smul]
  -- Goal: ωx a⁻¹ = a⁻¹ • ωx 1, where `a⁻¹ : ℂ = TangentSpace 𝓘(ℂ,ℂ) x` definitionally.
  -- Rewrite the argument `a⁻¹` as `a⁻¹ • (1 : TangentSpace 𝓘(ℂ,ℂ) x)`, then apply map_smul.
  conv_lhs => rw [show ((deriv (chartLocalAt f x) (chartAt ℂ x x))⁻¹ :
      TangentSpace 𝓘(ℂ, ℂ) x) =
      ((deriv (chartLocalAt f x) (chartAt ℂ x x))⁻¹ : ℂ) •
        (1 : TangentSpace 𝓘(ℂ, ℂ) x) from by
    show ((deriv (chartLocalAt f x) (chartAt ℂ x x))⁻¹ : ℂ) =
        ((deriv (chartLocalAt f x) (chartAt ℂ x x))⁻¹ : ℂ) * (1 : ℂ)
    rw [mul_one]]
  rw [ContinuousLinearMap.map_smul]

omit [T2Space X] [CompactSpace X] [StableChartAt ℂ X]
  [T2Space Y] [CompactSpace Y] [ConnectedSpace Y] [StableChartAt ℂ Y] in
/--
**Single-summand `toSpanSingleton ℂ`-form (Commit C3a — sorry-free
helper).** Combining C2.1's `cotangentPushforward` formula with the
`ωx.comp (toSpanSingleton ℂ b) = toSpanSingleton ℂ (ωx (b • 1))`
identity, the cotangent pushforward at an unramified preimage `x` is
itself a `toSpanSingleton ℂ` CLM whose underlying ℂ-scalar is the
chart-local product `(deriv(chartLocalAt f x)(chart x x))⁻¹ * (η.toFun x) 1`.

After the `CotangentModelFiber ℂ = ℂ →L[ℂ] ℂ` identification (via the
trivial bundle and the Milestone-1 `TangentSpace` bridge), this lets
the C3a sum reduction push `toSpanSingleton ℂ` outside the Finset sum.
-/
private theorem cotangentPushforward_eq_toSpanSingleton_scalar
    {f : X → Y} (hbc : BranchedCoverData X Y f)
    (hcompat : hbc.RamificationIndexCompatible)
    (hHol : IsHolomorphic f)
    (η : HolomorphicOneForm ℂ X)
    {x : X} (hx_unram : hbc.ramificationIndex x = 1) :
    (cotangentPushforward f x (η.toFun x) : CotangentModelFiber ℂ) =
      ContinuousLinearMap.toSpanSingleton ℂ
        (((deriv (chartLocalAt f x) (chartAt ℂ x x))⁻¹) •
          (η.toFun x) (1 : TangentSpace 𝓘(ℂ, ℂ) x)) := by
  -- C2.1: cotangentPushforward = ωx.comp (toSpanSingleton ℂ a⁻¹).
  rw [cotangentPushforward_eq_comp_toSpanSingleton_inv hbc hcompat hHol hx_unram
        (η.toFun x)]
  -- Show ωx.comp (toSpanSingleton ℂ b) = toSpanSingleton ℂ (ωx (b • 1))
  -- where ωx = η.toFun x, b = a⁻¹. Both CLMs ℂ →L[ℂ] ℂ; check at any v : ℂ.
  refine ContinuousLinearMap.ext fun v => ?_
  -- LHS at v: ωx ((toSpanSingleton ℂ b) v) = ωx (v • b).
  -- RHS at v: (toSpanSingleton ℂ (b • ωx 1)) v = v • (b • ωx 1).
  -- Rewrite ωx (v • b) = ωx (v • (b • 1)) (using b = b • 1 in ℂ)
  --                    = v • ωx (b • 1) (by CLM map_smul on v)
  --                    = v • (b • ωx 1) (by CLM map_smul on b)
  -- which matches RHS.
  show (η.toFun x) ((ContinuousLinearMap.toSpanSingleton ℂ
      ((deriv (chartLocalAt f x) (chartAt ℂ x x))⁻¹)) v) =
    (ContinuousLinearMap.toSpanSingleton ℂ
      (((deriv (chartLocalAt f x) (chartAt ℂ x x))⁻¹ : ℂ) •
        (η.toFun x) (1 : TangentSpace 𝓘(ℂ, ℂ) x))) v
  rw [ContinuousLinearMap.toSpanSingleton_apply,
      ContinuousLinearMap.toSpanSingleton_apply]
  -- Goal: ωx (v • a⁻¹) = v • (a⁻¹ • ωx 1) where the SMul on the LHS-arg
  -- is ℂ-on-(TangentSpace 𝓘(ℂ,ℂ) x = ℂ).
  -- Rewrite v • a⁻¹ as v • (a⁻¹ • 1) (since a⁻¹ = a⁻¹ • 1 in ℂ).
  conv_lhs => rw [show ((deriv (chartLocalAt f x) (chartAt ℂ x x))⁻¹ :
      TangentSpace 𝓘(ℂ, ℂ) x) =
      ((deriv (chartLocalAt f x) (chartAt ℂ x x))⁻¹ : ℂ) •
        (1 : TangentSpace 𝓘(ℂ, ℂ) x) from by
    show ((deriv (chartLocalAt f x) (chartAt ℂ x x))⁻¹ : ℂ) =
        ((deriv (chartLocalAt f x) (chartAt ℂ x x))⁻¹ : ℂ) * (1 : ℂ)
    rw [mul_one]]
  -- Goal: ωx (v • (a⁻¹ • 1)) = v • (a⁻¹ • ωx 1).
  rw [smul_smul, ContinuousLinearMap.map_smul, smul_smul]

omit [T2Space X] [CompactSpace X] [StableChartAt ℂ X]
  [T2Space Y] [CompactSpace Y] [ConnectedSpace Y] [StableChartAt ℂ Y] in
/--
**CLM-sum reduction to `toSpanSingleton ℂ` of a scalar sum
(Commit C3a.1 — sorry-free helper).** For any Finset `s` of unramified
preimages of a single value `y`, the trace sum
`∑_{x ∈ s} cotangentPushforward f x (η.toFun x)` (typed as a
`CotangentModelFiber ℂ` CLM) equals `toSpanSingleton ℂ` of the
explicit ℂ-scalar sum
`∑_{x ∈ s} (deriv (chartLocalAt f x)(chart x x))⁻¹ • (η.toFun x) 1`.

This is the structural step that reduces the CLM-valued boundedness
obligation of `ramifiedKfoldSum_locally_bounded` to a complex-valued
boundedness obligation, which C3b/C4 will discharge analytically using
the roots-of-unity cancellation and Commit-B's chart-local derivative
formula.
-/
private theorem traceSum_eq_toSpanSingleton_of_scalarSum
    {f : X → Y} (hbc : BranchedCoverData X Y f)
    (hcompat : hbc.RamificationIndexCompatible)
    (hHol : IsHolomorphic f)
    (η : HolomorphicOneForm ℂ X)
    (s : Finset X)
    (hs_unram : ∀ x ∈ s, hbc.ramificationIndex x = 1) :
    (s.attach.sum (fun x =>
        (cotangentPushforward f x.1 (η.toFun x.1) :
          CotangentModelFiber ℂ)) : CotangentModelFiber ℂ) =
      ContinuousLinearMap.toSpanSingleton ℂ
        (s.attach.sum (fun x =>
          ((deriv (chartLocalAt f x.1) (chartAt ℂ x.1 x.1))⁻¹) •
            (η.toFun x.1) (1 : TangentSpace 𝓘(ℂ, ℂ) x.1))) := by
  classical
  -- Rewrite each summand using `cotangentPushforward_eq_toSpanSingleton_scalar`.
  have hsum_congr :
      s.attach.sum (fun x =>
        (cotangentPushforward f x.1 (η.toFun x.1) : CotangentModelFiber ℂ)) =
      s.attach.sum (fun x =>
        (ContinuousLinearMap.toSpanSingleton ℂ
          (((deriv (chartLocalAt f x.1) (chartAt ℂ x.1 x.1))⁻¹) •
            (η.toFun x.1) (1 : TangentSpace 𝓘(ℂ, ℂ) x.1)) :
          CotangentModelFiber ℂ)) := by
    refine Finset.sum_congr rfl ?_
    rintro ⟨x, hx_mem⟩ _
    exact cotangentPushforward_eq_toSpanSingleton_scalar hbc hcompat hHol η
      (hs_unram x hx_mem)
  rw [hsum_congr]
  -- Push `toSpanSingleton ℂ` out of the sum via `Finset.sum`-additivity of
  -- `toSpanSingleton`. Use `ContinuousLinearMap.ext` + pointwise check.
  refine ContinuousLinearMap.ext fun v => ?_
  -- LHS at v: ∑ (toSpanSingleton ℂ cᵢ) v = ∑ (v • cᵢ) = v • ∑ cᵢ.
  -- RHS at v: (toSpanSingleton ℂ (∑ cᵢ)) v = v • ∑ cᵢ.
  rw [ContinuousLinearMap.sum_apply]
  simp only [ContinuousLinearMap.toSpanSingleton_apply]
  rw [Finset.smul_sum]

omit [T2Space X] [CompactSpace X] [StableChartAt ℂ X]
  [T2Space Y] [CompactSpace Y] [ConnectedSpace Y] [StableChartAt ℂ Y] in
/--
**CLM-norm = scalar magnitude (Commit C3a.2 — sorry-free corollary).**
The norm of the CLM trace sum equals the magnitude of the underlying
ℂ-scalar sum, via Mathlib's `ContinuousLinearMap.norm_toSpanSingleton`.
This is the last structural step before C3b/C4's analytic boundedness
work: bounding the CLM-valued sum reduces to bounding a single complex
number's magnitude.
-/
private theorem norm_traceSum_eq_abs_scalarSum
    {f : X → Y} (hbc : BranchedCoverData X Y f)
    (hcompat : hbc.RamificationIndexCompatible)
    (hHol : IsHolomorphic f)
    (η : HolomorphicOneForm ℂ X)
    (s : Finset X)
    (hs_unram : ∀ x ∈ s, hbc.ramificationIndex x = 1) :
    ‖(s.attach.sum (fun x =>
        (cotangentPushforward f x.1 (η.toFun x.1) :
          CotangentModelFiber ℂ)) : CotangentModelFiber ℂ)‖ =
      ‖s.attach.sum (fun x =>
        ((deriv (chartLocalAt f x.1) (chartAt ℂ x.1 x.1))⁻¹) •
          (η.toFun x.1) (1 : TangentSpace 𝓘(ℂ, ℂ) x.1))‖ := by
  rw [traceSum_eq_toSpanSingleton_of_scalarSum hbc hcompat hHol η s hs_unram]
  exact ContinuousLinearMap.norm_toSpanSingleton _

omit [T2Space X] [CompactSpace X] [ConnectedSpace X] [ChartedSpace ℂ X]
  [IsManifold 𝓘(ℂ, ℂ) ω X] [StableChartAt ℂ X]
  [T2Space Y] [CompactSpace Y] [ConnectedSpace Y] [ChartedSpace ℂ Y]
  [IsManifold 𝓘(ℂ, ℂ) ω Y] [StableChartAt ℂ Y] in
/--
**Filter-sum to `s_y`-sum reduction (Commit C3b.1 — sorry-free helper).**

Given the kfold structural data `h_kfold_data` — a Finset `s` of unramified
preimages of `y` contained in `U_kfold` and exhausting all preimages of `y`
in `U_kfold` — and a window `W ⊆ U_kfold` containing `s`, the filter form
`(hbc.finite_fiber y).toFinset.filter (· ∈ W)` equals `s` as Finsets.

This is pure `Finset` extensionality, no analysis: the filter selects
elements of the fiber lying in `W`, which by `s ⊆ W ⊆ U_kfold` and the
`s`-exhausts-`U_kfold`-preimages property must be exactly `s`.

After C3b.1 + C3b.2, the L1214 `ramifiedKfoldSum_locally_bounded` LHS norm
reduces to a pure ℂ-valued Finset sum's magnitude — no more CLM / cotangent
bundle plumbing.
-/
private theorem filter_fiber_eq_kfold_finset
    {f : X → Y} (hbc : BranchedCoverData X Y f)
    {U_kfold : Set X} (W : Set X)
    (hW_sub_U : W ⊆ U_kfold)
    {y : Y} (s : Finset X)
    (hs_fiber : ∀ x ∈ s, f x = y)
    (hs_exhaust : ∀ x ∈ U_kfold, f x = y → x ∈ s)
    (hs_sub_W : (↑s : Set X) ⊆ W) :
    (hbc.finite_fiber y).toFinset.filter (· ∈ W) = s := by
  classical
  apply Finset.ext
  intro x'
  simp only [Finset.mem_filter, Set.Finite.mem_toFinset, Set.mem_preimage,
    Set.mem_singleton_iff]
  constructor
  · rintro ⟨hfx'y, hx'W⟩
    -- f x' = y, x' ∈ W ⊆ U_kfold, so x' ∈ s by exhaustion.
    exact hs_exhaust x' (hW_sub_U hx'W) hfx'y
  · intro hx's
    refine ⟨hs_fiber x' hx's, ?_⟩
    -- x' ∈ s ⊆ W (as sets), so x' ∈ W.
    exact hs_sub_W hx's

omit [T2Space X] [CompactSpace X] [StableChartAt ℂ X]
  [T2Space Y] [CompactSpace Y] [ConnectedSpace Y] [StableChartAt ℂ Y] in
/--
**Bridging corollary: filter-CLM-norm = `s_y`-scalar-magnitude
(Commit C3b.2 — sorry-free corollary).**

Combines C3b.1 (`filter_fiber_eq_kfold_finset`) with C3a.2
(`norm_traceSum_eq_abs_scalarSum`) to express the
`ramifiedKfoldSum_locally_bounded` LHS norm directly in terms of the
explicit chart-local complex-valued Finset sum over `s`, i.e. the
kfold-structural Finset of `k` unramified preimages. After this corollary,
the remaining boundedness obligation is `|complex Finset sum| ≤ M`
— pure ℂ.
-/
private theorem norm_filterSum_eq_norm_kfoldScalarSum
    {f : X → Y} (hbc : BranchedCoverData X Y f)
    (hcompat : hbc.RamificationIndexCompatible)
    (hHol : IsHolomorphic f) (η : HolomorphicOneForm ℂ X)
    {U_kfold : Set X} (W : Set X) (hW_sub_U : W ⊆ U_kfold)
    {y : Y} (s : Finset X)
    (hs_unram : ∀ x ∈ s, hbc.ramificationIndex x = 1)
    (hs_fiber : ∀ x ∈ s, f x = y)
    (hs_exhaust : ∀ x ∈ U_kfold, f x = y → x ∈ s)
    (hs_sub_W : (↑s : Set X) ⊆ W) :
    ‖(((hbc.finite_fiber y).toFinset.filter (· ∈ W)).attach.sum
        (fun x => (cotangentPushforward f x.1 (η.toFun x.1) :
          CotangentModelFiber ℂ)) : CotangentModelFiber ℂ)‖ =
      ‖s.attach.sum (fun x =>
        ((deriv (chartLocalAt f x.1) (chartAt ℂ x.1 x.1))⁻¹) •
          (η.toFun x.1) (1 : TangentSpace 𝓘(ℂ, ℂ) x.1))‖ := by
  rw [filter_fiber_eq_kfold_finset hbc W hW_sub_U s hs_fiber hs_exhaust hs_sub_W]
  exact norm_traceSum_eq_abs_scalarSum hbc hcompat hHol η s hs_unram

omit [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [IsManifold 𝓘(ℂ, ℂ) ω X]
  [T2Space Y] [CompactSpace Y] [ConnectedSpace Y]
  [IsManifold 𝓘(ℂ, ℂ) ω Y] in
/--
**Chart-stability rewrite of the per-summand derivative factor
(Commit C3c.1 — sorry-free helper).**

When `x` lies in the chart source of `chartAt ℂ x₀` and `f x` lies in
the chart source of `chartAt ℂ (f x₀)`, the `StableChartAt` typeclasses
identify both `chartAt ℂ x = chartAt ℂ x₀` (on `X`) and
`chartAt ℂ (f x) = chartAt ℂ (f x₀)` (on `Y`). Hence
`chartLocalAt f x = chartLocalAt f x₀` as functions `ℂ → ℂ`, and the
chart-evaluation `chartAt ℂ x x = chartAt ℂ x₀ x`, so the per-summand
derivative factor rewrites uniformly.

After C3c every per-summand factor in the scalar Finset sum refers to
the SAME `chartLocalAt f x₀` evaluated at chart coordinates
`chart x₀ x_j`, which is exactly the form Commits A/B
(`chartLocal_zPow_form_of_ramified`, `chartLocal_deriv_of_zPow_form`)
give explicit `φ`/`φ'` formulas for. This unblocks the C3d substitution.
-/
private theorem chartLocalAt_deriv_eq_of_chart_source
    {f : X → Y} {x₀ : X} {x : X}
    (hx_source : x ∈ (chartAt ℂ x₀).source)
    (hfx_source : f x ∈ (chartAt ℂ (f x₀)).source) :
    deriv (chartLocalAt f x) (chartAt ℂ x x) =
      deriv (chartLocalAt f x₀) (chartAt ℂ x₀ x) := by
  -- Both chart-stability identifications.
  have hchartX : chartAt ℂ x = chartAt ℂ x₀ :=
    JacobianChallenge.Periods.StableChartAt.chartAt_eq_of_mem_source x₀ x hx_source
  have hchartY : chartAt ℂ (f x) = chartAt ℂ (f x₀) :=
    JacobianChallenge.Periods.StableChartAt.chartAt_eq_of_mem_source (f x₀) (f x) hfx_source
  -- chartLocalAt f x = chartLocalAt f x₀ as functions (both sides unfold to the same composition).
  have hfun : chartLocalAt f x = chartLocalAt f x₀ := by
    unfold chartLocalAt
    rw [hchartX, hchartY]
  -- Evaluation point: chartAt ℂ x x = chartAt ℂ x₀ x.
  have hpt : (chartAt ℂ x) x = (chartAt ℂ x₀) x := by rw [hchartX]
  rw [hfun, hpt]

omit [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [T2Space Y] [CompactSpace Y] [ConnectedSpace Y]
  [IsManifold 𝓘(ℂ, ℂ) ω Y] in
/--
**Lift the chart-stability rewrite to the full scalar Finset sum
(Commit C3c.2 — sorry-free corollary).**

Under the per-summand chart-source-membership hypotheses, the explicit
ℂ-scalar Finset sum (from C3a's `norm_traceSum_eq_abs_scalarSum`) is
unchanged when each per-summand factor `deriv (chartLocalAt f x.1)(chart x.1 x.1)`
is replaced by `deriv (chartLocalAt f x₀)(chart x₀ x.1)`. This puts the
sum in the form needed to apply Commits A/B in C3d.
-/
private theorem scalarSum_factor_eq_x0_chart_form
    {f : X → Y} (x₀ : X) (η : HolomorphicOneForm ℂ X)
    (s : Finset X)
    (hs_source : ∀ x ∈ s, x ∈ (chartAt ℂ x₀).source)
    (hs_fsource : ∀ x ∈ s, f x ∈ (chartAt ℂ (f x₀)).source) :
    s.attach.sum (fun x =>
      ((deriv (chartLocalAt f x.1) (chartAt ℂ x.1 x.1))⁻¹) •
        (η.toFun x.1) (1 : TangentSpace 𝓘(ℂ, ℂ) x.1)) =
    s.attach.sum (fun x =>
      ((deriv (chartLocalAt f x₀) (chartAt ℂ x₀ x.1))⁻¹) •
        (η.toFun x.1) (1 : TangentSpace 𝓘(ℂ, ℂ) x.1)) := by
  refine Finset.sum_congr rfl ?_
  rintro ⟨x, hx_mem⟩ _
  rw [chartLocalAt_deriv_eq_of_chart_source
    (hs_source x hx_mem) (hs_fsource x hx_mem)]

omit [T2Space X] [CompactSpace X] [ConnectedSpace X] [StableChartAt ℂ X]
  [T2Space Y] [CompactSpace Y] [ConnectedSpace Y]
  [IsManifold 𝓘(ℂ, ℂ) ω Y] [StableChartAt ℂ Y] in
/--
**Substitute Commit B's `k · φ^{k-1} · φ'` derivative formula into the
scalar Finset sum (Commit C3d.1 — sorry-free helper).**

After C3c the per-summand derivative factor in the scalar sum refers
uniformly to `deriv (chartLocalAt f x₀)(chart x₀ x.1)`. Given the
per-summand hypothesis that Commit B's `chartLocal_deriv_of_zPow_form`
formula holds at each `chart x₀ x.1` (which C4 will arrange by picking
`W ⊆ X` small enough that `chart x₀ x` lies in Commit B's
eventually-neighborhood for all `x ∈ W`), substitute the formula
into each summand via `Finset.sum_congr`.

After C3d.1 each per-summand denominator has the explicit chart-local
`k · φ(z)^{k-1} · φ'(z)` form, ready for C4's roots-of-unity cancellation.
-/
private theorem scalarSum_in_phi_form
    {f : X → Y} (x₀ : X) (η : HolomorphicOneForm ℂ X)
    (k : ℕ) (φ : ℂ → ℂ)
    (s : Finset X)
    (h_deriv_formula : ∀ x ∈ s,
      deriv (chartLocalAt f x₀) (chartAt ℂ x₀ x) =
        (k : ℂ) * φ (chartAt ℂ x₀ x) ^ (k - 1) * deriv φ (chartAt ℂ x₀ x)) :
    s.attach.sum (fun x =>
      ((deriv (chartLocalAt f x₀) (chartAt ℂ x₀ x.1))⁻¹) •
        (η.toFun x.1) (1 : TangentSpace 𝓘(ℂ, ℂ) x.1)) =
    s.attach.sum (fun x =>
      (((k : ℂ) * φ (chartAt ℂ x₀ x.1) ^ (k - 1) *
          deriv φ (chartAt ℂ x₀ x.1))⁻¹) •
        (η.toFun x.1) (1 : TangentSpace 𝓘(ℂ, ℂ) x.1)) := by
  refine Finset.sum_congr rfl ?_
  rintro ⟨x, hx_mem⟩ _
  rw [h_deriv_formula x hx_mem]

omit [T2Space X] [CompactSpace X]
  [T2Space Y] [CompactSpace Y] [ConnectedSpace Y] in
/--
**End-to-end bridging corollary: filter-CLM-norm = `φ`/`φ'`-form
scalar magnitude (Commit C3d.2 — sorry-free corollary).**

Chains C3b.2 (`norm_filterSum_eq_norm_kfoldScalarSum`) → C3c.2
(`scalarSum_factor_eq_x0_chart_form`) → C3d.1 (`scalarSum_in_phi_form`)
into a single norm equality. After this corollary the
`ramifiedKfoldSum_locally_bounded` LHS norm has the literal `φ`/`φ'`
rational form, ready for C4's analytic cancellation argument.
-/
private theorem norm_filterSum_eq_norm_phiForm
    {f : X → Y} (hbc : BranchedCoverData X Y f)
    (hcompat : hbc.RamificationIndexCompatible)
    (hHol : IsHolomorphic f) (η : HolomorphicOneForm ℂ X)
    (x₀ : X) (k : ℕ) (φ : ℂ → ℂ)
    {U_kfold : Set X} (W : Set X) (hW_sub_U : W ⊆ U_kfold)
    {y : Y} (s : Finset X)
    (hs_unram : ∀ x ∈ s, hbc.ramificationIndex x = 1)
    (hs_fiber : ∀ x ∈ s, f x = y)
    (hs_exhaust : ∀ x ∈ U_kfold, f x = y → x ∈ s)
    (hs_sub_W : (↑s : Set X) ⊆ W)
    (hs_source : ∀ x ∈ s, x ∈ (chartAt ℂ x₀).source)
    (hs_fsource : ∀ x ∈ s, f x ∈ (chartAt ℂ (f x₀)).source)
    (h_deriv_formula : ∀ x ∈ s,
      deriv (chartLocalAt f x₀) (chartAt ℂ x₀ x) =
        (k : ℂ) * φ (chartAt ℂ x₀ x) ^ (k - 1) * deriv φ (chartAt ℂ x₀ x)) :
    ‖(((hbc.finite_fiber y).toFinset.filter (· ∈ W)).attach.sum
        (fun x => (cotangentPushforward f x.1 (η.toFun x.1) :
          CotangentModelFiber ℂ)) : CotangentModelFiber ℂ)‖ =
    ‖s.attach.sum (fun x =>
      (((k : ℂ) * φ (chartAt ℂ x₀ x.1) ^ (k - 1) *
          deriv φ (chartAt ℂ x₀ x.1))⁻¹) •
        (η.toFun x.1) (1 : TangentSpace 𝓘(ℂ, ℂ) x.1))‖ := by
  -- Chain the three equalities transitively.
  calc ‖(((hbc.finite_fiber y).toFinset.filter (· ∈ W)).attach.sum
        (fun x => (cotangentPushforward f x.1 (η.toFun x.1) :
          CotangentModelFiber ℂ)) : CotangentModelFiber ℂ)‖
      = ‖s.attach.sum (fun x =>
          ((deriv (chartLocalAt f x.1) (chartAt ℂ x.1 x.1))⁻¹) •
            (η.toFun x.1) (1 : TangentSpace 𝓘(ℂ, ℂ) x.1))‖ :=
        norm_filterSum_eq_norm_kfoldScalarSum hbc hcompat hHol η W hW_sub_U s
          hs_unram hs_fiber hs_exhaust hs_sub_W
    _ = ‖s.attach.sum (fun x =>
          ((deriv (chartLocalAt f x₀) (chartAt ℂ x₀ x.1))⁻¹) •
            (η.toFun x.1) (1 : TangentSpace 𝓘(ℂ, ℂ) x.1))‖ := by
        rw [scalarSum_factor_eq_x0_chart_form x₀ η s hs_source hs_fsource]
    _ = ‖s.attach.sum (fun x =>
          (((k : ℂ) * φ (chartAt ℂ x₀ x.1) ^ (k - 1) *
              deriv φ (chartAt ℂ x₀ x.1))⁻¹) •
            (η.toFun x.1) (1 : TangentSpace 𝓘(ℂ, ℂ) x.1))‖ := by
        congr 1
        exact scalarSum_in_phi_form x₀ η k φ s h_deriv_formula

/-! ### Commit C4-pre helpers: chart-local bijection `s_y ↔ Fin k` via `φ⁻¹`. -/

omit [T2Space X] [CompactSpace X] [ConnectedSpace X] [ChartedSpace ℂ X]
  [IsManifold 𝓘(ℂ, ℂ) ω X] [StableChartAt ℂ X]
  [T2Space Y] [CompactSpace Y] [ConnectedSpace Y] [ChartedSpace ℂ Y]
  [IsManifold 𝓘(ℂ, ℂ) ω Y] [StableChartAt ℂ Y] in
/--
**Layer-C bijection prerequisite (C4-pre.1) — local inverse of `φ` near
`z₀` (sorry-free helper).**

Given Commit A's `φ` (analytic at `z₀`, `φ z₀ = 0`, `deriv φ z₀ ≠ 0`),
the inverse function theorem produces a local inverse
`r : ℂ → ℂ` with `r (φ z₀) = z₀` and the right-inverse property
`∀ᶠ ε in 𝓝 (φ z₀), φ (r ε) = ε`. Since `φ z₀ = 0`, `r 0 = z₀` and the
right-inverse property holds eventually near `0 : ℂ`.

This is **C4-pre.1**: the first ingredient of the chart-local bijection.
C4-pre.2 (`kthRoot_branch`) provides `(·)^{1/k}` so C4-pre.3 can compose
to get the candidate preimages `r(ζ^j · w^{1/k})`.
-/
private theorem phi_localInverse_exists
    {φ : ℂ → ℂ} {z₀ : ℂ} (hφ_an : AnalyticAt ℂ φ z₀)
    (hφ_z₀ : φ z₀ = 0)
    (hφ_deriv : deriv φ z₀ ≠ 0) :
    ∃ r : ℂ → ℂ, r 0 = z₀ ∧
      (∀ᶠ ε in 𝓝 (0 : ℂ), φ (r ε) = ε) ∧
      (∀ᶠ z in 𝓝 z₀, r (φ z) = z) := by
  -- φ has a strict derivative at z₀, namely deriv φ z₀.
  have hSD : HasStrictDerivAt φ (deriv φ z₀) z₀ := hφ_an.hasStrictDerivAt
  -- Construct the local inverse via the inverse function theorem.
  refine ⟨hSD.localInverse φ (deriv φ z₀) z₀ hφ_deriv, ?_, ?_, ?_⟩
  · -- r 0 = z₀: rewrite via φ z₀ = 0, then `eventually_left_inverse` at z₀.
    have hL : ∀ᶠ z in 𝓝 z₀, hSD.localInverse φ (deriv φ z₀) z₀ hφ_deriv (φ z) = z :=
      hSD.eventually_left_inverse hφ_deriv
    -- Specialize at z = z₀.
    have hz₀ : hSD.localInverse φ (deriv φ z₀) z₀ hφ_deriv (φ z₀) = z₀ := hL.self_of_nhds
    -- Substitute φ z₀ = 0.
    rwa [hφ_z₀] at hz₀
  · -- right inverse: φ (r ε) = ε for ε near φ z₀ = 0.
    have hR : ∀ᶠ ε in 𝓝 (φ z₀), φ (hSD.localInverse φ (deriv φ z₀) z₀ hφ_deriv ε) = ε :=
      hSD.eventually_right_inverse hφ_deriv
    rwa [hφ_z₀] at hR
  · -- left inverse: r (φ z) = z for z near z₀.
    exact hSD.eventually_left_inverse hφ_deriv

omit [T2Space X] [CompactSpace X] [ConnectedSpace X] [ChartedSpace ℂ X]
  [IsManifold 𝓘(ℂ, ℂ) ω X] [StableChartAt ℂ X]
  [T2Space Y] [CompactSpace Y] [ConnectedSpace Y] [ChartedSpace ℂ Y]
  [IsManifold 𝓘(ℂ, ℂ) ω Y] [StableChartAt ℂ Y] in
/--
**Layer-C bijection prerequisite (C4-pre.2) — `k`-th root branch (sorry-free
helper).**

Choose the principal `k`-th root via `Complex.cpow` with exponent `k⁻¹`:
`kthRoot w := w ^ ((k : ℂ)⁻¹)`. For `k > 0`, this satisfies
`(kthRoot w)^k = w` for every `w : ℂ` (a consequence of
`Complex.cpow_nat_inv_pow`).

This is **C4-pre.2**: the chosen branch of the `k`-th root. C4-pre.3 will
compose `phi_localInverse_exists.r ∘ (ζ^j · ·) ∘ kthRoot` to produce
the candidate chart-local preimages.
-/
private theorem kthRoot_branch_pow_eq
    {k : ℕ} (hk : k ≠ 0) (w : ℂ) :
    (w ^ ((k : ℂ)⁻¹)) ^ k = w :=
  Complex.cpow_nat_inv_pow w hk

omit [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [IsManifold 𝓘(ℂ, ℂ) ω X] [StableChartAt ℂ X]
  [T2Space Y] [CompactSpace Y] [ConnectedSpace Y]
  [IsManifold 𝓘(ℂ, ℂ) ω Y] [StableChartAt ℂ Y] in
/--
**Layer-C bijection prerequisite (C4-pre.3) — chart-coordinate value
of the candidate preimage (sorry-free helper).**

Let `r` be the local inverse of `φ` from `phi_localInverse_exists`,
and `kthRoot w := w ^ ((k : ℂ)⁻¹)`. For `j ∈ Fin k`, `ζ` a primitive
`k`-th root of unity, and `w ∈ ℂ` with `ζ^j · kthRoot w` in `r`'s
right-inverse neighborhood, the chart-local map at `r(ζ^j · kthRoot w)`
takes the value `chartAt ℂ (f x₀) (f x₀) + w`:

  `chartLocalAt f x₀ (r (ζ^j · kthRoot w)) = c₀ + w`

This uses the chart-local power form (Commit A) `chartLocalAt f x₀ z - c₀ = φ(z)^k`,
the right-inverse property `φ(r ε) = ε`, the kth-root identity
`(kthRoot w)^k = w`, and the primitive-root identity `ζ^(j·k) = (ζ^k)^j = 1`.

This is **C4-pre.3**: the chart-level identity at the candidate preimage.
C4-pre.4 will use this to map back through the chart, conclude
`f (chart-preimage) = y`, and verify the bijection with `s_y`.
-/
private theorem chart_preimage_at_kthRoot_chart_eq
    {f : X → Y} {x₀ : X}
    {k : ℕ}
    {φ r kthRoot : ℂ → ℂ}
    (h_pow_form_at : ∀ z, chartLocalAt f x₀ z - chartAt ℂ (f x₀) (f x₀) = φ z ^ k)
    (h_right_inv_at : ∀ ε, φ (r ε) = ε)
    (h_kthRoot_pow : ∀ w, (kthRoot w) ^ k = w)
    {ζ : ℂ} (hζ : IsPrimitiveRoot ζ k)
    (j : ℕ) (w : ℂ) :
    chartLocalAt f x₀ (r ((ζ ^ j) * kthRoot w)) =
      chartAt ℂ (f x₀) (f x₀) + w := by
  -- (LHS - c₀) = φ(r(ζ^j * kthRoot w))^k by h_pow_form_at
  --            = (ζ^j * kthRoot w)^k by h_right_inv_at
  --            = ζ^(jk) * (kthRoot w)^k by mul_pow
  --            = (ζ^k)^j * w by ζ-commutativity and h_kthRoot_pow
  --            = 1^j * w = w by hζ.pow_eq_one
  have h_LHS_sub : chartLocalAt f x₀ (r ((ζ ^ j) * kthRoot w)) -
      chartAt ℂ (f x₀) (f x₀) = w := by
    rw [h_pow_form_at, h_right_inv_at, mul_pow, h_kthRoot_pow]
    rw [show (ζ ^ j) ^ k = (ζ ^ k) ^ j from by rw [← pow_mul, ← pow_mul, Nat.mul_comm]]
    rw [hζ.pow_eq_one, one_pow, one_mul]
  linear_combination h_LHS_sub

omit [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [IsManifold 𝓘(ℂ, ℂ) ω X] [StableChartAt ℂ X]
  [T2Space Y] [CompactSpace Y] [ConnectedSpace Y]
  [IsManifold 𝓘(ℂ, ℂ) ω Y] [StableChartAt ℂ Y] in
/--
**Layer-C bijection prerequisite (C4-pre.4) — chart-preimage of the
candidate maps under `f` to the predetermined `y` (sorry-free helper).**

Combining C4-pre.3's chart-coordinate identity with the assumption that
both `f (chart-preimage)` and the predetermined `y` lie in
`(chartAt ℂ (f x₀)).source` (so the partial chart is injective on them),
the candidate chart-preimage `x_j(w) := (chart x₀).symm (r (ζ^j · kthRoot w))`
satisfies `f (x_j(w)) = y` when `chart y₀ y - c₀ = w`.

The hypothesis `h_chart_preim_source` (the candidate is in `(chart x₀)`'s
source) is what `C4` will arrange by choosing `W` small enough; similarly
`h_y_source` (y near y₀ in chart source) follows for small `V` near `y₀`.

This is **C4-pre.4**: candidate preimage really IS a preimage of `y`.
Together with C4-pre.{1,2,3}, this gives the four chart-local primitives
the C4 cancellation argument needs.
-/
private theorem chart_preimage_at_kthRoot_in_fiber
    {f : X → Y} {x₀ : X}
    {k : ℕ}
    {φ r kthRoot : ℂ → ℂ}
    (h_pow_form_at : ∀ z, chartLocalAt f x₀ z - chartAt ℂ (f x₀) (f x₀) = φ z ^ k)
    (h_right_inv_at : ∀ ε, φ (r ε) = ε)
    (h_kthRoot_pow : ∀ w, (kthRoot w) ^ k = w)
    {ζ : ℂ} (hζ : IsPrimitiveRoot ζ k)
    (j : ℕ) {y : Y} (w : ℂ)
    (h_y_chart_eq : chartAt ℂ (f x₀) y = chartAt ℂ (f x₀) (f x₀) + w)
    (h_y_source : y ∈ (chartAt ℂ (f x₀)).source)
    (h_f_chart_preim_source :
      f ((chartAt ℂ x₀).symm (r ((ζ ^ j) * kthRoot w))) ∈ (chartAt ℂ (f x₀)).source) :
    f ((chartAt ℂ x₀).symm (r ((ζ ^ j) * kthRoot w))) = y := by
  -- Step 1: chartLocalAt f x₀ at the candidate equals c₀ + w (C4-pre.3).
  have h_chartLocal_val := chart_preimage_at_kthRoot_chart_eq
    (f := f) (x₀ := x₀) (k := k)
    (φ := φ) (r := r) (kthRoot := kthRoot)
    h_pow_form_at h_right_inv_at h_kthRoot_pow hζ j w
  -- Step 2: unfold chartLocalAt to identify
  --   chartAt ℂ (f x₀) (f ((chart x₀).symm (r (ζ^j · kthRoot w)))) = c₀ + w.
  have h_chartY_val :
      chartAt ℂ (f x₀) (f ((chartAt ℂ x₀).symm (r ((ζ ^ j) * kthRoot w)))) =
        chartAt ℂ (f x₀) (f x₀) + w := by
    -- chartLocalAt f x₀ z = chartAt ℂ (f x₀) (f ((chart x₀).symm z)) by def.
    have hdef : chartLocalAt f x₀ (r ((ζ ^ j) * kthRoot w)) =
        chartAt ℂ (f x₀) (f ((chartAt ℂ x₀).symm (r ((ζ ^ j) * kthRoot w)))) := by
      unfold chartLocalAt
      rfl
    rw [← hdef]
    exact h_chartLocal_val
  -- Step 3: now `chartAt ℂ (f x₀)` is injective on its source; identify f(candidate) with y.
  -- chartAt ℂ (f x₀) (f candidate) = c₀ + w = chartAt ℂ (f x₀) y by h_y_chart_eq.
  have hchart_eq :
      chartAt ℂ (f x₀) (f ((chartAt ℂ x₀).symm (r ((ζ ^ j) * kthRoot w)))) =
        chartAt ℂ (f x₀) y := by
    rw [h_chartY_val, ← h_y_chart_eq]
  exact (chartAt ℂ (f x₀)).injOn h_f_chart_preim_source h_y_source hchart_eq

/-! ### R-sub-development R1 — coefficient-vanishing for ζ-rotation-invariant analytic functions. -/

omit [T2Space X] [CompactSpace X] [ConnectedSpace X] [ChartedSpace ℂ X]
  [IsManifold 𝓘(ℂ, ℂ) ω X] [StableChartAt ℂ X]
  [T2Space Y] [CompactSpace Y] [ConnectedSpace Y] [ChartedSpace ℂ Y]
  [IsManifold 𝓘(ℂ, ℂ) ω Y] [StableChartAt ℂ Y] in
/--
**R1 — Coefficient-vanishing for ζ-rotation-invariant analytic functions
(sorry-free helper; first R-leaf of the locally-built
rotation-invariant analytic-extension theorem).**

If `F : ℂ → ℂ` is analytic at `0` and satisfies the eventual rotation
invariance `F =ᶠ[𝓝 0] (fun z => F (ζ * z))` for `ζ` a primitive `k`-th
root of unity (`k ≠ 0`), then the `n`-th iterated derivative of `F` at
`0` vanishes whenever `¬ k ∣ n`.

Proof sketch:
- `AnalyticAt ⇒ AnalyticOnNhd` on some open ball `B := Metric.ball 0 r`.
- `‖ζ‖ = 1` (primitive root) ⇒ `Set.MapsTo (ζ * ·) B B`.
- `AnalyticOnNhd ⇒ ContDiffOn ⊤` on `B`.
- `iteratedDerivWithin_comp_const_smul` at `0`:
  `iteratedDerivWithin n (F ∘ (ζ·)) B 0 = ζ^n • iteratedDerivWithin n F B 0`.
- `iteratedDerivWithin_of_isOpen` to convert to `iteratedDeriv`.
- `Filter.EventuallyEq.iteratedDeriv_eq` to get
  `iteratedDeriv n F 0 = iteratedDeriv n (F ∘ (ζ·)) 0`.
- Combine: `iteratedDeriv n F 0 = ζ^n • iteratedDeriv n F 0`, so
  `(1 - ζ^n) • iteratedDeriv n F 0 = 0`.
- `ζ^n ≠ 1` (from `¬ k ∣ n` + `IsPrimitiveRoot.dvd_of_pow_eq_one`).
- Conclude `iteratedDeriv n F 0 = 0`.

This is the algebraic engine for the rotation-invariant analytic-extension
theorem `R-final`: the coefficient vanishing it establishes is what makes
a `ζ`-rotation-invariant analytic function factor as `G(z^k)` for some
analytic `G`.
-/
private theorem iteratedDeriv_zero_of_eventually_rotation_invariant
    {F : ℂ → ℂ} (hF : AnalyticAt ℂ F 0)
    {k : ℕ} (hk : k ≠ 0) {ζ : ℂ} (hζ : IsPrimitiveRoot ζ k)
    (h_rot : F =ᶠ[𝓝 0] (fun z => F (ζ * z)))
    {n : ℕ} (hn : ¬ k ∣ n) :
    iteratedDeriv n F 0 = 0 := by
  -- Step 1: Extract an open ball `B := Metric.ball 0 r` where `F` is analytic.
  obtain ⟨r, hr_pos, hF_an⟩ := hF.exists_ball_analyticOnNhd
  set B : Set ℂ := Metric.ball 0 r with hB_def
  have hB_open : IsOpen B := Metric.isOpen_ball
  have h0_mem : (0 : ℂ) ∈ B := by
    simp [hB_def, Metric.mem_ball, hr_pos]
  -- Step 2: `‖ζ‖ = 1` ⇒ MapsTo (ζ * ·) B B.
  have hζ_norm : ‖ζ‖ = 1 := hζ.norm'_eq_one hk
  have hmaps : Set.MapsTo (fun z => ζ * z) B B := by
    intro z hz
    simp only [hB_def, Metric.mem_ball, dist_zero_right] at hz ⊢
    rw [norm_mul, hζ_norm, one_mul]
    exact hz
  -- Step 3: `AnalyticOnNhd ⇒ ContDiffOn ⊤` on `B`.
  have hUnique : UniqueDiffOn ℂ B := hB_open.uniqueDiffOn
  have hContDiff : ContDiffOn ℂ (n : WithTop ℕ∞) F B :=
    (hF_an.contDiffOn hUnique).of_le (by exact_mod_cast le_top)
  -- Step 4: Apply `iteratedDerivWithin_comp_const_smul` at `x = 0`.
  have h_step :
      iteratedDerivWithin n (fun x => F (ζ * x)) B 0 =
        ζ ^ n • iteratedDerivWithin n F B (ζ * 0) :=
    iteratedDerivWithin_comp_const_smul h0_mem hUnique hContDiff ζ hmaps
  rw [mul_zero] at h_step
  -- Step 5: Convert iteratedDerivWithin to iteratedDeriv on the open ball.
  have h_within_to_full_F :
      iteratedDerivWithin n F B 0 = iteratedDeriv n F 0 :=
    iteratedDerivWithin_of_isOpen hB_open h0_mem
  have h_within_to_full_Fcomp :
      iteratedDerivWithin n (fun x => F (ζ * x)) B 0 =
        iteratedDeriv n (fun x => F (ζ * x)) 0 :=
    iteratedDerivWithin_of_isOpen hB_open h0_mem
  rw [h_within_to_full_F, h_within_to_full_Fcomp] at h_step
  -- h_step : iteratedDeriv n (fun x => F (ζ * x)) 0 = ζ^n • iteratedDeriv n F 0.
  -- Step 6: Lift `h_rot` to iterated derivatives.
  have h_eq_iter :
      iteratedDeriv n F 0 = iteratedDeriv n (fun x => F (ζ * x)) 0 :=
    Filter.EventuallyEq.iteratedDeriv_eq n h_rot
  -- Combine: iteratedDeriv n F 0 = ζ^n • iteratedDeriv n F 0.
  have h_fixed :
      iteratedDeriv n F 0 = ζ ^ n • iteratedDeriv n F 0 :=
    h_eq_iter.trans h_step
  -- Step 7: Show ζ^n ≠ 1.
  have hζ_pow_ne_one : ζ ^ n ≠ 1 := fun h => hn (hζ.dvd_of_pow_eq_one n h)
  -- Step 8: From `iteratedDeriv n F 0 = ζ^n • iteratedDeriv n F 0`, deduce vanishing.
  -- (1 - ζ^n) • iteratedDeriv n F 0 = 0; (1 - ζ^n) ≠ 0 in ℂ ⇒ smul_eq_zero gives the result.
  have h_sub : (1 - ζ ^ n) • iteratedDeriv n F 0 = 0 := by
    rw [sub_smul, one_smul, sub_eq_zero]
    exact h_fixed
  have h_sub_ne : (1 - ζ ^ n) ≠ 0 := sub_ne_zero_of_ne (Ne.symm hζ_pow_ne_one)
  exact (smul_eq_zero.mp h_sub).resolve_left h_sub_ne

/-! ### R-sub-development R2 — Taylor-coefficient vanishing bundled with the canonical Taylor power series. -/

omit [T2Space X] [CompactSpace X] [ConnectedSpace X] [ChartedSpace ℂ X]
  [IsManifold 𝓘(ℂ, ℂ) ω X] [StableChartAt ℂ X]
  [T2Space Y] [CompactSpace Y] [ConnectedSpace Y] [ChartedSpace ℂ Y]
  [IsManifold 𝓘(ℂ, ℂ) ω Y] [StableChartAt ℂ Y] in
/--
**R2 — Taylor-coefficient vanishing bundled with the canonical Taylor
power series (sorry-free helper; second R-leaf of the locally-built
rotation-invariant analytic-extension theorem).**

Combining R1 with Mathlib's `AnalyticAt.hasFPowerSeriesAt`, the canonical
Taylor coefficient function `a n := iteratedDeriv n F 0 / n.factorial` of
a ζ-rotation-invariant analytic function `F` near `0` both (i) provides
the formal power series witness `HasFPowerSeriesAt F (ofScalars ℂ a) 0`,
and (ii) vanishes for every `n` with `¬ k ∣ n`.

This bundles everything R3 needs to define the surviving-coefficient
function `b m := a (k * m)` and to prove the convergence of the
corresponding formal series `ofScalars ℂ b`.

Mathlib primitives:
- `AnalyticAt.hasFPowerSeriesAt` (in `IteratedDeriv.Defs`, requires
  `[RCLike 𝕜]` or `[NontriviallyNormedField + CompleteSpace + CharZero]`
  — ℂ satisfies both via `RCLike`).
- R1 (`iteratedDeriv_zero_of_eventually_rotation_invariant`) — the
  iteratedDeriv vanishing this lemma divides by `n!`.
-/
private theorem taylorCoeff_zero_of_eventually_rotation_invariant
    {F : ℂ → ℂ} (hF : AnalyticAt ℂ F 0)
    {k : ℕ} (hk : k ≠ 0) {ζ : ℂ} (hζ : IsPrimitiveRoot ζ k)
    (h_rot : F =ᶠ[𝓝 0] (fun z => F (ζ * z))) :
    HasFPowerSeriesAt F
      (FormalMultilinearSeries.ofScalars ℂ
        (fun n => iteratedDeriv n F 0 / (n.factorial : ℂ))) 0 ∧
    ∀ n, ¬ k ∣ n → iteratedDeriv n F 0 / (n.factorial : ℂ) = 0 := by
  refine ⟨hF.hasFPowerSeriesAt, ?_⟩
  intro n hn
  rw [iteratedDeriv_zero_of_eventually_rotation_invariant hF hk hζ h_rot hn,
      zero_div]

/-! ### R-sub-development R3 — `tsum` reindexing under `n ↦ k * n` for vanish-off-multiples-of-k sequences. -/

omit [T2Space X] [CompactSpace X] [ConnectedSpace X] [ChartedSpace ℂ X]
  [IsManifold 𝓘(ℂ, ℂ) ω X] [StableChartAt ℂ X]
  [T2Space Y] [CompactSpace Y] [ConnectedSpace Y] [ChartedSpace ℂ Y]
  [IsManifold 𝓘(ℂ, ℂ) ω Y] [StableChartAt ℂ Y] in
/--
**R3 — `tsum` reindexing under `n ↦ k * n` for vanish-off-multiples-of-`k`
sequences (sorry-free helper; third R-leaf of the locally-built
rotation-invariant analytic-extension theorem).**

For any sequence `a : ℕ → ℂ` vanishing whenever `¬ k ∣ n` (and `k ≠ 0`),
the `w`-weighted `tsum` reindexes through the surviving multiples of `k`:

  `∑' n, a n * w^n = ∑' m, a (k * m) * w^(k * m)`

This is the direct tsum identity R4 (R-final) will combine with R2's
`HasFPowerSeriesAt`-summability witness to conclude
`G(z^k) = F z` near `0`, where `G(w) := ∑' m, a (k * m) * w^m`.

Mathlib primitive: `Function.Injective.tsum_eq` (in
`Mathlib.Topology.Algebra.InfiniteSum.Basic`, via `to_additive` of
`Function.Injective.tprod_eq` at line ~525):
  `{g : γ → β} (hg : Injective g) {f : β → α} (hf : support f ⊆ Set.range g) :
   ∑' c, f (g c) = ∑' b, f b`.

Applied with `g := (k * ·)` (injective on `ℕ` since `k ≠ 0`),
`f := fun n => a n * w^n`. The support condition holds: if
`a n * w^n ≠ 0`, then `a n ≠ 0`, so `k ∣ n` (contrapositive of the
vanishing hypothesis), so `n ∈ Set.range g`.
-/
private theorem tsum_pow_eq_tsum_pow_of_zero_off_dvd
    {a : ℕ → ℂ} {k : ℕ} (hk : k ≠ 0)
    (h_vanish : ∀ n, ¬ k ∣ n → a n = 0) (w : ℂ) :
    ∑' n, a n * w ^ n = ∑' m, a (k * m) * w ^ (k * m) := by
  -- Step 1: the multiplication-by-k map is injective on `ℕ` (since `k ≠ 0`).
  have hg_inj : Function.Injective (fun m : ℕ => k * m) := by
    intro m₁ m₂ heq
    exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hk) heq
  -- Step 2: support condition. If `a n * w^n ≠ 0`, then `a n ≠ 0`,
  -- hence `k ∣ n` (contrapositive of `h_vanish`), hence `n = k * (n/k) ∈ range g`.
  have h_supp : Function.support (fun n => a n * w ^ n) ⊆
      Set.range (fun m : ℕ => k * m) := by
    intro n hn
    have ha_ne : a n ≠ 0 := by
      intro ha
      apply hn
      simp [ha]
    have h_dvd : k ∣ n := by
      by_contra h
      exact ha_ne (h_vanish n h)
    obtain ⟨m, hm⟩ := h_dvd
    exact ⟨m, hm.symm⟩
  -- Step 3: apply Function.Injective.tsum_eq.
  exact (hg_inj.tsum_eq h_supp).symm

/-! ### R-sub-development R4a — convergence of the surviving-coefficient series. -/

omit [T2Space X] [CompactSpace X] [ConnectedSpace X] [ChartedSpace ℂ X]
  [IsManifold 𝓘(ℂ, ℂ) ω X] [StableChartAt ℂ X]
  [T2Space Y] [CompactSpace Y] [ConnectedSpace Y] [ChartedSpace ℂ Y]
  [IsManifold 𝓘(ℂ, ℂ) ω Y] [StableChartAt ℂ Y] in
/--
**R4a — Convergence of the surviving-coefficient series (sorry-free
helper; fourth R-leaf of the locally-built rotation-invariant
analytic-extension theorem).**

Given a sequence `a : ℕ → ℂ` whose Taylor series
`p := FormalMultilinearSeries.ofScalars ℂ a` has positive radius, and
which vanishes off multiples of `k` (`k ≠ 0`), the formal power series
of the surviving coefficients
`q := FormalMultilinearSeries.ofScalars ℂ (fun m => a (k * m))`
also has positive radius.

Proof: pick `r : ℝ≥0` with `0 < r < (ofScalars ℂ a).radius`. By
`p.summable_nnnorm_mul_pow`, `Summable (fun n => ‖p n‖₊ * r^n)`. Using
the vanishing hypothesis, terms outside `Set.range (k * ·)` are zero,
so by `Function.Injective.hasSum_iff` (with the multiplication-by-k
injection) the reindexed series
`(fun m => ‖p (k*m)‖₊ * r^(k*m)) = (fun m => ‖q m‖₊ * (r^k)^m)`
is also summable. Apply `q.le_radius_of_summable_nnnorm` to get
`(r^k : ℝ≥0∞) ≤ q.radius`. Positivity follows from `r > 0` and `k ≠ 0`.

This is **R4a** in the R-sub-development. R4b (R-final) consumes R4a
to define `G := q.sum` (analytic at `0` via `q.hasFPowerSeriesOnBall`)
and proves the extension identity `F z = G(z^k)`.
-/
private theorem ofScalars_surviving_radius_pos
    {a : ℕ → ℂ} {k : ℕ} (hk : k ≠ 0)
    (h_vanish : ∀ n, ¬ k ∣ n → a n = 0)
    (h_pos : 0 < (FormalMultilinearSeries.ofScalars ℂ a).radius) :
    0 < (FormalMultilinearSeries.ofScalars ℂ (fun m => a (k * m))).radius := by
  set p : FormalMultilinearSeries ℂ ℂ ℂ := FormalMultilinearSeries.ofScalars ℂ a
    with hp_def
  set q : FormalMultilinearSeries ℂ ℂ ℂ :=
    FormalMultilinearSeries.ofScalars ℂ (fun m => a (k * m)) with hq_def
  -- Step 1: pick r : ℝ≥0 with 0 < (r : ℝ≥0∞) < p.radius.
  obtain ⟨r, hr_pos, hr_lt⟩ : ∃ r : ℝ≥0, 0 < r ∧ (r : ℝ≥0∞) < p.radius := by
    rcases ENNReal.lt_iff_exists_nnreal_btwn.mp h_pos with ⟨r, hr_pos, hr_lt⟩
    exact ⟨r, ENNReal.coe_pos.mp hr_pos, hr_lt⟩
  -- Step 2: summability of (fun n => ‖p n‖₊ * r^n).
  have h_summable_a : Summable (fun n : ℕ => ‖p n‖₊ * r ^ n) :=
    p.summable_nnnorm_mul_pow hr_lt
  -- Step 3: for each n, ‖p n‖₊ = ‖a n‖₊. So the vanishing-off-multiples-of-k
  -- carries over: ‖p n‖₊ * r^n = 0 when ¬ k ∣ n.
  have h_pnorm_eq : ∀ n, ‖p n‖₊ = ‖a n‖₊ := by
    intro n
    have : ‖p n‖₊ = ‖a n‖₊ * ‖ContinuousMultilinearMap.mkPiAlgebraFin ℂ n ℂ‖₊ := by
      simp [hp_def, FormalMultilinearSeries.ofScalars, nnnorm_smul]
    rw [this, show
      ‖ContinuousMultilinearMap.mkPiAlgebraFin ℂ n ℂ‖₊ = 1 from
        Subtype.ext (ContinuousMultilinearMap.norm_mkPiAlgebraFin), mul_one]
  -- Similarly for q.
  have h_qnorm_eq : ∀ m, ‖q m‖₊ = ‖a (k * m)‖₊ := by
    intro m
    have : ‖q m‖₊ = ‖a (k * m)‖₊ * ‖ContinuousMultilinearMap.mkPiAlgebraFin ℂ m ℂ‖₊ := by
      simp [hq_def, FormalMultilinearSeries.ofScalars, nnnorm_smul]
    rw [this, show
      ‖ContinuousMultilinearMap.mkPiAlgebraFin ℂ m ℂ‖₊ = 1 from
        Subtype.ext (ContinuousMultilinearMap.norm_mkPiAlgebraFin), mul_one]
  -- Step 4: vanishing.
  have hp_vanish : ∀ n, ¬ k ∣ n → ‖p n‖₊ * r ^ n = 0 := by
    intro n hn
    rw [h_pnorm_eq n, h_vanish n hn]
    simp
  -- Step 5: reindex via Function.Injective.hasSum_iff.
  have hg_inj : Function.Injective (fun m : ℕ => k * m) := fun m₁ m₂ heq =>
    Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hk) heq
  -- Term equality: (fun m => ‖q m‖₊ * (r^k)^m) = (fun n => ‖p n‖₊ * r^n) ∘ (fun m => k*m).
  have h_term_eq : ∀ m : ℕ,
      ‖q m‖₊ * (r ^ k) ^ m = ‖p (k * m)‖₊ * r ^ (k * m) := by
    intro m
    rw [h_qnorm_eq m, h_pnorm_eq (k * m), ← pow_mul, Nat.mul_comm k m]
  -- Off-range vanishing for the composition.
  have h_off_range : ∀ n, n ∉ Set.range (fun m : ℕ => k * m) →
      ‖p n‖₊ * r ^ n = 0 := by
    intro n hn_range
    have hn_ndvd : ¬ k ∣ n := fun ⟨m, hm⟩ => hn_range ⟨m, hm.symm⟩
    exact hp_vanish n hn_ndvd
  -- Apply Function.Injective.hasSum_iff to lift summability through the injection.
  obtain ⟨s, hs⟩ := h_summable_a
  have h_summable_b : Summable (fun m : ℕ => ‖q m‖₊ * (r ^ k) ^ m) := by
    refine ⟨s, ?_⟩
    rw [funext h_term_eq]
    exact (hg_inj.hasSum_iff h_off_range).mpr hs
  -- Step 6: apply le_radius_of_summable_nnnorm.
  have hrk_le_q_radius : (r ^ k : ℝ≥0∞) ≤ q.radius := by
    have := q.le_radius_of_summable_nnnorm h_summable_b
    -- The lemma gives ↑(r ^ k) ≤ q.radius; coerce.
    simpa using this
  -- Step 7: r^k > 0.
  have hrk_pos : (0 : ℝ≥0) < r ^ k := pow_pos hr_pos k
  refine lt_of_lt_of_le ?_ hrk_le_q_radius
  exact_mod_cast hrk_pos

/-! ### R-sub-development R4b — rotation-invariant analytic-extension theorem (R-final). -/

omit [T2Space X] [CompactSpace X] [ConnectedSpace X] [ChartedSpace ℂ X]
  [IsManifold 𝓘(ℂ, ℂ) ω X] [StableChartAt ℂ X]
  [T2Space Y] [CompactSpace Y] [ConnectedSpace Y] [ChartedSpace ℂ Y]
  [IsManifold 𝓘(ℂ, ℂ) ω Y] [StableChartAt ℂ Y] in
/--
**R4b (R-final) — Rotation-invariant analytic-extension theorem
(sorry-free helper; caps the locally-built pure-ℂ R-sub-development
that replaces the Mathlib v4.28.0 gap).**

If `F : ℂ → ℂ` is analytic at `0`, ζ is a primitive `k`-th root of unity
(`k ≠ 0`), and `F =ᶠ[𝓝 0] (fun z => F (ζ * z))`, then there exists
`G : ℂ → ℂ` analytic at `0` with `F z = G (z^k)` near `0`.

Proof: consume R4a for convergence (`0 < q.radius`); define `G := q.sum`;
`G` is analytic via `q.hasFPowerSeriesOnBall`; the extension identity
`F z = G(z^k)` follows from reindexing the HasSum identity of `F`'s
power series via `Function.Injective.hasSum_iff` plus `HasSum.unique`
matching the LHS `HasSum` against the RHS `HasSum` (for `q` applied at `z^k`).

The eball-membership step `z^k ∈ Metric.eball 0 q.radius` is established
by an internal re-derivation of the convergence bound (using the same
`Function.Injective.hasSum_iff` reindex as R4a, but with the explicit
`r > 0` we choose here so we can chain strict inequalities).
-/
private theorem exists_analytic_extension_of_rotation_invariant
    {F : ℂ → ℂ} (hF : AnalyticAt ℂ F 0)
    {k : ℕ} (hk : k ≠ 0) {ζ : ℂ} (hζ : IsPrimitiveRoot ζ k)
    (h_rot : F =ᶠ[𝓝 0] (fun z => F (ζ * z))) :
    ∃ G : ℂ → ℂ, AnalyticAt ℂ G 0 ∧ F =ᶠ[𝓝 0] (fun z => G (z^k)) := by
  -- Step 1: extract Taylor data via R2.
  obtain ⟨hF_hpw, h_vanish⟩ :=
    taylorCoeff_zero_of_eventually_rotation_invariant hF hk hζ h_rot
  set a : ℕ → ℂ := fun n => iteratedDeriv n F 0 / (n.factorial : ℂ) with ha_def
  set p : FormalMultilinearSeries ℂ ℂ ℂ := FormalMultilinearSeries.ofScalars ℂ a
    with hp_def
  set q : FormalMultilinearSeries ℂ ℂ ℂ :=
    FormalMultilinearSeries.ofScalars ℂ (fun m => a (k * m)) with hq_def
  -- Step 2: unpack HasFPowerSeriesAt → HasFPowerSeriesOnBall.
  obtain ⟨rF, hF_onBall⟩ := hF_hpw
  have hrF_pos : 0 < rF := hF_onBall.r_pos
  have hp_radius_pos : 0 < p.radius := lt_of_lt_of_le hrF_pos hF_onBall.r_le
  -- Step 3: pick r : ℝ≥0 with 0 < r and (r : ℝ≥0∞) < min p.radius rF.
  obtain ⟨r, hr_pos, hr_lt_p, hr_lt_rF⟩ :
      ∃ r : ℝ≥0, 0 < r ∧ (r : ℝ≥0∞) < p.radius ∧ (r : ℝ≥0∞) < rF := by
    rcases ENNReal.lt_iff_exists_nnreal_btwn.mp
      (lt_min hp_radius_pos hrF_pos) with ⟨r, hr_pos_coe, hr_lt_min⟩
    refine ⟨r, ENNReal.coe_pos.mp hr_pos_coe, ?_, ?_⟩
    · exact lt_of_lt_of_le hr_lt_min (min_le_left _ _)
    · exact lt_of_lt_of_le hr_lt_min (min_le_right _ _)
  -- Step 4: re-derive (r^k : ℝ≥0∞) ≤ q.radius (same skeleton as R4a, but
  -- with our chosen `r` to keep the strict inequality chain explicit).
  have hr_lt_p_radius : (r : ℝ≥0∞) < p.radius := hr_lt_p
  have h_summable_a : Summable (fun n : ℕ => ‖p n‖₊ * r ^ n) :=
    p.summable_nnnorm_mul_pow hr_lt_p_radius
  have h_pnorm_eq : ∀ n, ‖p n‖₊ = ‖a n‖₊ := by
    intro n
    have : ‖p n‖₊ = ‖a n‖₊ * ‖ContinuousMultilinearMap.mkPiAlgebraFin ℂ n ℂ‖₊ := by
      simp [hp_def, FormalMultilinearSeries.ofScalars, nnnorm_smul]
    rw [this, show
      ‖ContinuousMultilinearMap.mkPiAlgebraFin ℂ n ℂ‖₊ = 1 from
        Subtype.ext (ContinuousMultilinearMap.norm_mkPiAlgebraFin), mul_one]
  have h_qnorm_eq : ∀ m, ‖q m‖₊ = ‖a (k * m)‖₊ := by
    intro m
    have : ‖q m‖₊ = ‖a (k * m)‖₊ * ‖ContinuousMultilinearMap.mkPiAlgebraFin ℂ m ℂ‖₊ := by
      simp [hq_def, FormalMultilinearSeries.ofScalars, nnnorm_smul]
    rw [this, show
      ‖ContinuousMultilinearMap.mkPiAlgebraFin ℂ m ℂ‖₊ = 1 from
        Subtype.ext (ContinuousMultilinearMap.norm_mkPiAlgebraFin), mul_one]
  have hp_vanish_norm : ∀ n, ¬ k ∣ n → ‖p n‖₊ * r ^ n = 0 := by
    intro n hn
    rw [h_pnorm_eq n,
        show a n = 0 from (by
          have := h_vanish n hn
          simp_all)]
    simp
  have hg_inj : Function.Injective (fun m : ℕ => k * m) := fun m₁ m₂ heq =>
    Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hk) heq
  have h_term_eq : ∀ m : ℕ,
      ‖q m‖₊ * (r ^ k) ^ m = ‖p (k * m)‖₊ * r ^ (k * m) := by
    intro m
    rw [h_qnorm_eq m, h_pnorm_eq (k * m), ← pow_mul, Nat.mul_comm k m]
  have h_off_range : ∀ n, n ∉ Set.range (fun m : ℕ => k * m) →
      ‖p n‖₊ * r ^ n = 0 := by
    intro n hn_range
    exact hp_vanish_norm n (fun ⟨m, hm⟩ => hn_range ⟨m, hm.symm⟩)
  obtain ⟨s, hs⟩ := h_summable_a
  have h_summable_b : Summable (fun m : ℕ => ‖q m‖₊ * (r ^ k) ^ m) := by
    refine ⟨s, ?_⟩
    rw [funext h_term_eq]
    exact (hg_inj.hasSum_iff h_off_range).mpr hs
  have hrk_le_q_radius : (r ^ k : ℝ≥0∞) ≤ q.radius := by
    have := q.le_radius_of_summable_nnnorm h_summable_b
    simpa using this
  -- Step 5: q.radius positivity (follows from r^k > 0).
  have hrk_pos : (0 : ℝ≥0) < r ^ k := pow_pos hr_pos k
  have hq_radius_pos : 0 < q.radius :=
    lt_of_lt_of_le (by exact_mod_cast hrk_pos) hrk_le_q_radius
  -- Step 6: define G := q.sum; analyticity via q.hasFPowerSeriesOnBall.
  refine ⟨q.sum, (q.hasFPowerSeriesOnBall hq_radius_pos).analyticAt, ?_⟩
  -- Step 7: F =ᶠ[𝓝 0] (fun z => q.sum (z^k)).
  -- Pick a ball of radius `r` (≤ rF and giving r^k ≤ q.radius for z^k).
  filter_upwards [Metric.eball_mem_nhds (0 : ℂ) (show 0 < (r : ℝ≥0∞) from by
    exact_mod_cast hr_pos)] with z hz_in_r_ball
  -- ‖z‖₊ < r.
  have h_z_nnnorm_lt : (‖z‖₊ : ℝ≥0∞) < r := by
    simpa [Metric.mem_eball, edist_zero_right] using hz_in_r_ball
  -- z ∈ eball 0 rF (since r < rF).
  have hz_in_rF : z ∈ Metric.eball (0 : ℂ) rF := by
    rw [Metric.mem_eball, edist_zero_right]
    exact lt_of_lt_of_le (lt_trans h_z_nnnorm_lt hr_lt_rF) (le_refl _)
  -- HasSum at z via hF_onBall.
  have hHasSum_a : HasSum (fun n : ℕ => p n (fun _ : Fin n => z)) (F z) := by
    have := hF_onBall.hasSum hz_in_rF
    simpa using this
  -- Vanishing: for n ∉ Set.range (k * ·), p n (fun _ => z) = 0.
  have h_pn_vanish : ∀ n, n ∉ Set.range (fun m : ℕ => k * m) →
      p n (fun _ : Fin n => z) = 0 := by
    intro n hn_range
    have hn_ndvd : ¬ k ∣ n := fun ⟨m, hm⟩ => hn_range ⟨m, hm.symm⟩
    have ha_zero : a n = 0 := by
      have := h_vanish n hn_ndvd
      simp_all
    simp [hp_def, ha_zero]
  -- HasSum reindex via Function.Injective.hasSum_iff.
  have hHasSum_b_via_z : HasSum (fun m : ℕ => p (k * m) (fun _ : Fin (k * m) => z))
      (F z) :=
    (hg_inj.hasSum_iff h_pn_vanish).mpr hHasSum_a
  -- Term equality: p (k*m) (fun _ => z) = q m (fun _ => z^k).
  have h_term_zk : ∀ m : ℕ,
      p (k * m) (fun _ : Fin (k * m) => z) = q m (fun _ : Fin m => z^k) := by
    intro m
    -- p (k*m) (fun _ => z) = a (k*m) • z^(k*m) (via ofScalars_apply_eq).
    -- q m (fun _ => z^k) = a (k*m) • (z^k)^m = a (k*m) • z^(k*m).
    have h1 : p (k * m) (fun _ : Fin (k * m) => z) = a (k * m) • z ^ (k * m) :=
      FormalMultilinearSeries.ofScalars_apply_eq (E := ℂ) a z (k * m)
    have h2 : q m (fun _ : Fin m => z ^ k) = a (k * m) • (z ^ k) ^ m :=
      FormalMultilinearSeries.ofScalars_apply_eq (E := ℂ) (fun m => a (k * m))
        (z ^ k) m
    rw [h1, h2, ← pow_mul, Nat.mul_comm k m]
  have hHasSum_q_at_zk : HasSum (fun m : ℕ => q m (fun _ : Fin m => z ^ k)) (F z) :=
    hHasSum_b_via_z.congr_fun (fun m => (h_term_zk m).symm)
  -- z^k ∈ eball 0 q.radius (strict).
  have hzk_in_q_eball : z ^ k ∈ Metric.eball (0 : ℂ) q.radius := by
    rw [Metric.mem_eball, edist_zero_right]
    rw [enorm_pow]
    -- Goal: ‖z‖ₑ ^ k < q.radius.
    -- ‖z‖ₑ = (‖z‖₊ : ℝ≥0∞), so this is the same as (‖z‖₊ : ℝ≥0∞)^k < q.radius.
    -- We have h_z_nnnorm_lt : (‖z‖₊ : ℝ≥0∞) < (r : ℝ≥0∞), and hrk_le_q_radius.
    have h_strict : ‖z‖ₑ ^ k < (r : ℝ≥0∞) ^ k := by
      have h_enorm_eq : ‖z‖ₑ = (‖z‖₊ : ℝ≥0∞) := rfl
      rw [h_enorm_eq]
      exact (ENNReal.pow_lt_pow_left_iff hk).mpr h_z_nnnorm_lt
    refine lt_of_lt_of_le h_strict ?_
    -- (r : ℝ≥0∞)^k = ((r^k : ℝ≥0) : ℝ≥0∞) ≤ q.radius.
    rw [show (r : ℝ≥0∞) ^ k = ((r ^ k : ℝ≥0) : ℝ≥0∞) from by push_cast; ring]
    exact hrk_le_q_radius
  -- HasSum from q.hasFPowerSeriesOnBall at z^k.
  have hHasSum_qsum : HasSum (fun m : ℕ => q m (fun _ : Fin m => z ^ k))
      (q.sum (z ^ k)) := by
    have hball : z ^ k ∈ Metric.eball (0 : ℂ) q.radius := hzk_in_q_eball
    have := (q.hasFPowerSeriesOnBall hq_radius_pos).hasSum hball
    simpa using this
  -- Conclude F z = q.sum (z^k) by HasSum.unique.
  exact (hHasSum_q_at_zk.unique hHasSum_qsum)

/-! ### DA — Chart-local cancellation `H = t^(k-1) · g(t^k)` via R-final. -/

omit [T2Space X] [CompactSpace X] [ConnectedSpace X] [ChartedSpace ℂ X]
  [IsManifold 𝓘(ℂ, ℂ) ω X] [StableChartAt ℂ X]
  [T2Space Y] [CompactSpace Y] [ConnectedSpace Y] [ChartedSpace ℂ Y]
  [IsManifold 𝓘(ℂ, ℂ) ω Y] [StableChartAt ℂ Y] in
/-- DA Layer A — roots-of-unity sum, `k ∣ ℓ` case. -/
private theorem rootsOfUnity_pow_sum_eq_k_of_dvd
    {k : ℕ} {ζ : ℂ} (hζ : IsPrimitiveRoot ζ k)
    {ℓ : ℕ} (hℓ : k ∣ ℓ) :
    (∑ j ∈ Finset.range k, ζ ^ (j * ℓ)) = (k : ℂ) := by
  have h_each : ∀ j ∈ Finset.range k, ζ ^ (j * ℓ) = 1 := by
    intro j _
    obtain ⟨m, rfl⟩ := hℓ
    rw [show j * (k * m) = k * (j * m) by ring, pow_mul, hζ.pow_eq_one, one_pow]
  rw [Finset.sum_congr rfl h_each, Finset.sum_const, Finset.card_range,
      Nat.smul_one_eq_cast]

omit [T2Space X] [CompactSpace X] [ConnectedSpace X] [ChartedSpace ℂ X]
  [IsManifold 𝓘(ℂ, ℂ) ω X] [StableChartAt ℂ X]
  [T2Space Y] [CompactSpace Y] [ConnectedSpace Y] [ChartedSpace ℂ Y]
  [IsManifold 𝓘(ℂ, ℂ) ω Y] [StableChartAt ℂ Y] in
/-- DA Layer A — roots-of-unity sum, `k ∤ ℓ` case. -/
private theorem rootsOfUnity_pow_sum_eq_zero_of_not_dvd
    {k : ℕ} {ζ : ℂ} (hζ : IsPrimitiveRoot ζ k)
    {ℓ : ℕ} (hℓ : ¬ k ∣ ℓ) :
    (∑ j ∈ Finset.range k, ζ ^ (j * ℓ)) = 0 := by
  have h_each : ∀ j ∈ Finset.range k, ζ ^ (j * ℓ) = (ζ ^ ℓ) ^ j := by
    intro j _
    rw [← pow_mul, Nat.mul_comm j ℓ, pow_mul]
  rw [Finset.sum_congr rfl h_each]
  have hζℓ_ne_one : ζ ^ ℓ ≠ 1 := fun h => hℓ (hζ.dvd_of_pow_eq_one ℓ h)
  rw [geom_sum_eq hζℓ_ne_one k]
  have hpow_k_eq_one : (ζ ^ ℓ) ^ k = 1 := by
    rw [← pow_mul, Nat.mul_comm, pow_mul, hζ.pow_eq_one, one_pow]
  rw [hpow_k_eq_one, sub_self, zero_div]

/--
**DA — Chart-local cancellation `rotation_avg_eq_g_pow_k`
(sorry-free helper; the central analytic identity behind L2085).**

Given `h : ℂ → ℂ` analytic at `0`, primitive `k`-th root `ζ` (`k > 0`):
```
H(t) := ∑_{j ∈ Fin k} ζ^j · h(ζ^j · t) = t^(k-1) · g(t^k)
```
near `0` for some `g : ℂ → ℂ` analytic at `0`.

Proof structure (manager's §8-internal four helpers within this one commit):
- Step 1: `H` analytic at `0` (finite sum of compositions).
- Step 2: `iteratedDeriv m H 0 = 0` for `m < k-1` (via R1-style
  `iteratedDerivWithin_comp_const_smul` on an open ball + Layer A
  roots-of-unity cancellation).
- Step 3: Factor `H(t) = t^(k-1) · gtilde(t)` with `gtilde` analytic at `0`
  (via `natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero` +
  `exists_eventuallyEq_pow_smul_nonzero_iff` /
  `analyticOrderNatAt_eq_iff` from `Analytic/IsolatedZeros.lean` /
  `Analytic/Order.lean`).
- Step 4: Show `gtilde` is ζ-invariant near `0` (from `H`'s ζ^(k-1)-equivariance
  + the `(ζ·t)^(k-1) = ζ^(k-1) · t^(k-1)` cancellation); apply R-final
  (`exists_analytic_extension_of_rotation_invariant`) to get `gtilde(t) = g(t^k)`;
  multiply through.

The weight `ζ^j` here equals `ζ^(-j(k-1))` (via `ζ^(-(k-1)) = ζ^(k-(k-1)) = ζ`),
matching the chart-local application's `(ζ^j · kthRoot w)^(-(k-1))` factor.
-/
private theorem rotation_avg_eq_g_pow_k
    {h : ℂ → ℂ} (hh : AnalyticAt ℂ h 0)
    {k : ℕ} (hk_pos : 0 < k) {ζ : ℂ} (hζ : IsPrimitiveRoot ζ k) :
    ∃ g : ℂ → ℂ, AnalyticAt ℂ g 0 ∧
      ∀ᶠ t in 𝓝 (0 : ℂ),
        (∑ j ∈ Finset.range k, ζ ^ j * h (ζ ^ j * t))
            = t ^ (k - 1) * g (t ^ k) := by
  -- Define H.
  set H : ℂ → ℂ := fun t => ∑ j ∈ Finset.range k, ζ ^ j * h (ζ ^ j * t)
    with hH_def
  -- ============================================================
  -- Step 1: H is analytic at 0.
  -- ============================================================
  have hH_an : AnalyticAt ℂ H 0 := by
    refine (Finset.range k).analyticAt_fun_sum ?_
    intro j _
    have h_mul_an : AnalyticAt ℂ (fun t : ℂ => ζ ^ j * t) 0 :=
      analyticAt_const.mul analyticAt_id
    have h_val : (fun t : ℂ => ζ ^ j * t) 0 = 0 := by simp
    have hh_at_shift : AnalyticAt ℂ h ((fun t : ℂ => ζ ^ j * t) 0) := by
      rw [h_val]; exact hh
    exact analyticAt_const.mul (hh_at_shift.comp h_mul_an)
  -- ============================================================
  -- Step 2: iteratedDeriv m H 0 = 0 for m < k-1.
  -- ============================================================
  obtain ⟨r, hr_pos, hh_an_ball⟩ := hh.exists_ball_analyticOnNhd
  set B : Set ℂ := Metric.ball 0 r with hB_def
  have hB_open : IsOpen B := Metric.isOpen_ball
  have h0_mem : (0 : ℂ) ∈ B := by simp [hB_def, Metric.mem_ball, hr_pos]
  have hUnique : UniqueDiffOn ℂ B := hB_open.uniqueDiffOn
  have hζ_norm : ‖ζ‖ = 1 := hζ.norm'_eq_one hk_pos.ne'
  have hζj_norm : ∀ j : ℕ, ‖(ζ ^ j : ℂ)‖ = 1 := fun j => by
    rw [norm_pow, hζ_norm, one_pow]
  have hmaps : ∀ j : ℕ, Set.MapsTo (fun z : ℂ => ζ ^ j * z) B B := by
    intro j z hz
    simp only [hB_def, Metric.mem_ball, dist_zero_right] at hz ⊢
    rw [norm_mul, hζj_norm j, one_mul]
    exact hz
  have hh_contDiff_on : ContDiffOn ℂ (⊤ : WithTop ℕ∞) h B :=
    hh_an_ball.contDiffOn hUnique
  -- Inner derivative computation for each j.
  have h_inDeriv : ∀ (m : ℕ) (j : ℕ),
      iteratedDeriv m (fun t : ℂ => h (ζ ^ j * t)) 0 =
        (ζ ^ j) ^ m • iteratedDeriv m h 0 := by
    intro m j
    have hh_at_m : ContDiffOn ℂ (m : WithTop ℕ∞) h B :=
      hh_contDiff_on.of_le (by exact_mod_cast le_top)
    have h_step_comp :
        iteratedDerivWithin m (fun t : ℂ => h (ζ ^ j * t)) B 0 =
          (ζ ^ j) ^ m • iteratedDerivWithin m h B (ζ ^ j * 0) :=
      iteratedDerivWithin_comp_const_smul h0_mem hUnique hh_at_m (ζ ^ j) (hmaps j)
    have hwithin_h : iteratedDerivWithin m h B 0 = iteratedDeriv m h 0 :=
      iteratedDerivWithin_of_isOpen hB_open h0_mem
    have hwithin_comp :
        iteratedDerivWithin m (fun t : ℂ => h (ζ ^ j * t)) B 0 =
          iteratedDeriv m (fun t : ℂ => h (ζ ^ j * t)) 0 :=
      iteratedDerivWithin_of_isOpen hB_open h0_mem
    rw [← hwithin_comp, h_step_comp, mul_zero, hwithin_h]
  -- Full per-summand derivative with the ζ^j multiplicative weight.
  have h_inDeriv_full : ∀ (m : ℕ) (j : ℕ),
      iteratedDeriv m (fun t : ℂ => ζ ^ j * h (ζ ^ j * t)) 0 =
        ζ ^ j * ((ζ ^ j) ^ m * iteratedDeriv m h 0) := by
    intro m j
    have h_smul : (fun t : ℂ => ζ ^ j * h (ζ ^ j * t)) =
        (ζ ^ j : ℂ) • (fun t : ℂ => h (ζ ^ j * t)) := by
      funext t; simp [Pi.smul_apply, smul_eq_mul]
    rw [h_smul, iteratedDeriv_const_smul_field (ζ ^ j) (fun t => h (ζ ^ j * t)),
        h_inDeriv m j, smul_eq_mul, smul_eq_mul]
  -- The vanishing lemma.
  have hH_vanish : ∀ m : ℕ, m < k - 1 → iteratedDeriv m H 0 = 0 := by
    intro m hm
    have h_iter_sum : iteratedDeriv m H 0 =
        iteratedDeriv m h 0 * ∑ j ∈ Finset.range k, ζ ^ (j * (m + 1)) := by
      rw [hH_def]
      have h_summand_contDiff : ∀ j ∈ Finset.range k,
          ContDiffAt ℂ (m : WithTop ℕ∞) (fun t : ℂ => ζ ^ j * h (ζ ^ j * t)) 0 := by
        intro j _
        have h_mul_an : AnalyticAt ℂ (fun t : ℂ => ζ ^ j * t) 0 :=
          analyticAt_const.mul analyticAt_id
        have h_val : (fun t : ℂ => ζ ^ j * t) 0 = 0 := by simp
        have hh_at_shift : AnalyticAt ℂ h ((fun t : ℂ => ζ ^ j * t) 0) := by
          rw [h_val]; exact hh
        have h_comp_an : AnalyticAt ℂ (fun t : ℂ => h (ζ ^ j * t)) 0 :=
          hh_at_shift.comp h_mul_an
        exact (analyticAt_const.mul h_comp_an).contDiffAt
      rw [iteratedDeriv_fun_sum h_summand_contDiff]
      simp_rw [h_inDeriv_full]
      have h_rearrange : ∀ j : ℕ,
          ζ ^ j * ((ζ ^ j) ^ m * iteratedDeriv m h 0) =
            iteratedDeriv m h 0 * ζ ^ (j * (m + 1)) := by
        intro j
        rw [show j * (m + 1) = j + j * m by ring, pow_add, ← pow_mul]
        ring
      simp_rw [h_rearrange]
      rw [← Finset.mul_sum]
    rw [h_iter_sum]
    have hmp1_pos : 0 < m + 1 := Nat.succ_pos m
    have hmp1_lt_k : m + 1 < k := by omega
    have hk_not_dvd : ¬ k ∣ (m + 1) := fun hdvd =>
      Nat.not_lt.mpr (Nat.le_of_dvd hmp1_pos hdvd) hmp1_lt_k
    rw [rootsOfUnity_pow_sum_eq_zero_of_not_dvd hζ hk_not_dvd, mul_zero]
  -- ============================================================
  -- Step 3: H_factor — H(t) = t^(k-1) * gtilde(t), gtilde analytic at 0.
  -- ============================================================
  -- From Step 2 + natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero:
  --   (k-1 : ℕ∞) ≤ analyticOrderAt H 0.
  have h_order_ge : (↑(k - 1) : ℕ∞) ≤ analyticOrderAt H 0 := by
    rw [natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero hH_an]
    intro i hi
    have hi_nat : i < k - 1 := by exact_mod_cast hi
    exact hH_vanish i hi_nat
  -- Split on whether H is identically zero near 0.
  by_cases hH_zero_event : ∀ᶠ t in 𝓝 (0 : ℂ), H t = 0
  · -- H = 0 near 0. Take g = 0; identity becomes 0 = t^(k-1) · 0 = 0.
    refine ⟨0, analyticAt_const, ?_⟩
    filter_upwards [hH_zero_event] with t ht
    simp only [hH_def] at ht
    rw [ht]
    simp
  · -- H ≢ 0 near 0. Extract a factorization via exists_eventuallyEq_pow_smul.
    obtain ⟨n, g₀, hg₀_an, hg₀_ne, hH_factored_n⟩ :=
      (hH_an.exists_eventuallyEq_pow_smul_nonzero_iff).mpr hH_zero_event
    -- analyticOrderAt H 0 ≠ ⊤ since H is not eventually 0.
    have h_order_ne_top : analyticOrderAt H 0 ≠ ⊤ := by
      intro h_eq_top
      exact hH_zero_event (analyticOrderAt_eq_top.mp h_eq_top)
    -- analyticOrderNatAt H 0 = n by uniqueness of factorization.
    have h_n_eq : analyticOrderNatAt H 0 = n :=
      (hH_an.analyticOrderNatAt_eq_iff h_order_ne_top).mpr
        ⟨g₀, hg₀_an, hg₀_ne, hH_factored_n⟩
    -- n ≥ k - 1 from h_order_ge.
    have hn_ge : n ≥ k - 1 := by
      have h_nat_eq : analyticOrderAt H 0 = (n : ℕ∞) := by
        rw [← h_n_eq]
        exact (Nat.cast_analyticOrderNatAt h_order_ne_top).symm
      rw [h_nat_eq] at h_order_ge
      exact_mod_cast h_order_ge
    -- Define gtilde := fun t => t^(n - (k - 1)) * g₀ t. Analytic at 0.
    set gtilde : ℂ → ℂ := fun t => t ^ (n - (k - 1)) * g₀ t with hgtilde_def
    have hgtilde_an : AnalyticAt ℂ gtilde 0 := by
      have : AnalyticAt ℂ (fun t : ℂ => t ^ (n - (k - 1))) 0 := by
        exact analyticAt_id.pow _
      exact this.mul hg₀_an
    -- H(t) = t^(k-1) · gtilde(t) eventually near 0.
    have hH_eq_factored :
        H =ᶠ[𝓝 (0 : ℂ)] fun t => t ^ (k - 1) * gtilde t := by
      filter_upwards [hH_factored_n] with t ht
      rw [ht]
      simp only [sub_zero, smul_eq_mul, hgtilde_def]
      rw [← mul_assoc, ← pow_add]
      congr 2
      omega
    -- ============================================================
    -- Step 4: gtilde ζ-invariance + R-final + final identity.
    -- ============================================================
    -- Show gtilde is ζ-invariant near 0 (i.e., gtilde(ζ·t) = gtilde(t) eventually).
    -- This uses: H(ζ·t) = ζ^(k-1) · H(t) (computed from H's definition),
    -- combined with H = t^(k-1) · gtilde via hH_eq_factored.
    -- From hH_eq_factored at ζ·t: H(ζ·t) = (ζ·t)^(k-1) · gtilde(ζ·t) = ζ^(k-1) · t^(k-1) · gtilde(ζ·t).
    -- And: ζ^(k-1) · H(t) = ζ^(k-1) · t^(k-1) · gtilde(t).
    -- Equating: gtilde(ζ·t) = gtilde(t).
    -- First: H(ζ·t) = ζ^(k-1) · H(t) (a direct calculation, no extra hypothesis needed).
    have hH_equivariant : ∀ t : ℂ, H (ζ * t) = ζ ^ (k - 1) * H t := by
      intro t
      simp only [hH_def, Finset.mul_sum]
      -- We use Finset.sum_bij with the cyclic shift σ : j ↦ (j+1) % k.
      classical
      -- σ : range k → range k, σ i = (i + k - 1) % k (cyclic shift by -1).
      let σ : ℕ → ℕ := fun i => (i + k - 1) % k
      have hσ_mem : ∀ i ∈ Finset.range k, σ i ∈ Finset.range k := fun i _ => by
        refine Finset.mem_range.mpr ?_
        exact Nat.mod_lt _ hk_pos
      have hσ_inj : Set.InjOn σ (Finset.range k : Set ℕ) := by
        intro i hi i' hi' h_eq
        simp only [Finset.mem_coe, Finset.mem_range] at hi hi'
        simp only [σ] at h_eq
        -- (i+k-1) % k = (i'+k-1) % k.
        -- Case i = 0: σ i = (k-1) % k = k-1. Case i ≥ 1: σ i = i - 1.
        rcases Nat.eq_zero_or_pos i with hi0 | hi_pos
        · rcases Nat.eq_zero_or_pos i' with hi'0 | hi'_pos
          · omega
          · subst hi0
            rw [show (0 + k - 1) % k = k - 1 from by
                  rw [Nat.zero_add, Nat.mod_eq_of_lt (by omega : k - 1 < k)]] at h_eq
            rw [show (i' + k - 1) % k = i' - 1 from by
                  rw [show i' + k - 1 = (i' - 1) + k from by omega,
                      Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]] at h_eq
            omega
        · rcases Nat.eq_zero_or_pos i' with hi'0 | hi'_pos
          · subst hi'0
            rw [show (0 + k - 1) % k = k - 1 from by
                  rw [Nat.zero_add, Nat.mod_eq_of_lt (by omega : k - 1 < k)]] at h_eq
            rw [show (i + k - 1) % k = i - 1 from by
                  rw [show i + k - 1 = (i - 1) + k from by omega,
                      Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]] at h_eq
            omega
          · rw [show (i + k - 1) % k = i - 1 from by
                  rw [show i + k - 1 = (i - 1) + k from by omega,
                      Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]] at h_eq
            rw [show (i' + k - 1) % k = i' - 1 from by
                  rw [show i' + k - 1 = (i' - 1) + k from by omega,
                      Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]] at h_eq
            omega
      have hσ_surj : Set.SurjOn σ (Finset.range k : Set ℕ) (Finset.range k : Set ℕ) := by
        intro j hj
        rw [Finset.mem_coe, Finset.mem_range] at hj
        -- Need: ∃ i ∈ range k, σ i = j. Take i = (j + 1) % k.
        refine ⟨(j + 1) % k, ?_, ?_⟩
        · rw [Finset.mem_coe, Finset.mem_range]
          exact Nat.mod_lt _ hk_pos
        · simp only [σ]
          by_cases hjk : j + 1 = k
          · rw [hjk, Nat.mod_self]
            rw [show (0 + k - 1) % k = k - 1 from by
                  rw [Nat.zero_add, Nat.mod_eq_of_lt (by omega : k - 1 < k)]]
            omega
          · have hjk_lt : j + 1 < k := by omega
            rw [Nat.mod_eq_of_lt hjk_lt]
            rw [show (j + 1 + k - 1) % k = (j + k) % k from by
                  congr 1; omega]
            rw [Nat.add_mod_right]
            exact Nat.mod_eq_of_lt hj
      -- Apply Finset.sum_nbij with σ.
      rw [show (∑ j ∈ Finset.range k, ζ ^ j * h (ζ ^ j * (ζ * t)))
          = ∑ i ∈ Finset.range k, ζ ^ ((i + k - 1) % k) * h (ζ ^ i * t)
          from ?_]
      · -- Show RHS = ∑_i ζ^(k-1) * (ζ^i * h(ζ^i * t)).
        refine Finset.sum_congr rfl ?_
        intros i hi
        have hi_lt : i < k := Finset.mem_range.mp hi
        -- ζ^((i+k-1) % k) = ζ^(i+k-1) = ζ^(k-1+i) = ζ^(k-1) * ζ^i.
        have h_pow_eq : ζ ^ ((i + k - 1) % k) = ζ ^ (k - 1) * ζ ^ i := by
          have h_idx_eq : (i + k - 1) % k + k * ((i + k - 1) / k) = i + k - 1 :=
            Nat.mod_add_div _ _
          have h_mod_eq : (i + k - 1) % k = i + k - 1 - k * ((i + k - 1) / k) := by omega
          -- Use ζ^k = 1 to absorb the k * (i+k-1)/k part.
          conv_lhs => rw [show ζ ^ ((i + k - 1) % k)
                            = ζ ^ ((i + k - 1) % k) * (ζ ^ k) ^ ((i + k - 1) / k)
                          from by rw [hζ.pow_eq_one, one_pow, mul_one]]
          rw [← pow_mul, ← pow_add, show (i + k - 1) % k + k * ((i + k - 1) / k)
                                       = i + k - 1 from h_idx_eq]
          rw [show i + k - 1 = (k - 1) + i from by omega, pow_add]
        rw [h_pow_eq]
        ring
      · -- Reindex via Finset.sum_nbij.
        symm
        refine Finset.sum_nbij σ hσ_mem hσ_inj hσ_surj ?_
        intros i hi
        have hi_lt : i < k := Finset.mem_range.mp hi
        -- Goal: ζ^((i+k-1)%k) * h(ζ^i * t) = ζ^(σ i) * h(ζ^(σ i) * (ζ * t)).
        -- σ i = (i+k-1)%k, so the LHS power = ζ^(σ i) (definitionally).
        -- For the h-arguments: need h(ζ^i * t) = h(ζ^(σ i) * (ζ * t)),
        -- i.e., ζ^i * t = ζ^(σ i + 1) * t (after pow_succ), so ζ^i = ζ^(σ i + 1).
        have h_σi_succ_eq : ζ ^ (σ i + 1) = ζ ^ i := by
          simp only [σ]
          rcases Nat.eq_zero_or_pos i with hi0 | hi_pos
          · subst hi0
            rw [show (0 + k - 1) % k = k - 1 from by
                  rw [Nat.zero_add, Nat.mod_eq_of_lt (by omega : k - 1 < k)]]
            rw [show k - 1 + 1 = k from by omega, hζ.pow_eq_one, pow_zero]
          · rw [show (i + k - 1) % k = i - 1 from by
                  rw [show i + k - 1 = (i - 1) + k from by omega,
                      Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]]
            rw [show i - 1 + 1 = i from by omega]
        -- Note: σ i = (i+k-1)%k matches the LHS-exponent literally.
        -- So the goal is `ζ^(σ i) * h(ζ^i * t) = ζ^(σ i) * h(ζ^(σ i) * (ζ*t))`.
        congr 1
        rw [show ζ ^ σ i * (ζ * t) = ζ ^ (σ i + 1) * t from by
              rw [pow_succ]; ring]
        rw [h_σi_succ_eq]
    -- gtilde ζ-invariance via hH_equivariant + hH_eq_factored.
    have hgtilde_inv : ∀ᶠ t in 𝓝 (0 : ℂ), gtilde (ζ * t) = gtilde t := by
      -- We have hH_eq_factored : H =ᶠ[𝓝 0] fun t => t^(k-1) · gtilde t.
      -- Apply at t and at ζ·t: need ζ·t also in the eventuality nhd.
      -- Use that multiplication by ζ is continuous at 0 (sends 0 to 0).
      have h_mul_cont : Filter.Tendsto (fun t : ℂ => ζ * t) (𝓝 0) (𝓝 0) := by
        have : Filter.Tendsto (fun t : ℂ => ζ * t) (𝓝 0) (𝓝 (ζ * 0)) :=
          (continuous_const.mul continuous_id).tendsto 0
        simpa using this
      have hH_eq_at_ζt : ∀ᶠ t in 𝓝 (0 : ℂ),
          H (ζ * t) = (ζ * t) ^ (k - 1) * gtilde (ζ * t) :=
        h_mul_cont.eventually hH_eq_factored
      filter_upwards [hH_eq_factored, hH_eq_at_ζt] with t hHt hHζt
      -- We have:
      --   hHt : H t = t^(k-1) · gtilde t
      --   hHζt : H (ζ·t) = (ζ·t)^(k-1) · gtilde(ζ·t)
      --   hH_equivariant t : H(ζ·t) = ζ^(k-1) · H t = ζ^(k-1) · t^(k-1) · gtilde t.
      -- So (ζ·t)^(k-1) · gtilde(ζ·t) = ζ^(k-1) · t^(k-1) · gtilde t.
      -- (ζ·t)^(k-1) = ζ^(k-1) · t^(k-1). Cancel (when t ≠ 0).
      -- But we want eventually equality, INCLUDING t = 0 if it lands there.
      -- At t = 0: both sides of `gtilde(ζ·0) = gtilde(0)` reduce to `gtilde 0 = gtilde 0`. ✓
      -- For t ≠ 0: cancel t^(k-1) · ζ^(k-1) (both non-zero).
      by_cases ht0 : t = 0
      · subst ht0; simp
      · -- t ≠ 0. Then t^(k-1) ≠ 0 and ζ^(k-1) ≠ 0.
        have h1 : (ζ * t) ^ (k - 1) * gtilde (ζ * t) = ζ ^ (k - 1) * t ^ (k - 1) * gtilde t := by
          rw [← hHζt, hH_equivariant t, hHt]
          ring
        have h_zt : (ζ * t) ^ (k - 1) = ζ ^ (k - 1) * t ^ (k - 1) := by ring
        rw [h_zt] at h1
        have hζkm1_ne : ζ ^ (k - 1) ≠ 0 := pow_ne_zero _ (hζ.ne_zero hk_pos.ne')
        have htkm1_ne : t ^ (k - 1) ≠ 0 := pow_ne_zero _ ht0
        have hmul_ne : ζ ^ (k - 1) * t ^ (k - 1) ≠ 0 := mul_ne_zero hζkm1_ne htkm1_ne
        exact mul_left_cancel₀ hmul_ne h1
    -- Apply R-final to gtilde.
    obtain ⟨g, hg_an, hgtilde_extension⟩ :=
      exists_analytic_extension_of_rotation_invariant hgtilde_an hk_pos.ne' hζ
        (by
          -- Need: gtilde =ᶠ[𝓝 0] fun z => gtilde (ζ * z). Equivalent to hgtilde_inv (swap symm).
          filter_upwards [hgtilde_inv] with t ht
          exact ht.symm)
    refine ⟨g, hg_an, ?_⟩
    -- ∀ᶠ t, H(t) = t^(k-1) · g(t^k).
    filter_upwards [hH_eq_factored, hgtilde_extension] with t hHt hgt
    -- hHt : H t = t^(k-1) · gtilde t   (from hH_eq_factored, where H is unfolded).
    -- hgt : gtilde t = g (t^k).
    -- Goal: ∑_j ζ^j * h(ζ^j * t) = t^(k-1) * g (t^k).
    -- This equals H t = t^(k-1) * gtilde t = t^(k-1) * g(t^k).
    show H t = t ^ (k - 1) * g (t ^ k)
    rw [hHt, hgt]

omit [T2Space X] [CompactSpace X] [ConnectedSpace X] [StableChartAt ℂ X]
  [T2Space Y] [CompactSpace Y] [ConnectedSpace Y] [StableChartAt ℂ Y] in
/--
**DB-A — Chart-local Finset bijection `Fin k ↪ s_y` (eventually-y form).**

For a ramified branch point `x₀` of index `k`, the C4-pre chart-local
primitives (`φ`, local inverse `r`, principal `k`-th root `kthRoot`,
primitive `k`-th root `ζ`) realize the unramified `k`-element preimage
Finset `s_y` of any nearby regular value `y` as the image of the
explicit map `j ↦ (chartAt x₀).symm (r (ζ^j · kthRoot w_y))` where
`w_y := chartAt (f x₀) y - chartAt (f x₀) (f x₀)`.

The bijection is delivered in *eventually-y* form: for `y` in some
neighbourhood of `y₀` with `y ≠ y₀`, an injection `e : Fin k → s` exists
with `(e j).val = (chartAt x₀).symm (r (ζ^j · kthRoot w_y))`. DB-B
extracts an open `V ⊆ V_kfold` from the eventually quantifier via
`mem_nhds_iff`.

Sorry-free; primitive extraction is folded in as §8-internal `have`s.
-/
private theorem ramified_kfold_chart_bijection
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (⊤ : WithTop ℕ∞) f)
    (hbc : BranchedCoverData X Y f) (hcompat : hbc.RamificationIndexCompatible)
    (y₀ : Y) (x₀ : X) (hx₀_fiber : f x₀ = y₀)
    (k : ℕ) (hk_pos : 0 < k) (hk_ram : k = hbc.ramificationIndex x₀)
    (U_kfold : Set X) (hU_kfold_open : IsOpen U_kfold) (hxU_kfold : x₀ ∈ U_kfold) :
    ∃ (φ r kthRoot : ℂ → ℂ) (ζ : ℂ),
      AnalyticAt ℂ φ (chartAt ℂ x₀ x₀) ∧
      φ (chartAt ℂ x₀ x₀) = 0 ∧
      deriv φ (chartAt ℂ x₀ x₀) ≠ 0 ∧
      (∀ᶠ z in 𝓝 (chartAt ℂ x₀ x₀),
        chartLocalAt f x₀ z - chartAt ℂ (f x₀) (f x₀) = φ z ^ k) ∧
      (∀ᶠ ε in 𝓝 (0 : ℂ), φ (r ε) = ε) ∧
      (∀ᶠ z in 𝓝 (chartAt ℂ x₀ x₀), r (φ z) = z) ∧
      r 0 = chartAt ℂ x₀ x₀ ∧
      (∀ w : ℂ, (kthRoot w) ^ k = w) ∧
      kthRoot 0 = 0 ∧
      IsPrimitiveRoot ζ k ∧
      ∀ᶠ y in 𝓝 y₀, y ≠ y₀ → ∀ (s : Finset X),
        s.card = k → (↑s : Set X) ⊆ U_kfold →
        (∀ x' ∈ s, f x' = y ∧ hbc.ramificationIndex x' = 1) →
        (∀ x' ∈ U_kfold, f x' = y → x' ∈ s) →
        ∃ e : Fin k → s,
          Function.Injective e ∧
          ∀ j : Fin k, (e j : X) =
            (chartAt ℂ x₀).symm
              (r ((ζ ^ (j : ℕ)) *
                (kthRoot (chartAt ℂ (f x₀) y - chartAt ℂ (f x₀) (f x₀))))) := by
  classical
  have hHol : IsHolomorphic f :=
    isHolomorphic_of_contMDiff hf (hasLocalKfoldRamification_of_contMDiff hf)
  have hk_ram' : mapAnalyticOrderAt f x₀ = k := by
    rw [hk_ram]
    exact (hbc.ramificationIndex_eq_mapAnalyticOrderAt hcompat
      (hHol.holomorphicAt x₀)).symm
  obtain ⟨φ, hφ_an, hφ_z₀, hφ_deriv, hφ_eq⟩ :=
    chartLocal_zPow_form_of_ramified (hHol.holomorphicAt x₀) hk_pos hk_ram'
  have hSD : HasStrictDerivAt φ (deriv φ (chartAt ℂ x₀ x₀)) (chartAt ℂ x₀ x₀) :=
    hφ_an.hasStrictDerivAt
  set z₀ : ℂ := chartAt ℂ x₀ x₀ with hz₀_def
  set c₀ : ℂ := chartAt ℂ (f x₀) (f x₀) with hc₀_def
  let r : ℂ → ℂ := hSD.localInverse φ (deriv φ z₀) z₀ hφ_deriv
  have h_right_inv : ∀ᶠ ε in 𝓝 (0 : ℂ), φ (r ε) = ε := by
    have hR : ∀ᶠ ε in 𝓝 (φ z₀), φ (r ε) = ε :=
      hSD.eventually_right_inverse hφ_deriv
    rwa [hφ_z₀] at hR
  have h_left_inv : ∀ᶠ z in 𝓝 z₀, r (φ z) = z :=
    hSD.eventually_left_inverse hφ_deriv
  have hr_at_0 : r 0 = z₀ := by
    have hL : r (φ z₀) = z₀ := h_left_inv.self_of_nhds
    rwa [hφ_z₀] at hL
  let kthRoot : ℂ → ℂ := fun w => w ^ ((k : ℂ)⁻¹)
  have h_kthRoot_pow : ∀ w : ℂ, (kthRoot w) ^ k = w :=
    fun w => Complex.cpow_nat_inv_pow w hk_pos.ne'
  have h_kthRoot_zero : kthRoot 0 = 0 := by
    show (0 : ℂ) ^ ((k : ℂ)⁻¹) = 0
    apply Complex.zero_cpow
    have : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hk_pos.ne'
    exact inv_ne_zero this
  set ζ : ℂ := Complex.exp (2 * Real.pi * Complex.I / k) with hζ_def
  have hζ_pr : IsPrimitiveRoot ζ k :=
    Complex.isPrimitiveRoot_exp k hk_pos.ne'
  refine ⟨φ, r, kthRoot, ζ, hφ_an, hφ_z₀, hφ_deriv, hφ_eq,
    h_right_inv, h_left_inv, hr_at_0, h_kthRoot_pow, h_kthRoot_zero,
    hζ_pr, ?_⟩
  set w_of : Y → ℂ := fun y => chartAt ℂ (f x₀) y - c₀ with hw_of_def
  have hw_of_at_y₀ : w_of y₀ = 0 := by
    show chartAt ℂ (f x₀) y₀ - c₀ = 0
    rw [show y₀ = f x₀ from hx₀_fiber.symm, hc₀_def]; ring
  have h_chart_y₀_cont : ContinuousAt (chartAt ℂ (f x₀)) y₀ := by
    have h_chart_src : (chartAt ℂ (f x₀)).source ∈ 𝓝 y₀ := by
      apply (chartAt ℂ (f x₀)).open_source.mem_nhds
      rw [show y₀ = f x₀ from hx₀_fiber.symm]
      exact mem_chart_source ℂ (f x₀)
    exact (chartAt ℂ (f x₀)).continuousOn.continuousAt h_chart_src
  have hw_of_cont : ContinuousAt w_of y₀ := h_chart_y₀_cont.sub continuousAt_const
  have h_kthRoot_cont : ContinuousAt kthRoot 0 := by
    show ContinuousAt (fun w => w ^ ((k : ℂ)⁻¹)) 0
    have h_re_pos : 0 < ((k : ℂ)⁻¹).re := by
      have hk_re : ((k : ℂ)⁻¹).re = ((k : ℝ)⁻¹) := by
        simp [Complex.inv_re, Complex.natCast_re]
      rw [hk_re]
      exact inv_pos.mpr (Nat.cast_pos.mpr hk_pos)
    exact Complex.continuousAt_cpow_const_of_re_pos (Or.inl (le_refl _)) h_re_pos
  have h_r_cont_at_0 : ContinuousAt r 0 := by
    have h_r_strict_at_φz₀ : HasStrictDerivAt r ((deriv φ z₀)⁻¹) (φ z₀) :=
      hSD.to_localInverse hφ_deriv
    have h_r_cont_at_φz₀ : ContinuousAt r (φ z₀) := h_r_strict_at_φz₀.continuousAt
    rw [hφ_z₀] at h_r_cont_at_φz₀
    exact h_r_cont_at_φz₀
  have h_chart_symm_cont_at_z₀ : ContinuousAt (chartAt ℂ x₀).symm z₀ := by
    apply (chartAt ℂ x₀).continuousAt_symm
    show z₀ ∈ (chartAt ℂ x₀).target
    rw [hz₀_def]
    exact (chartAt ℂ x₀).map_source (mem_chart_source ℂ x₀)
  set candY : Fin k → Y → X := fun j y =>
    (chartAt ℂ x₀).symm (r ((ζ ^ (j : ℕ)) * kthRoot (w_of y))) with hcandY_def
  have h_candY_at_y₀ : ∀ j : Fin k, candY j y₀ = x₀ := by
    intro j
    show (chartAt ℂ x₀).symm (r ((ζ ^ (j : ℕ)) * kthRoot (w_of y₀))) = x₀
    rw [hw_of_at_y₀, h_kthRoot_zero, mul_zero, hr_at_0]
    exact (chartAt ℂ x₀).left_inv (mem_chart_source ℂ x₀)
  have h_ε_at_y₀ : ∀ j : Fin k, (ζ ^ (j : ℕ)) * kthRoot (w_of y₀) = 0 := by
    intro j; rw [hw_of_at_y₀, h_kthRoot_zero, mul_zero]
  have h_ε_cont : ∀ j : Fin k,
      ContinuousAt (fun y => (ζ ^ (j : ℕ)) * kthRoot (w_of y)) y₀ := by
    intro j
    have h1 : ContinuousAt kthRoot (w_of y₀) := by
      rw [hw_of_at_y₀]; exact h_kthRoot_cont
    exact continuousAt_const.mul (h1.comp hw_of_cont)
  have h_rε_at_y₀ : ∀ j : Fin k, r ((ζ ^ (j : ℕ)) * kthRoot (w_of y₀)) = z₀ := by
    intro j; rw [h_ε_at_y₀ j]; exact hr_at_0
  -- Express r ∘ ε continuity into 𝓝 z₀ directly via a Tendsto statement,
  -- so subsequent .eventually applications match nhds-target nhds.
  have h_rε_tendsto : ∀ j : Fin k,
      Filter.Tendsto (fun y => r ((ζ ^ (j : ℕ)) * kthRoot (w_of y))) (𝓝 y₀) (𝓝 z₀) := by
    intro j
    -- Build via Tendsto.comp explicitly.
    have h_ε_tend_to_0 : Filter.Tendsto (fun y => (ζ ^ (j : ℕ)) * kthRoot (w_of y))
        (𝓝 y₀) (𝓝 0) := by
      have h_val : (fun y => (ζ ^ (j : ℕ)) * kthRoot (w_of y)) y₀ = 0 := h_ε_at_y₀ j
      have h_tend : Filter.Tendsto (fun y => (ζ ^ (j : ℕ)) * kthRoot (w_of y))
          (𝓝 y₀) (𝓝 ((fun y => (ζ ^ (j : ℕ)) * kthRoot (w_of y)) y₀)) :=
        (h_ε_cont j).tendsto
      rwa [h_val] at h_tend
    have h_r_tend : Filter.Tendsto r (𝓝 0) (𝓝 z₀) := by
      have h_val : r 0 = z₀ := hr_at_0
      have h_tend : Filter.Tendsto r (𝓝 0) (𝓝 (r 0)) := h_r_cont_at_0.tendsto
      rwa [h_val] at h_tend
    exact h_r_tend.comp h_ε_tend_to_0
  -- Similarly for the ε itself: Tendsto into 𝓝 0.
  have h_ε_tendsto : ∀ j : Fin k,
      Filter.Tendsto (fun y => (ζ ^ (j : ℕ)) * kthRoot (w_of y)) (𝓝 y₀) (𝓝 0) := by
    intro j
    have h_eq : (fun y => (ζ ^ (j : ℕ)) * kthRoot (w_of y)) y₀ = 0 := h_ε_at_y₀ j
    have : Filter.Tendsto (fun y => (ζ ^ (j : ℕ)) * kthRoot (w_of y)) (𝓝 y₀)
        (𝓝 ((fun y => (ζ ^ (j : ℕ)) * kthRoot (w_of y)) y₀)) := (h_ε_cont j).tendsto
    rwa [h_eq] at this
  have h_candY_tendsto : ∀ j : Fin k,
      Filter.Tendsto (candY j) (𝓝 y₀) (𝓝 x₀) := by
    intro j
    have h_symm_tendsto : Filter.Tendsto (chartAt ℂ x₀).symm (𝓝 z₀) (𝓝 x₀) := by
      have h_chart_symm_at_z₀_val : (chartAt ℂ x₀).symm z₀ = x₀ := by
        rw [hz₀_def]; exact (chartAt ℂ x₀).left_inv (mem_chart_source ℂ x₀)
      have : Filter.Tendsto (chartAt ℂ x₀).symm (𝓝 z₀) (𝓝 ((chartAt ℂ x₀).symm z₀)) :=
        h_chart_symm_cont_at_z₀.tendsto
      rwa [h_chart_symm_at_z₀_val] at this
    exact h_symm_tendsto.comp (h_rε_tendsto j)
  have h_chart_x₀_src_nhd : (chartAt ℂ x₀).source ∈ 𝓝 x₀ :=
    (chartAt ℂ x₀).open_source.mem_nhds (mem_chart_source ℂ x₀)
  have h_U_kfold_nhd : U_kfold ∈ 𝓝 x₀ := hU_kfold_open.mem_nhds hxU_kfold
  have h_chart_x₀_tgt_nhd : (chartAt ℂ x₀).target ∈ 𝓝 z₀ :=
    (chartAt ℂ x₀).open_target.mem_nhds
      (by rw [hz₀_def]; exact (chartAt ℂ x₀).map_source (mem_chart_source ℂ x₀))
  have h_chart_y₀_src_nhd : (chartAt ℂ (f x₀)).source ∈ 𝓝 (f x₀) :=
    (chartAt ℂ (f x₀)).open_source.mem_nhds (mem_chart_source ℂ (f x₀))
  have h_f_cont_at_x₀ : ContinuousAt f x₀ := hf.continuous.continuousAt
  have h_per_j_evt : ∀ j : Fin k, ∀ᶠ y in 𝓝 y₀,
      candY j y ∈ (chartAt ℂ x₀).source ∧
      candY j y ∈ U_kfold ∧
      r ((ζ ^ (j : ℕ)) * kthRoot (w_of y)) ∈ (chartAt ℂ x₀).target ∧
      φ (r ((ζ ^ (j : ℕ)) * kthRoot (w_of y))) =
        (ζ ^ (j : ℕ)) * kthRoot (w_of y) ∧
      (∀ᶠ z in 𝓝 (r ((ζ ^ (j : ℕ)) * kthRoot (w_of y))),
        chartLocalAt f x₀ z - c₀ = φ z ^ k) ∧
      f (candY j y) ∈ (chartAt ℂ (f x₀)).source := by
    intro j
    have h_cand_tend := h_candY_tendsto j
    have h_src : ∀ᶠ y in 𝓝 y₀, candY j y ∈ (chartAt ℂ x₀).source :=
      h_cand_tend.eventually h_chart_x₀_src_nhd
    have h_U : ∀ᶠ y in 𝓝 y₀, candY j y ∈ U_kfold :=
      h_cand_tend.eventually h_U_kfold_nhd
    have h_rε_tgt : ∀ᶠ y in 𝓝 y₀,
        r ((ζ ^ (j : ℕ)) * kthRoot (w_of y)) ∈ (chartAt ℂ x₀).target :=
      (h_rε_tendsto j).eventually h_chart_x₀_tgt_nhd
    have h_φr : ∀ᶠ y in 𝓝 y₀,
        φ (r ((ζ ^ (j : ℕ)) * kthRoot (w_of y))) =
          (ζ ^ (j : ℕ)) * kthRoot (w_of y) :=
      (h_ε_tendsto j).eventually h_right_inv
    have h_pow_form_evt : ∀ᶠ y in 𝓝 y₀,
        ∀ᶠ z in 𝓝 (r ((ζ ^ (j : ℕ)) * kthRoot (w_of y))),
          chartLocalAt f x₀ z - c₀ = φ z ^ k := by
      have h_eventually_nhd : ∀ᶠ z in 𝓝 z₀,
          ∀ᶠ z' in 𝓝 z, chartLocalAt f x₀ z' - c₀ = φ z' ^ k :=
        eventually_eventually_nhds.mpr hφ_eq
      exact (h_rε_tendsto j).eventually h_eventually_nhd
    have h_f_cand_src : ∀ᶠ y in 𝓝 y₀, f (candY j y) ∈ (chartAt ℂ (f x₀)).source := by
      have h_f_tendsto : Filter.Tendsto (fun y => f (candY j y)) (𝓝 y₀) (𝓝 (f x₀)) := by
        have h_f_at : ContinuousAt f x₀ := h_f_cont_at_x₀
        exact h_f_at.tendsto.comp h_cand_tend
      exact h_f_tendsto.eventually h_chart_y₀_src_nhd
    filter_upwards [h_src, h_U, h_rε_tgt, h_φr, h_pow_form_evt, h_f_cand_src]
      with y h1 h2 h3 h4 h5 h6
    exact ⟨h1, h2, h3, h4, h5, h6⟩
  have h_all_evt : ∀ᶠ y in 𝓝 y₀, ∀ j : Fin k,
      candY j y ∈ (chartAt ℂ x₀).source ∧
      candY j y ∈ U_kfold ∧
      r ((ζ ^ (j : ℕ)) * kthRoot (w_of y)) ∈ (chartAt ℂ x₀).target ∧
      φ (r ((ζ ^ (j : ℕ)) * kthRoot (w_of y))) =
        (ζ ^ (j : ℕ)) * kthRoot (w_of y) ∧
      (∀ᶠ z in 𝓝 (r ((ζ ^ (j : ℕ)) * kthRoot (w_of y))),
        chartLocalAt f x₀ z - c₀ = φ z ^ k) ∧
      f (candY j y) ∈ (chartAt ℂ (f x₀)).source := by
    rw [Filter.eventually_all]
    exact h_per_j_evt
  have h_y_src_evt : ∀ᶠ y in 𝓝 y₀, y ∈ (chartAt ℂ (f x₀)).source := by
    have h_src_nhd : (chartAt ℂ (f x₀)).source ∈ 𝓝 y₀ := by
      apply (chartAt ℂ (f x₀)).open_source.mem_nhds
      rw [show y₀ = f x₀ from hx₀_fiber.symm]
      exact mem_chart_source ℂ (f x₀)
    exact Filter.eventually_mem_set.mpr h_src_nhd
  filter_upwards [h_all_evt, h_y_src_evt] with y h_jall h_y_src
  intro hy_ne s _hs_card _hs_sub _hs_unram hs_exhaust
  set w_y : ℂ := w_of y with hw_y_def
  set candX : Fin k → X := fun j =>
    (chartAt ℂ x₀).symm (r ((ζ ^ (j : ℕ)) * kthRoot w_y)) with hcandX_def
  have h_f_candX_eq : ∀ j : Fin k, f (candX j) = y := by
    intro j
    obtain ⟨_h_src, _h_U, _h_rε_tgt, h_φr, h_pow_form_evt, h_f_src⟩ := h_jall j
    have h_pow_at_rε : chartLocalAt f x₀ (r ((ζ ^ (j : ℕ)) * kthRoot w_y)) - c₀ =
        (φ (r ((ζ ^ (j : ℕ)) * kthRoot w_y))) ^ k :=
      h_pow_form_evt.self_of_nhds
    have h_chartLocal_val :
        chartLocalAt f x₀ (r ((ζ ^ (j : ℕ)) * kthRoot w_y)) - c₀ = w_y := by
      rw [h_pow_at_rε, h_φr, mul_pow, h_kthRoot_pow]
      rw [show (ζ ^ (j : ℕ)) ^ k = (ζ ^ k) ^ (j : ℕ) from by
            rw [← pow_mul, ← pow_mul, Nat.mul_comm]]
      rw [hζ_pr.pow_eq_one, one_pow, one_mul]
    have h_chartY_val :
        chartAt ℂ (f x₀) (f (candX j)) = c₀ + w_y := by
      have hdef : chartLocalAt f x₀ (r ((ζ ^ (j : ℕ)) * kthRoot w_y)) =
          chartAt ℂ (f x₀) (f (candX j)) := rfl
      have := hdef ▸ h_chartLocal_val
      linear_combination this
    have h_y_chart_eq : chartAt ℂ (f x₀) y = c₀ + w_y := by
      show chartAt ℂ (f x₀) y = c₀ + (chartAt ℂ (f x₀) y - c₀); ring
    have hchart_eq : chartAt ℂ (f x₀) (f (candX j)) = chartAt ℂ (f x₀) y := by
      rw [h_chartY_val, h_y_chart_eq]
    have h_candX_eq : candX j = candY j y := rfl
    have h_f_candX_src : f (candX j) ∈ (chartAt ℂ (f x₀)).source := by
      rw [h_candX_eq]; exact h_f_src
    exact (chartAt ℂ (f x₀)).injOn h_f_candX_src h_y_src hchart_eq
  have h_candX_U : ∀ j : Fin k, candX j ∈ U_kfold := by
    intro j
    have h_candX_eq : candX j = candY j y := rfl
    rw [h_candX_eq]; exact (h_jall j).2.1
  have h_candX_in_s : ∀ j : Fin k, candX j ∈ s := fun j =>
    hs_exhaust (candX j) (h_candX_U j) (h_f_candX_eq j)
  have h_candX_inj : Function.Injective candX := by
    intro j₁ j₂ h_eq
    have hr_tgt_1 := (h_jall j₁).2.2.1
    have hr_tgt_2 := (h_jall j₂).2.2.1
    have h_chart_eq :
        chartAt ℂ x₀ (candX j₁) = chartAt ℂ x₀ (candX j₂) := by rw [h_eq]
    have h_chart_symm_1 : chartAt ℂ x₀ (candX j₁) =
        r ((ζ ^ (j₁ : ℕ)) * kthRoot w_y) :=
      (chartAt ℂ x₀).right_inv hr_tgt_1
    have h_chart_symm_2 : chartAt ℂ x₀ (candX j₂) =
        r ((ζ ^ (j₂ : ℕ)) * kthRoot w_y) :=
      (chartAt ℂ x₀).right_inv hr_tgt_2
    have h_r_eq : r ((ζ ^ (j₁ : ℕ)) * kthRoot w_y) = r ((ζ ^ (j₂ : ℕ)) * kthRoot w_y) := by
      rw [← h_chart_symm_1, ← h_chart_symm_2]; exact h_chart_eq
    have h_φr_1 := (h_jall j₁).2.2.2.1
    have h_φr_2 := (h_jall j₂).2.2.2.1
    have h_ε_eq : (ζ ^ (j₁ : ℕ)) * kthRoot w_y = (ζ ^ (j₂ : ℕ)) * kthRoot w_y := by
      have := congrArg φ h_r_eq
      rw [h_φr_1, h_φr_2] at this; exact this
    have hw_y_ne : w_y ≠ 0 := by
      intro hzero
      apply hy_ne
      have heq : chartAt ℂ (f x₀) y = c₀ := by
        have h0 : chartAt ℂ (f x₀) y - c₀ = 0 := hzero
        linear_combination h0
      have h_fx₀_src : f x₀ ∈ (chartAt ℂ (f x₀)).source := mem_chart_source ℂ (f x₀)
      rw [show y₀ = f x₀ from hx₀_fiber.symm]
      exact (chartAt ℂ (f x₀)).injOn h_y_src h_fx₀_src heq
    have h_kthRoot_ne : kthRoot w_y ≠ 0 := by
      intro hzero
      apply hw_y_ne
      have h := h_kthRoot_pow w_y
      rw [hzero, zero_pow hk_pos.ne'] at h
      exact h.symm
    have h_ζ_eq : ζ ^ (j₁ : ℕ) = ζ ^ (j₂ : ℕ) :=
      mul_right_cancel₀ h_kthRoot_ne h_ε_eq
    have h_nat_eq : (j₁ : ℕ) = (j₂ : ℕ) := by
      have h1_lt : (j₁ : ℕ) < k := j₁.isLt
      have h2_lt : (j₂ : ℕ) < k := j₂.isLt
      exact hζ_pr.pow_inj h1_lt h2_lt h_ζ_eq
    exact Fin.ext h_nat_eq
  refine ⟨fun j => ⟨candX j, h_candX_in_s j⟩, ?_, ?_⟩
  · intro j₁ j₂ h_eq
    have h_val_eq : candX j₁ = candX j₂ := Subtype.mk_eq_mk.mp h_eq
    exact h_candX_inj h_val_eq
  · intro j; rfl

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
    (_hx₀_ram : hbc.ramificationIndex x₀ ≠ 1)
    (W₀ : Set X) (hW₀_open : IsOpen W₀) (hxW₀ : x₀ ∈ W₀) :
    ∃ (V : Set Y) (W : Set X) (M : ℝ),
      IsOpen V ∧ y₀ ∈ V ∧ IsOpen W ∧ x₀ ∈ W ∧ W ⊆ W₀ ∧
      ∀ y ∈ V, y ≠ y₀ → ∀ (_hy : isRegularValue hbc y),
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
      ∀ y ∈ V, ∀ (_hy : isRegularValue hbc y),
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
      ∀ y ∈ V, ∀ (_hy : isRegularValue hbc y),
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
  [StableChartAt ℂ X] [CompactSpace Y] [ConnectedSpace Y]
  [IsManifold 𝓘(ℂ, ℂ) ω Y] in
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
    (regular : Set Y) (_hOpen : IsOpen regular)
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
  [StableChartAt ℂ X] [CompactSpace Y] [ConnectedSpace Y]
  [IsManifold 𝓘(ℂ, ℂ) ω Y] [StableChartAt ℂ Y] in
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
    (regular : Set Y) (hOpen : IsOpen regular) (_hDense : Dense regular)
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
  [StableChartAt ℂ X] [T2Space Y] [CompactSpace Y] [ConnectedSpace Y]
  [StableChartAt ℂ Y] in
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
  [StableChartAt ℂ X] [T2Space Y] [CompactSpace Y] [ConnectedSpace Y]
  [StableChartAt ℂ Y] in
/--
**Model-shift bridge (sorry-free helper).**

Converts manifold-`ContMDiff` of `f : Y → CotangentModelFiber ℂ` in
the singleton-chart model on `CotangentModelFiber ℂ` (codomain model
`𝓘(ℂ, ℂ)`, with the chart `cotangentFiberIso`) into normed-space
`ContMDiff` (codomain model `𝓘(ℂ, ℂ →L[ℂ] ℂ)`, treating
`CotangentModelFiber ℂ = ℂ →L[ℂ] ℂ` as a normed `ℂ`-space directly).

The proof factors as `f = cotangentFiberIso.symm ∘ (cotangentFiberIso ∘ f)`:
* `cotangentFiberIso ∘ f : Y → ℂ` is `ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ⊤`
  by the singleton-chart unfolding of the hypothesis.
* `cotangentFiberIso.symm : ℂ →L[ℂ] (ℂ →L[ℂ] ℂ)` is a CLM, hence
  `ContMDiff` as a map between normed spaces.
-/
private theorem contMDiff_normedClm_of_contMDiff_singletonChart
    {f : Y → CotangentModelFiber ℂ}
    (hf : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (⊤ : WithTop ℕ∞) f) :
    ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, CotangentModelFiber ℂ) (⊤ : WithTop ℕ∞) f := by
  -- The chart on CotangentModelFiber ℂ is the singleton chart from
  -- `cotangentFiberIso.toHomeomorph.toOpenPartialHomeomorph`. The
  -- chart-local form of `f` codomain-side is `cotangentFiberIso ∘ f`
  -- post-composed with `chartAt ℂ (f y).symm = chartAt ℂ y₀.symm` for the
  -- domain. We reduce both `ContMDiff` claims to pointwise `ContDiff`
  -- statements at the chart-target via `contMDiffAt_iff_of_mem_source`.
  intro y₀
  have hfy₀ : ContMDiffAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (⊤ : WithTop ℕ∞) f y₀ := hf y₀
  rw [contMDiffAt_iff_of_mem_source (I := 𝓘(ℂ, ℂ)) (I' := 𝓘(ℂ, ℂ))
      (x := y₀) (y := f y₀) (mem_chart_source ℂ y₀)
      (mem_chart_source ℂ (f y₀))] at hfy₀
  rw [contMDiffAt_iff_of_mem_source (I := 𝓘(ℂ, ℂ))
      (I' := (𝓘(ℂ, CotangentModelFiber ℂ)))
      (x := y₀) (y := f y₀) (mem_chart_source ℂ y₀)
      (mem_chart_source (CotangentModelFiber ℂ) (f y₀))]
  obtain ⟨hcont, hCD⟩ := hfy₀
  refine ⟨hcont, ?_⟩
  -- The chart-local form is `chartAt ℂ (f y₀) ∘ f ∘ (chartAt ℂ y₀).symm`,
  -- which equals `cotangentFiberIso ∘ f ∘ (chartAt ℂ y₀).symm` in both
  -- cases (singleton chart on CotangentModelFiber ℂ vs the normed-space
  -- chart-target). We use `cotangentFiberIso.symm` as a CLM (smooth between
  -- normed spaces) to bridge.
  -- Convert `hCD : ContDiffWithinAt ℂ ⊤ (chartAt ℂ (f y₀) ∘ f ∘
  --   (chartAt ℂ y₀).symm) ... (chartAt ℂ y₀ y₀)` to the corresponding
  -- statement with chart-target replaced; the chart-target for
  -- `CotangentModelFiber ℂ` is `cotangentFiberIso`, but the chart-target
  -- for the normed `ℂ →L[ℂ] ℂ` self-chart is `id`.
  -- Apply cotangentFiberIso.symm post-composition to the local form.
  have hCD' : ContDiffWithinAt ℂ (⊤ : WithTop ℕ∞)
      ((cotangentFiberIso.symm : ℂ →L[ℂ] (ℂ →L[ℂ] ℂ)) ∘
        (chartAt ℂ (f y₀) ∘ f ∘ (chartAt ℂ y₀).symm))
      _ (chartAt ℂ y₀ y₀) :=
    (cotangentFiberIso.symm :
      ℂ →L[ℂ] (ℂ →L[ℂ] ℂ)).contDiff.contDiffAt.contDiffWithinAt.comp _ hCD
      (Set.mapsTo_univ _ _)
  -- Now (cotangentFiberIso.symm ∘ chartAt ℂ (f y₀)) = chartAt _ (f y₀)
  -- in the normed-space chart on CotangentModelFiber ℂ.
  -- Both `chartAt ℂ (f y₀)` (singleton) and `chartAt _ (f y₀)` (normed self)
  -- are the same chart-target function-application; the singleton chart on
  -- `CotangentModelFiber ℂ` is `cotangentFiberIso` (a map to ℂ), and the
  -- normed self-chart on `CotangentModelFiber ℂ = ℂ →L[ℂ] ℂ` is the
  -- identity. Composition with `cotangentFiberIso.symm` recovers `f`.
  convert hCD' using 1
  funext z
  show (chartAt (CotangentModelFiber ℂ) (f y₀) ∘ f ∘ (chartAt ℂ y₀).symm) z =
    ((cotangentFiberIso.symm : ℂ →L[ℂ] (ℂ →L[ℂ] ℂ)) ∘
      (chartAt ℂ (f y₀) ∘ f ∘ (chartAt ℂ y₀).symm)) z
  show f ((chartAt ℂ y₀).symm z) =
    cotangentFiberIso.symm (cotangentFiberIso (f ((chartAt ℂ y₀).symm z)))
  rw [cotangentFiberIso.symm_apply_apply]

omit [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]
  [StableChartAt ℂ X] [T2Space Y] [CompactSpace Y] [ConnectedSpace Y] in
/--
**Bundle-section `ContMDiff` from pointwise holomorphicity (strictly
narrower sub-helper).**

Given a function `g_ext : Y → CotangentModelFiber ℂ` that is
`IsHolomorphicAt` at every point of `Y`, the corresponding section
of the cotangent bundle is `ContMDiff` of class `⊤`.

The proof inlines the following structural assembly:
1. `contMDiff_iff_contMDiffAt` reduces to pointwise.
2. `Trivialization.contMDiffAt_section_iff` reduces bundle-section
   `ContMDiff` to `ContMDiff` of the trivialized section
   `(e ⟨y, g_ext y⟩).2`.
3. The cotangent-trivialization formula (inlined, mirroring
   `cotangent_triv_inversion_snd` in
   `InversionChartContinuity.lean:192`) rewrites
   `(e ⟨y, g⟩).snd = g.comp (tT.symmL ℂ y)`.
4. The CLM composition is `ContMDiffAt` by `ContMDiffAt.clm_comp`,
   using:
   - `contMDiff_normedClm_of_contMDiff_singletonChart` to upgrade the
     manifold-`ContMDiff` of `g_ext` (singleton-chart) to normed-space
     `ContMDiff` (CLM-valued).
   - Smoothness of `y ↦ tT.symmL ℂ y` proved inline via the tangent
     trivialization on a stable-chart manifold.
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
  -- Reduce to pointwise (ContMDiff = ∀ x, ContMDiffAt by definition).
  intro y₀
  -- Trivialization at y₀; y₀ is in its baseSet.
  set e := trivializationAt (CotangentModelFiber ℂ) (CotangentSpace ℂ Y) y₀ with he_def
  have hy₀_base : y₀ ∈ e.baseSet :=
    FiberBundle.mem_baseSet_trivializationAt' y₀
  -- Reduce to ContMDiffAt of the trivialized section (e ⟨y, g_ext y⟩).2.
  rw [e.contMDiffAt_section_iff hy₀_base]
  -- The cotangent bundle trivialization decomposes via the tangent
  -- bundle and the trivial line bundle.
  set tT := trivializationAt ℂ (TangentSpace (modelWithCornersSelf ℂ ℂ)) y₀ with htT_def
  -- Cotangent-trivialization formula (inlined, mirroring
  -- cotangent_triv_inversion_snd):
  --   (e ⟨y, g⟩).snd = g.comp (tT.symmL ℂ y).
  have h_triv_eq :
      ∀ y : Y,
        (e ⟨y, (g_ext y : CotangentSpace ℂ Y y)⟩).snd =
          (g_ext y).comp (tT.symmL ℂ y) := by
    intro y
    show (e ⟨y, (g_ext y : CotangentSpace ℂ Y y)⟩).snd =
        (g_ext y).comp (tT.symmL ℂ y)
    rw [show e = tT.continuousLinearMap (RingHom.id ℂ)
        (trivializationAt ℂ (Bundle.Trivial Y ℂ) y₀) from rfl,
      Trivialization.continuousLinearMap_apply]
    have hTrivial :
        (trivializationAt ℂ (Bundle.Trivial Y ℂ) y₀).continuousLinearMapAt ℂ y =
          ContinuousLinearMap.id ℂ ℂ := by
      have h₀ : (Bundle.Trivial.trivialization Y ℂ).continuousLinearMapAt ℂ y
          = ContinuousLinearMap.id ℂ ℂ :=
        Bundle.Trivial.continuousLinearMapAt_trivialization ℂ Y ℂ y
      have hbridge :
          (trivializationAt ℂ (Bundle.Trivial Y ℂ) y₀).continuousLinearMapAt ℂ y =
            (Bundle.Trivial.trivialization Y ℂ).continuousLinearMapAt ℂ y := by
        congr 1
      exact hbridge.trans h₀
    rw [hTrivial]
    rfl
  -- Rewrite the goal via h_triv_eq using congr_of_eventuallyEq.
  apply ContMDiffAt.congr_of_eventuallyEq _ (Filter.Eventually.of_forall h_triv_eq)
  -- Now goal: ContMDiffAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ →L[ℂ] ℂ) ⊤
  --   (fun y => (g_ext y).comp (tT.symmL ℂ y)) y₀.
  -- Discharge via clm_comp.
  have hg_normed : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, CotangentModelFiber ℂ) (⊤ : WithTop ℕ∞) g_ext :=
    contMDiff_normedClm_of_contMDiff_singletonChart
      (contMDiff_of_pointwiseHolomorphic g_ext hg_ext_hol)
  -- Smoothness of the symmL factor.
  -- Key facts (inlined from Mathlib + project):
  -- * `symmL_trivializationAt_eq_core` (Mathlib): for `b ∈ chart.source`,
  --   `(trivializationAt … b₀).symmL ℂ b = tangentBundleCore.coordChange ...`.
  -- * Under `StableChartAt ℂ Y`, `achart ℂ b = achart ℂ b₀` on
  --   `chart.source` (project's `achart_eq_of_mem_source`).
  -- * `tangentBundleCore.coordChange_self` then makes the coordChange the
  --   identity, so `symmL` is locally constant equal to `(1 : ℂ →L[ℂ] ℂ)`.
  -- Therefore the function is `ContMDiffAt` via `congr_of_eventuallyEq`
  -- with the constant function (1 : ℂ →L[ℂ] ℂ).
  have h_symmL : ContMDiffAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ →L[ℂ] ℂ) (⊤ : WithTop ℕ∞)
      (fun y : Y => show ℂ →L[ℂ] ℂ from tT.symmL ℂ y) y₀ := by
    have h_const : ContMDiffAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ →L[ℂ] ℂ) (⊤ : WithTop ℕ∞)
        (fun _ : Y => (1 : ℂ →L[ℂ] ℂ)) y₀ := contMDiffAt_const
    refine h_const.congr_of_eventuallyEq ?_
    -- Show: ∀ᶠ y in 𝓝 y₀, tT.symmL ℂ y = (1 : ℂ →L[ℂ] ℂ).
    have h_src_nhds : (chartAt ℂ y₀).source ∈ 𝓝 y₀ :=
      (chartAt ℂ y₀).open_source.mem_nhds (mem_chart_source ℂ y₀)
    filter_upwards [h_src_nhds] with y hy
    show tT.symmL ℂ y = (1 : ℂ →L[ℂ] ℂ)
    -- Use symmL_trivializationAt_eq_core then coordChange_self via StableChartAt.
    rw [TangentBundle.symmL_trivializationAt_eq_core (b₀ := y₀) (b := y) hy]
    -- Now goal: tangentBundleCore ⟨ℂ, ℂ⟩ Y .coordChange (achart ℂ y₀) (achart ℂ y) y = 1.
    have hachart : achart ℂ y = achart ℂ y₀ :=
      JacobianChallenge.Periods.achart_eq_of_mem_source (H := ℂ) (M := Y) hy
    rw [hachart]
    -- Now: coordChange (achart ℂ y₀) (achart ℂ y₀) y = 1.
    have hy_base : y ∈ (tangentBundleCore 𝓘(ℂ, ℂ) Y).baseSet (achart ℂ y₀) := by
      rw [tangentBundleCore_baseSet, coe_achart]
      exact hy
    apply ContinuousLinearMap.ext
    intro v
    rw [(tangentBundleCore 𝓘(ℂ, ℂ) Y).coordChange_self (achart ℂ y₀) y hy_base v]
    simp
  -- Now apply clm_comp.
  have h_goal : ContMDiffAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ →L[ℂ] ℂ) (⊤ : WithTop ℕ∞)
      (fun y => (g_ext y).comp (show ℂ →L[ℂ] ℂ from tT.symmL ℂ y)) y₀ :=
    hg_normed.contMDiffAt.clm_comp h_symmL
  -- The goal modulo defeq is the same.
  exact h_goal

omit [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]
  [StableChartAt ℂ X] [T2Space Y] [CompactSpace Y] [ConnectedSpace Y] in
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
  [StableChartAt ℂ X] [CompactSpace Y] [ConnectedSpace Y] in
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
  [StableChartAt ℂ X] [CompactSpace Y] [ConnectedSpace Y] in
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

omit [StableChartAt ℂ X] [CompactSpace Y] [ConnectedSpace Y] [StableChartAt ℂ Y] in
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
