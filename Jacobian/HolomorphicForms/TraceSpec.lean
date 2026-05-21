import Jacobian.HolomorphicForms.Defs
import Jacobian.HolomorphicForms.ChartedSpaceComplexPoints
import Jacobian.HolomorphicForms.CompactRiemannSurface
import Jacobian.HolomorphicForms.SectionFiberNorm
import Jacobian.HolomorphicForms.HolomorphicMap
import Jacobian.HolomorphicForms.BranchedCover
import Jacobian.HolomorphicForms.ToFunApplyVec
import Jacobian.TraceDegree.TraceDefinition
import Jacobian.Periods.TrivializationContinuousLinearMapAt

/-!
# Trace form specification interface

This file contains the minimal trace object and regular-value
specification needed by both the analytic degree API and the bundled
trace API.  It deliberately does not import `TraceDegree.AnalyticDegree`,
so the degree layer can package trace laws without creating an import
cycle.
-/

namespace JacobianChallenge.HolomorphicForms

open scoped Manifold ContDiff Topology
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

/-- **Trace construction data.** Packages the global bundled trace form
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
construction provider `traceFormsConstructionData_provider`. -/
structure TraceFormsConstructionData
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (⊤ : WithTop ℕ∞) f)
    (η : HolomorphicOneForm ℂ X) where
  /-- The global bundled trace form of `η` along `f`. -/
  traceForm : HolomorphicOneForm ℂ Y
  /-- At every regular value of any compatible branched-cover datum on
  `f`, the global form agrees with the finite local fiber sum. -/
  regular_spec :
    ∀ (hbc : BranchedCoverData X Y f) (y : Y) (hy : isRegularValue hbc y),
      traceForm.toFun y = traceAtRegularValue hbc (fun x => η.toFun x) y hy
  /-- The zero input form maps to the zero global form. -/
  map_zero_spec : η = 0 → traceForm = 0

omit [T2Space X] [CompactSpace X] [ConnectedSpace X] [StableChartAt ℂ X]
  [IsManifold 𝓘(ℂ, ℂ) ω X]
  [T2Space Y] [CompactSpace Y] [ConnectedSpace Y]
  [IsManifold 𝓘(ℂ, ℂ) ω Y] [StableChartAt ℂ Y] in
/-- **Helper.** `cotangentPushforward` is zero on the zero cotangent
vector. Sorry-free unfolding of the definition. -/
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
/-- **Helper.** The trace sum at a regular value of the zero pointwise
input is zero. Sorry-free reduction to `cotangentPushforward_zero` on
every summand of the finite fiber sum. -/
private theorem traceAtRegularValue_zero
    {f : X → Y} (hbc : BranchedCoverData X Y f)
    (y : Y) (hy : isRegularValue hbc y) :
    traceAtRegularValue hbc (fun _ : X => (0 : CotangentModelFiber ℂ)) y hy = 0 := by
  classical
  unfold traceAtRegularValue
  refine Finset.sum_eq_zero ?_
  rintro ⟨x, _⟩ _
  exact cotangentPushforward_zero f x

/-- **Construction data for the zero input form.** Fully proved.

When `η = 0`, the trace is the zero form on `Y`, and both fields are
immediate:

* `regular_spec` reduces every summand of the finite fiber sum to
  `cotangentPushforward f x 0 = 0`;
* `map_zero_spec` is `rfl` since the global form is already zero.

This is the strictly smaller "zero-input" leaf split out of the original
construction provider. -/
private noncomputable def traceFormsConstructionData_zero
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (⊤ : WithTop ℕ∞) f) :
    TraceFormsConstructionData f hf (0 : HolomorphicOneForm ℂ X) where
  traceForm := 0
  regular_spec := by
    intro hbc y hy
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

/-- **Construction data for a constant map.** Fully proved.

For a constant map `f x = y₀`, the trace is the zero form. The
`regular_spec` field is discharged by case-splitting on whether the
target value `y` equals `y₀`:

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
original construction provider. -/
private noncomputable def traceFormsConstructionData_constant
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (⊤ : WithTop ℕ∞) f)
    (η : HolomorphicOneForm ℂ X) (hconst : ∃ y₀, ∀ x, f x = y₀)
    (hη : η ≠ 0) :
    TraceFormsConstructionData f hf η where
  traceForm := 0
  regular_spec := by
    classical
    intro hbc y hy
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

/-- **Narrow leaf: trace construction for a nonconstant nonzero
input.** This is the sole remaining analytic frontier beneath the
bundled trace API. The cases `η = 0` and "`f` constant" are fully
handled by `traceFormsConstructionData_zero` and
`traceFormsConstructionData_constant`; this leaf carries exactly the
nonconstant-map-with-nonzero-input portion, which is the genuine
content of "extend the finite local fiber sum of a nonzero
holomorphic 1-form holomorphically across the finite branch locus of a
nonconstant holomorphic map".

Strictly narrower than the previous `traceFormsConstructionData_provider`
sorry: it is only required to produce the construction data for the
case where `f` is nonconstant **and** `η ≠ 0`. -/
noncomputable def traceFormsConstructionData_nonconstant_nonzero_provider
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (⊤ : WithTop ℕ∞) f)
    (η : HolomorphicOneForm ℂ X) (_hη : η ≠ 0)
    (_hnonconst : ¬ ∃ y₀, ∀ x, f x = y₀) :
    TraceFormsConstructionData f hf η := by
  sorry

/-- **The trace construction provider.** Three-way case split:

* `η = 0` — fully proved via `traceFormsConstructionData_zero`;
* `η ≠ 0` and `f` constant — fully proved via
  `traceFormsConstructionData_constant`;
* `η ≠ 0` and `f` nonconstant — delegates to the strictly narrower
  analytic leaf
  `traceFormsConstructionData_nonconstant_nonzero_provider`.

The first two branches are strictly smaller leaves already proved in
this pass; the third branch is the genuine analytic frontier (removable
singularity / holomorphic extension of the finite local fiber sum
across the finite branch locus of a nonconstant holomorphic map). -/
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

/-- The trace (pushforward) of a holomorphic 1-form along a smooth map.
Sorry-free shim around `traceFormsConstructionData_provider`: the trace
is the `traceForm` field of the construction data. -/
noncomputable def traceFormsBundled
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (⊤ : WithTop ℕ∞) f)
    (η : HolomorphicOneForm ℂ X) : HolomorphicOneForm ℂ Y :=
  (traceFormsConstructionData_provider f hf η).traceForm

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

private theorem dense_compl_of_finite_of_perfect
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

/-- Minimal trace input used by local linearity and regular-value
assemblies.  This separates the specification needed downstream from
the construction of the global bundled trace form. -/
structure TraceFormsRegularSpec
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (⊤ : WithTop ℕ∞) f) where
  /-- Trace sends the zero form to zero. -/
  map_zero : traceFormsBundled f hf 0 = 0
  /-- At regular values, trace agrees with the finite local fiber sum. -/
  apply_fun_regular :
    ∀ (hbc : BranchedCoverData X Y f) (η : HolomorphicOneForm ℂ X)
      (y : Y) (hy : isRegularValue hbc y),
      (traceFormsBundled f hf η).toFun y =
        traceAtRegularValue hbc (fun x => η.toFun x) y hy

end JacobianChallenge.HolomorphicForms
