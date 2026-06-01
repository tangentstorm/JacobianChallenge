import Jacobian.HolomorphicForms.BranchedCover
import Jacobian.HolomorphicForms.HolomorphicMap
import Jacobian.HolomorphicForms.EvalAtOneHelper

/-!
# Local-pullback holomorphic-variation infrastructure (M4)

This file establishes prerequisites for discharging the project's single
custom axiom

```
axiom localPullbackAt_holomorphic
    {f : X → Y} (h : BranchedCoverData X Y f)
    (hcompat : h.RamificationIndexCompatible)
    (hf : IsHolomorphic f)
    (ω : HolomorphicOneForm ℂ X)
    (x : X) (hx : h.ramificationIndex x = 1) :
    IsHolomorphicAt (localPullbackAt h hf ω x hx) (f x)
```

(declared at `Jacobian/TraceDegree/TraceDefinition.lean:220`; see
`ref/axiom-audit.md` §1 for the 13 transitive dependents).

The axiom's proof requires that, locally near `f x`, the chart-pulled
back function `y' ↦ cotangentPushforward f (localInverseAt y')
(η.toFun (localInverseAt y'))` is analytic.

This file currently provides two prerequisite lemmas:

* **M4-prep** — `BranchedCoverData.localInverseAt_eventually_unramified`:
  the local inverse stays in the unramified locus eventually, enabling
  pointwise application of the unramified-only formula
  `cotangentPushforward_eq_toSpanSingleton_scalar` (TraceSpec.lean
  ~L1047).

* **M4b-step1** — `etaTimesOne_chart_local_analytic`: the chart-local
  analyticity of `ω.toFun · 1`. This extracts as a named lemma the
  in-line `etaTimesOne` pattern used in DB-B (TraceSpec.lean ~L2812).
  It is needed for the eventual M4-final composition with the chart-local
  cotangent-pushforward formula.

The final discharge of the axiom (M4-final) will combine these
prerequisites with `localInverseAt_holomorphic` (TraceDefinition.lean
L119) and the chart-local cotangent-pushforward machinery in TraceSpec.
-/

namespace JacobianChallenge.HolomorphicForms

open scoped Manifold Topology
open Filter Set Bundle

variable {X Y : Type*}
  [TopologicalSpace X] [ChartedSpace ℂ X]
  [TopologicalSpace Y] [ChartedSpace ℂ Y]

omit [ChartedSpace ℂ X] [ChartedSpace ℂ Y] in
/--
**Eventually-unramified at the local inverse.**

For an unramified preimage `x` of `f x` (i.e.
`h.ramificationIndex x = 1`), the local inverse `h.localInverseAt x hx`
maps a neighborhood of `f x` into the unramified locus of `f`. Hence,
for all `y'` in a neighborhood of `f x`, the preimage
`h.localInverseAt x hx y'` has ramification index `1`.

This is the bridge that lets pointwise unramified-only formulas like
`cotangentPushforward_eq_toSpanSingleton_scalar` (TraceSpec.lean
~L1047) apply uniformly in a neighborhood of `f x`, enabling the
holomorphic-variation arguments needed for `localPullbackAt_holomorphic`.

**Proof idea.** The local-bijection property of `BranchedCoverData`
at the unramified point `x` gives an open `U ⊆ X` with `x ∈ U`, open
`V ⊆ Y` with `f x ∈ V`, and `f` bijective `U → V`. The ramification
locus minus `{x}` is finite hence closed in T2 spaces. Its image under
`f` (restricted to `U`) is also finite hence closed in T2 `Y`, and
`f x` is not in this image (by `BijOn.injOn`). So `y'` near `f x`
avoids the bad image, and the bijection forces the preimage
`localInverseAt y'` outside the ramification locus.
-/
theorem BranchedCoverData.localInverseAt_eventually_unramified
    [T2Space X] [T2Space Y] [Nonempty X]
    {f : X → Y} (h : BranchedCoverData X Y f)
    (x : X) (hx : h.ramificationIndex x = 1) :
    ∀ᶠ y' in 𝓝 (f x), h.ramificationIndex (h.localInverseAt x hx y') = 1 := by
  classical
  obtain ⟨U, V, hUopen, hVopen, hxU, hfxV, hbij, hright_branch, hleft_branch⟩ :=
    h.localInverse_is_inverse hx
  set ramSet : Set X := {y | h.ramificationIndex y ≠ 1} \ {x} with hramSet_def
  have hramSet_finite : ramSet.Finite := by
    apply Set.Finite.subset h.ramified_finite
    intro y hy; exact hy.1
  have hxU' : x ∉ ramSet := by intro hramX; exact hramX.2 rfl
  have h_evt_in_V : ∀ᶠ y' in 𝓝 (f x), y' ∈ V :=
    hVopen.mem_nhds hfxV
  have h_localInv_in_U : ∀ y' ∈ V, h.localInverseAt x hx y' ∈ U := by
    intro y' hy'V
    obtain ⟨x', hx'U, hfx'⟩ := hbij.surjOn hy'V
    have h_local_at_y : h.localInverseAt x hx y' = x' := by
      rw [← hfx']
      exact hleft_branch x' hx'U
    rw [h_local_at_y]; exact hx'U
  set bad_X : Set X := U ∩ ramSet with hbad_X_def
  have hbad_X_finite : bad_X.Finite := hramSet_finite.subset (fun _ h' => h'.2)
  set bad_Y : Set Y := f '' bad_X with hbad_Y_def
  have hbad_Y_finite : bad_Y.Finite := hbad_X_finite.image f
  have hfx_not_bad : f x ∉ bad_Y := by
    intro hfxbad
    obtain ⟨x', hx'bad, hfx'eq⟩ := hfxbad
    have hx'U : x' ∈ U := hx'bad.1
    have hx'x : x' = x := hbij.injOn hx'U hxU hfx'eq
    have : x ∈ ramSet := hx'x ▸ hx'bad.2
    exact hxU' this
  have hbad_Y_closed : IsClosed bad_Y := hbad_Y_finite.isClosed
  have h_compl_nhd : bad_Yᶜ ∈ 𝓝 (f x) :=
    hbad_Y_closed.isOpen_compl.mem_nhds hfx_not_bad
  filter_upwards [h_evt_in_V, h_compl_nhd] with y' hy'V hy'bad
  by_contra h_neg
  have h_loc_in_U : h.localInverseAt x hx y' ∈ U := h_localInv_in_U y' hy'V
  have h_loc_in_ram : h.localInverseAt x hx y' ∈ ramSet := by
    refine ⟨h_neg, ?_⟩
    intro h_eq; rw [h_eq] at h_neg; exact h_neg hx
  have h_loc_in_bad : h.localInverseAt x hx y' ∈ bad_X := ⟨h_loc_in_U, h_loc_in_ram⟩
  have h_y'_in_bad : y' ∈ bad_Y := by
    refine ⟨h.localInverseAt x hx y', h_loc_in_bad, ?_⟩
    exact hright_branch y' hy'V
  exact hy'bad h_y'_in_bad

variable
  [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
  [JacobianChallenge.Periods.StableChartAt ℂ X]

/--
**Chart-local analyticity of `ω.toFun · 1` (DB-B pattern, lemma form).**

For a holomorphic 1-form `ω` on `X` and any base point `x₀`, the
function `ε ↦ (ω.toFun ((chartAt ℂ x₀).symm ε)) 1` is analytic at
`chartAt ℂ x₀ x₀`. This is the analyticity counterpart of
`continuous_eval_at_one_of_contMDiffSection` (EvalAtOneHelper.lean
L50), extracted as a stand-alone lemma rather than re-inlined per the
DB-B template at TraceSpec.lean ~L2812.

**Proof.** `ContMDiff.clm_bundle_apply` combines the smooth section `ω`
with the smooth constant-1 section `contMDiff_tangentSection_one` to
produce a smooth section of the trivial bundle. Extract `ContMDiffAt`
at `x₀`, unfold via `Trivialization.contMDiffAt_iff` then
`contMDiffAt_iff` to land in `ContDiffAt ω` of the chart-local map;
self-model `range = univ` lets `ContDiffWithinAt.analyticAt` finish.
-/
theorem etaTimesOne_chart_local_analytic
    (ω : HolomorphicOneForm ℂ X) (x₀ : X) :
    AnalyticAt ℂ (fun ε : ℂ => (ω.toFun ((chartAt ℂ x₀).symm ε)) (1 : ℂ))
      (chartAt ℂ x₀ x₀) := by
  have h1 : ContMDiff (𝓘(ℂ, ℂ)) ((𝓘(ℂ, ℂ)).prod (𝓘(ℂ, ℂ))) ⊤
      (fun x : X => Bundle.TotalSpace.mk' ℂ (E := Bundle.Trivial X ℂ) x
        (show (Bundle.Trivial X ℂ) x from (ω.toFun x) (1 : ℂ))) :=
    ω.contMDiff.clm_bundle_apply contMDiff_tangentSection_one
  have hsrc : (fun x : X => Bundle.TotalSpace.mk' ℂ
      (E := Bundle.Trivial X ℂ) x ((ω.toFun x) (1 : ℂ))) x₀
        ∈ (trivializationAt ℂ (Bundle.Trivial X ℂ) x₀).source := by
    rw [Trivialization.mem_source]
    exact FiberBundle.mem_baseSet_trivializationAt' x₀
  have h_iff :=
    (trivializationAt ℂ (Bundle.Trivial X ℂ) x₀).contMDiffAt_iff
      (IB := 𝓘(ℂ, ℂ)) (IM := 𝓘(ℂ, ℂ)) (n := (⊤ : WithTop ℕ∞))
      (f := fun x : X => Bundle.TotalSpace.mk' ℂ (E := Bundle.Trivial X ℂ) x
        ((ω.toFun x) (1 : ℂ)))
      hsrc
  have h_evalOne : ContMDiffAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ⊤
      (fun x : X => (ω.toFun x) (1 : ℂ)) x₀ :=
    (h_iff.mp h1.contMDiffAt).2
  rw [contMDiffAt_iff] at h_evalOne
  obtain ⟨_h_cont, h_cdwithin⟩ := h_evalOne
  rw [ModelWithCorners.range_eq_univ, contDiffWithinAt_univ] at h_cdwithin
  exact h_cdwithin.analyticAt

end JacobianChallenge.HolomorphicForms
