import Mathlib.Topology.Path
import Mathlib.Topology.Connected.PathConnected
import Mathlib.Topology.Subpath
import Mathlib.Geometry.Manifold.ContMDiff.Basic
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Geometry.Manifold.MFDeriv.Basic

/-!
# Smooth paths on a real manifold

A `SmoothPath I_M a b` on a `ChartedSpace H X` (with model `I_M`) is a
`Path a b` together with a proof that its `ℝ`-extension is `C¹` as a
manifold map *on the unit interval* `[0,1]`.

The wrapper avoids threading `ContMDiffOn ... [0,1]` through every
downstream lemma and exposes the standard `Path` algebra (`refl`, etc.)
at the smooth level.

## Why `ContMDiffOn ... (Set.Icc 0 1)` (and not `ContMDiff` on all of `ℝ`)

`Path.extend` is constructed via `Set.IccExtend`, which clamps inputs
to `[0,1]`. Thus `Path.extend` is constant on `(-∞, 0]` and `[1, ∞)`.
For `Path.extend` to be `C¹` as a function on all of `ℝ`, the path's
derivative at `t = 0` and `t = 1` would have to vanish — which fails
for generic paths (e.g. linear interpolations). Restricting smoothness
to `[0,1]` matches Mathlib's curve-integral conventions
(`curveIntegralFun ω γ t = ω(γ.extend t)(derivWithin γ.extend (Icc 0 1) t)`),
which only accesses the path's behavior on `[0,1]`.

## Real-manifold target

The smoothness target is fixed at the *real* manifold model
(`ModelWithCorners ℝ E H`) because curve integration in Mathlib v4.28.0
is `ℝ`-parameterised: `Path a b` has source `unitInterval ⊆ ℝ`. The
source uses `modelWithCornersSelf ℝ ℝ`. For our project, `X` is a
complex 1-manifold, which is canonically a real 2-manifold; we
instantiate `I_M := modelWithCornersSelf ℂ ℂ` and Lean accepts it
because `ℂ` is canonically a real normed space via `RestrictScalars`.

## API

* `SmoothPath I_M a b` — the structure.
* `SmoothPath.refl I_M a` — the constant smooth path at `a`.
* `SmoothPath.symm` — reverse.
* `SmoothPath.map` — pushforward along a smooth map.
* `SmoothPath.toPath` — coercion forgetting smoothness.
-/

namespace JacobianChallenge.Periods

open Set unitInterval

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H]
  {X : Type*} [TopologicalSpace X] [ChartedSpace H X]

/-- A smooth path on a real manifold `X` (modeled on `(E, H, I_M)`):
a `Path a b` whose `ℝ`-extension is `C¹` as a manifold map *on the
unit interval*. We require smoothness only on `[0,1]` because
`Path.extend` is clamped via `IccExtend` outside `[0,1]`, which would
otherwise force endpoint derivatives to vanish. -/
structure SmoothPath (I_M : ModelWithCorners ℝ E H)
    [ChartedSpace H X] (a b : X) where
  /-- The underlying path. -/
  toPath : Path a b
  /-- The path's `ℝ`-extension is `C¹` on `[0,1]` as a manifold map. -/
  contMDiffOn_extend : ContMDiffOn (modelWithCornersSelf ℝ ℝ) I_M
    (1 : WithTop ℕ∞) toPath.extend (Set.Icc 0 1)

namespace SmoothPath

variable {I_M : ModelWithCorners ℝ E H} {a b c : X}

/-- The underlying path (constructor projection). -/
@[simp] theorem coe_mk (γ : Path a b)
    (h : ContMDiffOn (modelWithCornersSelf ℝ ℝ) I_M (1 : WithTop ℕ∞)
      γ.extend (Set.Icc 0 1)) :
    (⟨γ, h⟩ : SmoothPath I_M a b).toPath = γ := rfl

/-- Two smooth paths are equal iff their underlying paths are equal. -/
@[ext] theorem ext {γ γ' : SmoothPath I_M a b}
    (h : γ.toPath = γ'.toPath) : γ = γ' := by
  cases γ; cases γ'; congr

/-- The constant smooth path at a point. -/
def refl (I_M : ModelWithCorners ℝ E H) (a : X) : SmoothPath I_M a a where
  toPath := Path.refl a
  contMDiffOn_extend := by
    have : (Path.refl a).extend = fun _ : ℝ => a := by
      funext t
      simp [Path.extend, Set.IccExtend, Path.refl]
    rw [this]
    exact contMDiffOn_const

/-- The reverse of a smooth path, obtained by `Path.symm` on the
underlying path. Smoothness of the extension follows from smoothness
of `t ↦ 1 - t` (the reflection on `ℝ`) composed with the original
extension's smoothness.

Uses `Path.extend_symm` (`γ.symm.extend = (γ.extend <| 1 - ·)`). -/
def symm (γ : SmoothPath I_M a b) : SmoothPath I_M b a where
  toPath := γ.toPath.symm
  contMDiffOn_extend := by
    rw [Path.extend_symm]
    -- Goal: ContMDiffOn _ I_M 1 (fun t : ℝ => γ.toPath.extend (1 - t)) (Icc 0 1).
    -- This is γ.contMDiffOn_extend composed with the smooth map t ↦ 1 - t,
    -- which maps Icc 0 1 to Icc 0 1.
    have hsub : ContMDiff (modelWithCornersSelf ℝ ℝ) (modelWithCornersSelf ℝ ℝ)
        (1 : WithTop ℕ∞) (fun t : ℝ => 1 - t) :=
      ContDiff.contMDiff (by fun_prop)
    have hmap : Set.MapsTo (fun t : ℝ => 1 - t) (Set.Icc 0 1) (Set.Icc 0 1) := by
      intro t ht
      rcases ht with ⟨h0, h1⟩
      exact ⟨by linarith, by linarith⟩
    exact γ.contMDiffOn_extend.comp hsub.contMDiffOn hmap

/-- Push a smooth path forward along a `ContMDiff` map between manifolds.
The smoothness of the underlying `Path.map` extension follows from
composition of smooth maps: `(γ.map h).extend = f ∘ γ.extend` (when
`f` is continuous; here we strengthen `Continuous` to `ContMDiff`). -/
def map {Y : Type*} [TopologicalSpace Y] {H' : Type*} [TopologicalSpace H']
    {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    [ChartedSpace H' Y] (I_N : ModelWithCorners ℝ E' H')
    (γ : SmoothPath I_M a b) (f : X → Y)
    (hf : ContMDiff I_M I_N (1 : WithTop ℕ∞) f) :
    SmoothPath I_N (f a) (f b) where
  toPath := γ.toPath.map hf.continuous
  contMDiffOn_extend := by
    -- (γ.toPath.map h).extend t = f (γ.toPath.extend t).
    have hext : (γ.toPath.map hf.continuous).extend = f ∘ γ.toPath.extend := by
      funext t
      show (γ.toPath.map hf.continuous).extend t = f (γ.toPath.extend t)
      unfold Path.extend
      simp only [ContinuousMap.coe_mk, Set.IccExtend, Function.comp_apply]
      rfl
    rw [hext]
    exact hf.comp_contMDiffOn γ.contMDiffOn_extend

/-- The subpath of a smooth path: smoothness propagates through the
affine reparameterization `s ↦ (1-s)·t₀ + s·t₁` (which maps `[0,1]`
into `[0,1]` since `t₀, t₁ ∈ unitInterval`). -/
def subpath (γ : SmoothPath I_M a b) (t₀ t₁ : unitInterval) :
    SmoothPath I_M (γ.toPath t₀) (γ.toPath t₁) where
  toPath := γ.toPath.subpath t₀ t₁
  contMDiffOn_extend := by
    -- On [0,1], (γ.subpath t₀ t₁).extend s = γ.extend ((1-s)·t₀ + s·t₁).
    -- The affine map sends [0,1] into [0,1] (convex combination of points
    -- in [0,1] stays in [0,1]).
    have aff_C1 : ContMDiff (modelWithCornersSelf ℝ ℝ) (modelWithCornersSelf ℝ ℝ)
        (1 : WithTop ℕ∞) (fun s : ℝ => (1 - s) * (t₀ : ℝ) + s * (t₁ : ℝ)) :=
      ContDiff.contMDiff (by fun_prop)
    have aff_maps : Set.MapsTo
        (fun s : ℝ => (1 - s) * (t₀ : ℝ) + s * (t₁ : ℝ))
        (Set.Icc 0 1) (Set.Icc 0 1) := by
      intro s hs
      rcases hs with ⟨hs0, hs1⟩
      have ht0 := t₀.2
      have ht1 := t₁.2
      refine ⟨?_, ?_⟩
      · have h1ms : (0 : ℝ) ≤ 1 - s := by linarith
        have h1 : 0 ≤ (1 - s) * (t₀ : ℝ) := mul_nonneg h1ms ht0.1
        have h2 : 0 ≤ s * (t₁ : ℝ) := mul_nonneg hs0 ht1.1
        linarith
      · have h1 : (1 - s) * (t₀ : ℝ) ≤ (1 - s) * 1 := by
          apply mul_le_mul_of_nonneg_left ht0.2 (by linarith)
        have h2 : s * (t₁ : ℝ) ≤ s * 1 := by
          apply mul_le_mul_of_nonneg_left ht1.2 hs0
        nlinarith
    -- Reduce (subpath).extend on [0,1] to γ.extend ∘ affine.
    have hext : ∀ s ∈ Set.Icc (0 : ℝ) 1,
        (γ.toPath.subpath t₀ t₁).extend s =
          (γ.toPath.extend ∘ (fun s : ℝ => (1 - s) * (t₀ : ℝ) + s * (t₁ : ℝ))) s := by
      intro s hs
      have hin : (1 - s) * (t₀ : ℝ) + s * (t₁ : ℝ) ∈ Set.Icc (0 : ℝ) 1 :=
        aff_maps hs
      simp only [Function.comp_apply]
      rw [Path.extend_apply _ hs, Path.extend_apply _ hin]
      show γ.toPath.subpath t₀ t₁ ⟨s, hs⟩ =
           γ.toPath ⟨(1 - s) * (t₀ : ℝ) + s * (t₁ : ℝ), hin⟩
      -- subpath is γ.toPath ∘ subpathAux t₀ t₁; both sides are γ.toPath
      -- applied to the same value-in-I.
      rfl
    -- Apply ContMDiffOn.congr to swap to the explicit form, then compose.
    have hcomp : ContMDiffOn (modelWithCornersSelf ℝ ℝ) I_M (1 : WithTop ℕ∞)
        (γ.toPath.extend ∘ fun s : ℝ => (1 - s) * (t₀ : ℝ) + s * (t₁ : ℝ))
        (Set.Icc 0 1) :=
      γ.contMDiffOn_extend.comp aff_C1.contMDiffOn aff_maps
    exact hcomp.congr hext

/-! ### Bridge to chart coordinates

`SmoothPath`'s smoothness is *manifold*-smoothness on `[0,1]`. For
path integration via `Mathlib`'s `curveIntegrable_of_contDiffOn`, we
need *chart-coordinate* `ContDiffOn ℝ 1` of the lifted path on
`[0,1] ∩ extend⁻¹(chart source)`. The bridge: compose with `extChartAt`
(chart followed by the model embedding into the normed space `E`),
then convert from `ContMDiffOn` to `ContDiffOn` via
`contMDiffOn_iff_contDiffOn` (both sides now between normed spaces). -/

/-- The chart-lifted extension of a smooth path is `ContMDiffOn` to
the chart's target chart-source as a partial map into `H`. Composes
the path's manifold smoothness with the chart's manifold smoothness. -/
theorem chart_comp_extend_contMDiffOn
    [IsManifold I_M (1 : WithTop ℕ∞) X]
    (γ : SmoothPath I_M a b) (x : X) :
    ContMDiffOn (modelWithCornersSelf ℝ ℝ) I_M (1 : WithTop ℕ∞)
      (chartAt H x ∘ γ.toPath.extend)
      (Set.Icc 0 1 ∩ γ.toPath.extend ⁻¹' (chartAt H x).source) := by
  have hchart : ContMDiffOn I_M I_M (1 : WithTop ℕ∞)
      (chartAt H x) (chartAt H x).source := contMDiffOn_chart
  exact hchart.comp (γ.contMDiffOn_extend.mono Set.inter_subset_left)
    (fun _ ht => ht.2)

/-- The `extChartAt`-lifted extension of a smooth path is `ContMDiffOn`
to `(E, 𝓘(ℝ, E))` — a *normed-space-target* smoothness. This converts
to `ContDiffOn ℝ 1` via `contMDiffOn_iff_contDiffOn`. -/
theorem extChart_comp_extend_contMDiffOn
    [IsManifold I_M (1 : WithTop ℕ∞) X]
    (γ : SmoothPath I_M a b) (x : X) :
    ContMDiffOn (modelWithCornersSelf ℝ ℝ) (modelWithCornersSelf ℝ E)
      (1 : WithTop ℕ∞)
      (extChartAt I_M x ∘ γ.toPath.extend)
      (Set.Icc 0 1 ∩ γ.toPath.extend ⁻¹' (chartAt H x).source) := by
  have hchart : ContMDiffOn I_M (modelWithCornersSelf ℝ E) (1 : WithTop ℕ∞)
      (extChartAt I_M x) (chartAt H x).source :=
    contMDiffOn_extChartAt
  exact hchart.comp (γ.contMDiffOn_extend.mono Set.inter_subset_left)
    (fun _ ht => ht.2)

/-- The chart-coordinate path is `ContDiffOn ℝ 1`, which is exactly the
hypothesis Mathlib's `curveIntegrable_of_contDiffOn` consumes. Derived
from `extChart_comp_extend_contMDiffOn` by `contMDiffOn_iff_contDiffOn`. -/
theorem extChart_comp_extend_contDiffOn
    [IsManifold I_M (1 : WithTop ℕ∞) X]
    (γ : SmoothPath I_M a b) (x : X) :
    ContDiffOn ℝ (1 : WithTop ℕ∞)
      (extChartAt I_M x ∘ γ.toPath.extend)
      (Set.Icc 0 1 ∩ γ.toPath.extend ⁻¹' (chartAt H x).source) := by
  rw [← contMDiffOn_iff_contDiffOn]
  exact γ.extChart_comp_extend_contMDiffOn x

/-- If a smooth path's range is contained in the source of a single chart,
the chart-coordinate path is `ContDiffOn ℝ 1` on the entire `Set.Icc 0 1`. -/
theorem extChart_comp_extend_contDiffOn_unitInterval
    [IsManifold I_M (1 : WithTop ℕ∞) X]
    (γ : SmoothPath I_M a b) (x : X)
    (hsrc : Set.range γ.toPath ⊆ (chartAt H x).source) :
    ContDiffOn ℝ (1 : WithTop ℕ∞)
      (extChartAt I_M x ∘ γ.toPath.extend) (Set.Icc 0 1) := by
  -- The bridge gives ContDiffOn on (Icc 0 1) ∩ preimage; we show the
  -- intersection equals (Icc 0 1) under hsrc.
  have key : Set.Icc (0 : ℝ) 1 ⊆ γ.toPath.extend ⁻¹' (chartAt H x).source := by
    intro t ht
    show γ.toPath.extend t ∈ (chartAt H x).source
    rw [show γ.toPath.extend t = γ.toPath ⟨t, ht⟩ from
          γ.toPath.extend_apply ht]
    exact hsrc ⟨_, rfl⟩
  have heq : Set.Icc (0 : ℝ) 1 ∩ γ.toPath.extend ⁻¹' (chartAt H x).source =
      Set.Icc 0 1 := Set.inter_eq_left.mpr key
  have := γ.extChart_comp_extend_contDiffOn x
  rw [heq] at this
  exact this

/-! ### Convenience equalities for the underlying `Path` -/

/-- The underlying path of a smooth path, evaluated at the source endpoint. -/
@[simp] theorem toPath_zero (γ : SmoothPath I_M a b) :
    γ.toPath 0 = a := γ.toPath.source

/-- The underlying path of a smooth path, evaluated at the target endpoint. -/
@[simp] theorem toPath_one (γ : SmoothPath I_M a b) :
    γ.toPath 1 = b := γ.toPath.target

/-- The smooth-path's extension agrees with its underlying path on
the unit interval. -/
theorem extend_eq_toPath (γ : SmoothPath I_M a b) (t : unitInterval) :
    γ.toPath.extend t = γ.toPath t :=
  γ.toPath.extend_apply t.2

/-- `SmoothPath.refl I_M a` has underlying path `Path.refl a`. -/
@[simp] theorem refl_toPath (a : X) :
    (refl I_M a).toPath = Path.refl a := rfl

/-- `SmoothPath.symm γ` has underlying path `γ.toPath.symm`. -/
@[simp] theorem symm_toPath (γ : SmoothPath I_M a b) :
    γ.symm.toPath = γ.toPath.symm := rfl

/-- `SmoothPath.subpath γ t₀ t₁` has underlying path
`γ.toPath.subpath t₀ t₁`. -/
@[simp] theorem subpath_toPath (γ : SmoothPath I_M a b) (t₀ t₁ : unitInterval) :
    (γ.subpath t₀ t₁).toPath = γ.toPath.subpath t₀ t₁ := rfl

/-- `SmoothPath.map I_N γ f hf` has underlying path `γ.toPath.map hf.continuous`. -/
@[simp] theorem map_toPath {Y : Type*} [TopologicalSpace Y]
    {H' : Type*} [TopologicalSpace H']
    {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    [ChartedSpace H' Y] (I_N : ModelWithCorners ℝ E' H')
    (γ : SmoothPath I_M a b) (f : X → Y)
    (hf : ContMDiff I_M I_N (1 : WithTop ℕ∞) f) :
    (γ.map I_N f hf).toPath = γ.toPath.map hf.continuous := rfl

/-- A smooth path is, in particular, continuous. -/
theorem continuous_extend (γ : SmoothPath I_M a b) :
    ContinuousOn γ.toPath.extend (Set.Icc 0 1) :=
  γ.contMDiffOn_extend.continuousOn

/-- The underlying continuous-path `toPath` is itself continuous on
the unit interval (this is automatic for any `Path`, but is exposed
here for ergonomics). -/
theorem continuous_toPath (γ : SmoothPath I_M a b) :
    Continuous γ.toPath.toFun :=
  γ.toPath.continuous_toFun

end SmoothPath

end JacobianChallenge.Periods
