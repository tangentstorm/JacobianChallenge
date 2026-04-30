import Mathlib.Topology.Path
import Mathlib.Topology.Connected.PathConnected
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

end SmoothPath

end JacobianChallenge.Periods
