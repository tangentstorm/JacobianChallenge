import Mathlib.Topology.Path
import Mathlib.Topology.Connected.PathConnected
import Mathlib.Geometry.Manifold.ContMDiff.Basic
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Geometry.Manifold.MFDeriv.Basic

/-!
# Smooth paths on a real manifold

A `SmoothPath I_M a b` on a `ChartedSpace H X` (with model `I_M`) is a
`Path a b` together with a proof of `ContMDiff` of its `ℝ`-extension
with respect to the manifold's smoothness model — at smoothness target
`n = 1` (real `C¹`), as required by Mathlib's
`ContinuousOn.curveIntegrable_of_contDiffOn` for path integration.

The wrapper avoids threading `ContMDiff ... 1` through every downstream
lemma and exposes the standard `Path` algebra (`refl`, etc.) at the
smooth level.

The smoothness target is fixed at the *real* manifold model
(`ModelWithCorners ℝ E H`) because curve integration in Mathlib v4.28.0
is `ℝ`-parameterised: `Path a b` has source `unitInterval ⊆ ℝ`, and
`Path.extend γ : C(ℝ, X)`. To extend smooth-target-side smoothness
(the manifold) to be compatible with the `ℝ`-parameterised source,
the source uses `modelWithCornersSelf ℝ ℝ` and the target's manifold
must therefore also be a real manifold (which it is — even complex
manifolds restrict to real manifolds). For our project, `X` is a complex
1-manifold, which is canonically a real 2-manifold; we instantiate
`I_M := modelWithCornersSelf ℂ ℂ` and Lean accepts it because `ℂ` is
canonically a real normed space via `RestrictScalars`.

## API

* `SmoothPath I_M a b` — the structure.
* `SmoothPath.refl I_M a` — the constant smooth path at `a`.
* `SmoothPath.toPath` — coercion forgetting smoothness.
-/

namespace JacobianChallenge.Periods

open Set unitInterval

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H]
  {X : Type*} [TopologicalSpace X] [ChartedSpace H X]

/-- A smooth path on a real manifold `X` (modeled on `(E, H, I_M)`):
a `Path a b` whose `ℝ`-extension is `C¹` as a manifold map. -/
structure SmoothPath (I_M : ModelWithCorners ℝ E H)
    [ChartedSpace H X] (a b : X) where
  /-- The underlying path. -/
  toPath : Path a b
  /-- The path's `ℝ`-extension is `C¹` as a manifold map. -/
  contMDiff_extend : ContMDiff (modelWithCornersSelf ℝ ℝ) I_M (1 : WithTop ℕ∞)
    toPath.extend

namespace SmoothPath

variable {I_M : ModelWithCorners ℝ E H} {a b c : X}

/-- The underlying path. -/
@[simp] theorem coe_mk (γ : Path a b)
    (h : ContMDiff (modelWithCornersSelf ℝ ℝ) I_M (1 : WithTop ℕ∞) γ.extend) :
    (⟨γ, h⟩ : SmoothPath I_M a b).toPath = γ := rfl

/-- Two smooth paths are equal iff their underlying paths are equal. -/
@[ext] theorem ext {γ γ' : SmoothPath I_M a b}
    (h : γ.toPath = γ'.toPath) : γ = γ' := by
  cases γ; cases γ'; congr

/-- The constant smooth path at a point. -/
def refl (I_M : ModelWithCorners ℝ E H) (a : X) : SmoothPath I_M a a where
  toPath := Path.refl a
  contMDiff_extend := by
    have : (Path.refl a).extend = fun _ : ℝ => a := by
      funext t
      simp [Path.extend, Set.IccExtend, Path.refl]
    rw [this]
    exact contMDiff_const

/-- The reverse of a smooth path, obtained by `Path.symm` on the
underlying path. Smoothness of the extension follows from smoothness
of `t ↦ 1 - t` (the reflection on `ℝ`) composed with the original
extension's smoothness.

Uses `Path.extend_symm` (`γ.symm.extend = (γ.extend <| 1 - ·)`). -/
def symm (γ : SmoothPath I_M a b) : SmoothPath I_M b a where
  toPath := γ.toPath.symm
  contMDiff_extend := by
    rw [Path.extend_symm]
    -- Goal: ContMDiff _ I_M 1 (fun t : ℝ => γ.toPath.extend (1 - t)).
    -- This is γ.contMDiff_extend composed with the smooth map t ↦ 1 - t.
    have hsub : ContMDiff (modelWithCornersSelf ℝ ℝ) (modelWithCornersSelf ℝ ℝ)
        (1 : WithTop ℕ∞) (fun t : ℝ => 1 - t) :=
      ContDiff.contMDiff (by fun_prop)
    exact γ.contMDiff_extend.comp hsub

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
  contMDiff_extend := by
    -- (γ.toPath.map h).extend t = f (γ.toPath.extend t).
    have hext : (γ.toPath.map hf.continuous).extend = f ∘ γ.toPath.extend := by
      funext t
      show (γ.toPath.map hf.continuous).extend t = f (γ.toPath.extend t)
      unfold Path.extend
      simp only [ContinuousMap.coe_mk, Set.IccExtend, Function.comp_apply]
      rfl
    rw [hext]
    exact hf.comp γ.contMDiff_extend

/-! ### Bridge to chart coordinates

`SmoothPath`'s smoothness is *manifold*-smoothness. For path
integration via `Mathlib`'s `curveIntegrable_of_contDiffOn`, we need
*chart-coordinate* `ContDiffOn ℝ 1` of the lifted path. The bridge:
compose with the chart's `toFun` and use `contMDiffOn_chart` plus
`contMDiff_iff_contDiff` (since both source and target are normed
spaces in chart coordinates). -/

/-- The chart-lifted extension of a smooth path is `ContMDiff` to the
model space, on the `Path`'s domain (in fact on all of `ℝ` if the
chart-source membership is everywhere; more generally, on the
preimage of the chart's source under the extension). -/
theorem chart_comp_extend_contMDiffOn
    [IsManifold I_M (1 : WithTop ℕ∞) X]
    (γ : SmoothPath I_M a b) (x : X) :
    ContMDiffOn (modelWithCornersSelf ℝ ℝ) I_M (1 : WithTop ℕ∞)
      (chartAt H x ∘ γ.toPath.extend)
      (γ.toPath.extend ⁻¹' (chartAt H x).source) := by
  -- chartAt H x is ContMDiffOn on its source.
  have hchart : ContMDiffOn I_M I_M (1 : WithTop ℕ∞)
      (chartAt H x) (chartAt H x).source := contMDiffOn_chart
  -- γ.toPath.extend is ContMDiff into X.
  have hext : ContMDiff (modelWithCornersSelf ℝ ℝ) I_M (1 : WithTop ℕ∞)
      γ.toPath.extend := γ.contMDiff_extend
  exact hchart.comp hext.contMDiffOn (fun _ ht => ht)

end SmoothPath

end JacobianChallenge.Periods
