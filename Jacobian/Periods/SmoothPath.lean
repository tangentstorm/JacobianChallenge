import Mathlib.Topology.Path
import Mathlib.Topology.Connected.PathConnected
import Mathlib.Geometry.Manifold.ContMDiff.Basic
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

end SmoothPath

end JacobianChallenge.Periods
