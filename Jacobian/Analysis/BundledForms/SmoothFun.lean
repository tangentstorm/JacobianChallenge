import Mathlib.Geometry.Manifold.ContMDiffMap
import Mathlib.Geometry.Manifold.Algebra.SmoothFunctions
import Mathlib.Geometry.Manifold.Algebra.Structures

/-!
# Phase 1.1 — `SmoothFun M` : the bundle of `C^∞` real-valued functions on `M`

This file is the M1 substrate for the R10 dispatch plan
(`/root/.claude/plans/okay-let-s-plan-out-shimmering-hearth.md`).

The Lean stack of `Jacobian/Analysis/SobolevElliptic` and
`Jacobian/Analysis/BundledForms` currently uses the placeholder
`Omega M 0 := PUnit`.  This file replaces it (additively, via a
companion bridge in `Omega0.lean`) with a *real* `ℝ`-vector-space
of smooth real-valued functions on `M`, by wrapping Mathlib's
`ContMDiffMap` with the algebra instances already provided in
`Mathlib/Geometry/Manifold/Algebra/SmoothFunctions.lean`.

Key Mathlib hooks (no project-side reproof needed):

* `Mathlib/Geometry/Manifold/ContMDiffMap.lean` — `ContMDiffMap` and the
  `C^n⟮I, M; ℝ⟯` notation.
* `Mathlib/Geometry/Manifold/Algebra/SmoothFunctions.lean` —
  `ContMDiffMap.{addCommGroup, ring, commRing, module, algebra}` for
  values in any `ContMDiffRing`.
* `Mathlib/Geometry/Manifold/Algebra/Structures.lean` —
  `instFieldContMDiffRing : ContMDiffRing 𝓘(𝕜) n 𝕜` automatically
  provides the `[ContMDiffRing 𝓘(ℝ, ℝ) ⊤ ℝ]` we need.

So everything below is a thin re-exposure: define `SmoothFun M` as the
ambient `C^∞⟮𝓘(ℝ, E), M; ℝ⟯`, re-derive the project-side instances by
`inferInstance`, and provide `coeFn` lemmas in the project's namespace
for downstream stability.
-/

namespace JacobianChallenge.Analysis.BundledForms

set_option linter.unusedSectionVars false

open scoped Manifold ContDiff

universe u

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
  (M : Type) [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold (modelWithCornersSelf ℝ E) (⊤ : WithTop ℕ∞) M]

/-- **Phase 1.1.**  `SmoothFun M` is the `ℝ`-vector space of `C^∞`
real-valued functions on `M`.  Concretely the Mathlib bundled type
`C^∞⟮𝓘(ℝ, E), M; ℝ⟯`. -/
def SmoothFun : Type :=
  C^(⊤ : WithTop ℕ∞)⟮modelWithCornersSelf ℝ E, M; ℝ⟯

namespace SmoothFun

/-! ### Re-derived algebra instances

All instances below come from
`Mathlib/Geometry/Manifold/Algebra/SmoothFunctions.lean` plus
`Mathlib/Geometry/Manifold/Algebra/Structures.lean`'s
`instFieldContMDiffRing`.  We re-state them here so that downstream
files can refer to `SmoothFun M` instead of unfolding to the
`ContMDiffMap` notation. -/

noncomputable instance : FunLike (SmoothFun (E := E) M) M ℝ := by
  unfold SmoothFun; infer_instance

noncomputable instance : AddCommGroup (SmoothFun (E := E) M) := by
  unfold SmoothFun; infer_instance

noncomputable instance : CommRing (SmoothFun (E := E) M) := by
  unfold SmoothFun; infer_instance

noncomputable instance : Module ℝ (SmoothFun (E := E) M) := by
  unfold SmoothFun; infer_instance

noncomputable instance : Algebra ℝ (SmoothFun (E := E) M) := by
  unfold SmoothFun; infer_instance

/-- The constant smooth function with value `c : ℝ`. -/
noncomputable def const (c : ℝ) : SmoothFun (E := E) M :=
  ContMDiffMap.const c

/-- A smooth function `M → ℝ`, viewed as a plain function. -/
@[simp]
theorem const_apply (c : ℝ) (x : M) :
    (const (E := E) M c : M → ℝ) x = c := rfl

/-- The zero smooth function. -/
@[simp]
theorem zero_apply (x : M) : ((0 : SmoothFun (E := E) M) : M → ℝ) x = 0 := rfl

/-- The one smooth function. -/
@[simp]
theorem one_apply (x : M) : ((1 : SmoothFun (E := E) M) : M → ℝ) x = 1 := rfl

/-- Pointwise addition of smooth functions. -/
@[simp]
theorem add_apply (f g : SmoothFun (E := E) M) (x : M) :
    ((f + g : SmoothFun (E := E) M) : M → ℝ) x = f x + g x := rfl

/-- Pointwise multiplication of smooth functions. -/
@[simp]
theorem mul_apply (f g : SmoothFun (E := E) M) (x : M) :
    ((f * g : SmoothFun (E := E) M) : M → ℝ) x = f x * g x := rfl

/-- Pointwise scalar multiplication. -/
@[simp]
theorem smul_apply (c : ℝ) (f : SmoothFun (E := E) M) (x : M) :
    ((c • f : SmoothFun (E := E) M) : M → ℝ) x = c * f x := rfl

/-- Smooth functions are continuous. -/
theorem continuous (f : SmoothFun (E := E) M) :
    Continuous (f : M → ℝ) :=
  (show ContMDiffMap _ _ _ _ _ from f).contMDiff.continuous

end SmoothFun

end JacobianChallenge.Analysis.BundledForms
