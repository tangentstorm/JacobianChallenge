import Jacobian.Analysis.BundledForms.L2Norm
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.Complete

/-!
# Phase 1.5 — `L2Fun M` : Hilbert completion of `SmoothFun M`

This is the M1 finish line: the real Hilbert space `L²(M, ℝ)` for a
compact manifold `M` with a finite Borel measure `μ`, plus the
canonical inclusion `SmoothFun M ↪ L²(M)`.

The substantive content reuses Mathlib's `Lp` machinery in full:
* `Mathlib/MeasureTheory/Function/LpSpace/Basic.lean` —
  `MeasureTheory.Lp` and `MemLp.toLp`.
* `Mathlib/MeasureTheory/Function/LpSpace/Complete.lean` —
  `instCompleteSpace : CompleteSpace (Lp E p μ)`.
* `Mathlib/MeasureTheory/Function/L2Space.lean` —
  `instInner` and `innerProductSpace : InnerProductSpace 𝕜 (α →₂[μ] E)`.

So everything below is plumbing: define `L2Fun M μ := Lp ℝ 2 μ`,
re-derive `InnerProductSpace ℝ` and `CompleteSpace`, and provide
the inclusion `smoothFunToL2 : SmoothFun M → L2Fun M μ` (a `ℝ`-
linear map; bounded since `‖f‖_{L²} ≤ √μ(M) · sup‖f‖`, but we don't
need the bound here — the inclusion as a *plain* `LinearMap` is
enough for Phase 2).
-/

namespace JacobianChallenge.Analysis.BundledForms

set_option linter.unusedSectionVars false

open scoped Manifold ContDiff NNReal ENNReal
open MeasureTheory

universe u

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
  (M : Type) [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold (modelWithCornersSelf ℝ E) (⊤ : WithTop ℕ∞) M]
  [MeasurableSpace M] [BorelSpace M] [CompactSpace M]
  (μ : Measure M) [IsManifoldMeasure M μ]

/-- **Phase 1.5.**  `L2Fun M μ` is the Hilbert space `L²(M, ℝ)` of
square-integrable real-valued functions on `M` with respect to `μ`.
Concretely the Mathlib bundled type `M →₂[μ] ℝ`. -/
def L2Fun : Type := Lp (α := M) ℝ 2 μ

namespace L2Fun

/-! ### Re-derived Hilbert-space instances -/

noncomputable instance : NormedAddCommGroup (L2Fun M μ) := by
  unfold L2Fun; infer_instance

noncomputable instance : InnerProductSpace ℝ (L2Fun M μ) := by
  unfold L2Fun; infer_instance

instance : CompleteSpace (L2Fun M μ) := by
  unfold L2Fun; infer_instance

end L2Fun

/-! ### `SmoothFun` includes into `L2Fun` -/

/-- The canonical inclusion `SmoothFun M ↪ L²(M)`.  A smooth real
function on a compact manifold is bounded and hence square-integrable
against any finite Borel measure; we package the inclusion as a plain
`ℝ`-linear map. -/
noncomputable def smoothFunToL2 : SmoothFun (E := E) M →ₗ[ℝ] L2Fun M μ where
  toFun f := MemLp.toLp (f : M → ℝ) (SmoothFun.memLp (E := E) M μ 2 f)
  map_add' f g := by
    apply MeasureTheory.Lp.ext
    have h₁ := MemLp.coeFn_toLp (SmoothFun.memLp (E := E) M μ 2 (f + g))
    have h₂ := MemLp.coeFn_toLp (SmoothFun.memLp (E := E) M μ 2 f)
    have h₃ := MemLp.coeFn_toLp (SmoothFun.memLp (E := E) M μ 2 g)
    have h₄ := Lp.coeFn_add (MemLp.toLp (f : M → ℝ) (SmoothFun.memLp (E := E) M μ 2 f))
      (MemLp.toLp (g : M → ℝ) (SmoothFun.memLp (E := E) M μ 2 g))
    filter_upwards [h₁, h₂, h₃, h₄] with x hx₁ hx₂ hx₃ hx₄
    rw [hx₁, hx₄, Pi.add_apply, hx₂, hx₃]
    rfl
  map_smul' c f := by
    apply MeasureTheory.Lp.ext
    have h₁ := MemLp.coeFn_toLp (SmoothFun.memLp (E := E) M μ 2 (c • f))
    have h₂ := MemLp.coeFn_toLp (SmoothFun.memLp (E := E) M μ 2 f)
    have h₃ := Lp.coeFn_smul c (MemLp.toLp (f : M → ℝ) (SmoothFun.memLp (E := E) M μ 2 f))
    filter_upwards [h₁, h₂, h₃] with x hx₁ hx₂ hx₃
    simp only [RingHom.id_apply]
    rw [hx₁, hx₃, Pi.smul_apply, hx₂]
    simp

/-! ### M1 verification examples -/

/-- **M1 verification (instance).**  `L2Fun M μ` is a real
`InnerProductSpace`. -/
noncomputable example : InnerProductSpace ℝ (L2Fun M μ) := inferInstance

/-- **M1 verification (instance).**  `L2Fun M μ` is complete. -/
example : CompleteSpace (L2Fun M μ) := inferInstance

end JacobianChallenge.Analysis.BundledForms
