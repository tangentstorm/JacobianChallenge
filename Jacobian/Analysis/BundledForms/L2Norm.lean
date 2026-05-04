import Jacobian.Analysis.BundledForms.SmoothFun
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Topology.Algebra.Support

/-!
# Phase 1.4 — `L2Inner` on `SmoothFun M`

The L²-inner product `⟨f, g⟩ := ∫ x, f x * g x ∂μ` on the real-vector-
space `SmoothFun M` of smooth real-valued functions on a *compact*
manifold `M`, with respect to a project-side `Measure M`.

The dispatch plan deliberately takes `μ : Measure M` as data via a
typeclass `IsManifoldMeasure`, instead of building the manifold
volume form (which would require R10-sub-A,B / R9-bundled volume
form, both ABSENT from Mathlib v4.28.0).  See
`/root/.claude/plans/okay-let-s-plan-out-shimmering-hearth.md`,
Phase 1, "deliberate cheap shortcut".

Mathlib hooks used:
* `Mathlib/Topology/ContinuousMap/CompactlySupported.lean` —
  `HasCompactSupport.of_compactSpace` (every function on a compact
  space has compact support).
* `Mathlib/MeasureTheory/Function/LpSpace/Indicator.lean` —
  `Continuous.memLp_of_hasCompactSupport`.
* `Mathlib/MeasureTheory/Integral/Bochner/Basic.lean` —
  `MeasureTheory.integral_*` lemmas.

This file does **not** complete `SmoothFun M` to `L²(M)`; the
completion lives in `L2Completion.lean` (Phase 1.5) and uses
`MeasureTheory.Lp ℝ 2 μ`.
-/

namespace JacobianChallenge.Analysis.BundledForms

set_option linter.unusedSectionVars false

open scoped Manifold ContDiff NNReal ENNReal
open MeasureTheory

universe u

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
  (M : Type) [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold (modelWithCornersSelf ℝ E) (⊤ : WithTop ℕ∞) M]

/-- **Phase 1.4.**  `IsManifoldMeasure M μ` carries a finite Borel
measure `μ` on `M` against which we build `L²(M)`.  We *do not*
build the manifold volume form here — that requires R10-sub-A,B /
R9 bundled volume form, both ABSENT.  Instead the measure is
provided as data, with a finiteness hypothesis sufficient to make
continuous functions on a compact `M` square-integrable. -/
class IsManifoldMeasure
    [MeasurableSpace M] [BorelSpace M]
    (μ : Measure M) : Prop where
  /-- `μ` is finite: total mass below `∞`. -/
  isFiniteMeasure : IsFiniteMeasure μ

attribute [instance] IsManifoldMeasure.isFiniteMeasure

variable [MeasurableSpace M] [BorelSpace M] [CompactSpace M]
  (μ : Measure M) [IsManifoldMeasure M μ]

/-- A `SmoothFun M` is a continuous (in particular measurable) map
`M → ℝ`.  On a compact `M` it has compact support automatically. -/
theorem SmoothFun.hasCompactSupport (f : SmoothFun (E := E) M) :
    HasCompactSupport (f : M → ℝ) :=
  HasCompactSupport.of_compactSpace _

/-- A `SmoothFun M` is `L^p` for every `p`, in particular `L²`,
on a compact `M` with finite `μ`. -/
theorem SmoothFun.memLp (p : ℝ≥0∞) (f : SmoothFun (E := E) M) :
    MemLp (f : M → ℝ) p μ :=
  Continuous.memLp_of_hasCompactSupport (μ := μ) (p := p)
    (SmoothFun.continuous (E := E) M f)
    (SmoothFun.hasCompactSupport (E := E) M f)

/-- `f * g` is also continuous and hence `L^p` for every `p`. -/
theorem SmoothFun.mul_memLp (p : ℝ≥0∞) (f g : SmoothFun (E := E) M) :
    MemLp ((f : M → ℝ) * (g : M → ℝ)) p μ :=
  Continuous.memLp_of_hasCompactSupport (μ := μ) (p := p)
    ((SmoothFun.continuous (E := E) M f).mul
      (SmoothFun.continuous (E := E) M g))
    (HasCompactSupport.of_compactSpace _)

/-- **Phase 1.4 headline.**  `L2Inner f g := ∫ x, f x * g x ∂μ`
is the `L²` inner product on smooth real-valued functions on a
compact manifold with finite `μ`. -/
noncomputable def L2Inner (f g : SmoothFun (E := E) M) : ℝ :=
  ∫ x, f x * g x ∂μ

/-- `L2Inner` is symmetric: `⟨f, g⟩ = ⟨g, f⟩`. -/
theorem L2Inner_symm (f g : SmoothFun (E := E) M) :
    L2Inner (E := E) M μ f g = L2Inner (E := E) M μ g f := by
  unfold L2Inner
  congr 1
  funext x
  exact mul_comm _ _

/-- `L2Inner` is non-negative on the diagonal: `⟨f, f⟩ ≥ 0`. -/
theorem L2Inner_self_nonneg (f : SmoothFun (E := E) M) :
    0 ≤ L2Inner (E := E) M μ f f := by
  unfold L2Inner
  apply integral_nonneg
  intro x
  exact mul_self_nonneg _

/-- `L2Inner` is bilinear in the first argument: `⟨f₁ + f₂, g⟩ =
⟨f₁, g⟩ + ⟨f₂, g⟩`. -/
theorem L2Inner_add_left (f₁ f₂ g : SmoothFun (E := E) M) :
    L2Inner (E := E) M μ (f₁ + f₂) g =
      L2Inner (E := E) M μ f₁ g + L2Inner (E := E) M μ f₂ g := by
  unfold L2Inner
  rw [← integral_add]
  · congr 1
    funext x
    simp [add_mul]
  · exact ((SmoothFun.mul_memLp (E := E) M μ 1 f₁ g).integrable le_rfl)
  · exact ((SmoothFun.mul_memLp (E := E) M μ 1 f₂ g).integrable le_rfl)

/-- `L2Inner` is bilinear in the first argument: `⟨c • f, g⟩ = c · ⟨f, g⟩`. -/
theorem L2Inner_smul_left (c : ℝ) (f g : SmoothFun (E := E) M) :
    L2Inner (E := E) M μ (c • f) g = c * L2Inner (E := E) M μ f g := by
  unfold L2Inner
  rw [← integral_const_mul]
  congr 1
  funext x
  simp [mul_assoc]

end JacobianChallenge.Analysis.BundledForms
