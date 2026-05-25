import Mathlib.Geometry.Manifold.VectorBundle.SmoothSection
import Mathlib.Tactic.Abel
import Jacobian.HolomorphicForms.SectionFiberNorm
import Jacobian.HolomorphicForms.SectionSupNorm

/-!
# Metric-space axioms for smooth sections via the sup-norm

This file defines the distance function on smooth sections of a normed vector bundle
over a compact base manifold, and proves the four `MetricSpace` axioms as individual
named lemmas. The distance is defined as the sup-norm of the difference.

This is **Step 3** of the 5-step plan laid out in
`Jacobian/HolomorphicForms/SectionTopologyConstructionRecon.lean` for constructing
the Banach-space data on `HolomorphicOneForm ℂ X`.

## Design note

The `MetricSpace` axioms are exposed as individual lemmas rather than bundled into
a `MetricSpace` instance, to avoid a typeclass diamond when the downstream
`HolomorphicOneFormBanachData` (Step 5) assembles the metric-space structure as a
separate field alongside the norm.

## Main definitions

* `dist` — distance between two smooth sections: `dist σ τ = supNorm (σ - τ)`

## Main results

* `dist_self` — `dist σ σ = 0`
* `dist_comm` — `dist σ τ = dist τ σ`
* `dist_triangle` — `dist σ ρ ≤ dist σ τ + dist τ ρ`
* `eq_of_dist_eq_zero` — `dist σ τ = 0 → σ = τ`
* `dist_eq` — `dist σ τ = supNorm (σ - τ)` (definitional)
-/

namespace JacobianChallenge.HolomorphicForms.SectionMetric

set_option linter.unusedSectionVars false

open Bundle JacobianChallenge.HolomorphicForms.SectionFiberNorm
     JacobianChallenge.HolomorphicForms.SectionSupNorm

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners 𝕜 E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [CompactSpace M]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
variable {V : M → Type*}
variable [TopologicalSpace (TotalSpace F V)]
variable [∀ x, TopologicalSpace (V x)]
variable [FiberBundle F V]
variable [∀ x, NormedAddCommGroup (V x)]
variable [∀ x, NormedSpace 𝕜 (V x)]
variable [VectorBundle 𝕜 F V]

/-- Distance between two smooth sections, defined as the sup-norm of their difference. -/
noncomputable def dist (σ τ : ContMDiffSection I F ⊤ V) : ℝ :=
  supNorm (σ - τ)

omit [CompactSpace M] in
/-- `dist σ σ = 0`: distance from a section to itself is zero. -/
theorem dist_self
    (σ : ContMDiffSection I F ⊤ V) : dist σ σ = 0 := by
  show supNorm (σ - σ) = 0
  rw [sub_self]
  exact supNorm_zero

omit [CompactSpace M] in
/--
`dist σ τ = dist τ σ`: distance is symmetric.

The `_hcompat` hypothesis is included for API compatibility with the other metric
axioms but is not needed for this proof (which only uses `supNorm_neg`).
-/
theorem dist_comm
    (_hcompat : ∀ (σ : ContMDiffSection I F ⊤ V),
      Continuous (ContMDiffSection.fiberNorm σ))
    (σ τ : ContMDiffSection I F ⊤ V) :
    dist σ τ = dist τ σ := by
  show supNorm (σ - τ) = supNorm (τ - σ)
  rw [← neg_sub, supNorm_neg]

/--
Triangle inequality for the section distance.

Uses `σ - ρ = (σ - τ) + (τ - ρ)` and `supNorm_add_le`.
-/
theorem dist_triangle
    (hcompat : ∀ (σ : ContMDiffSection I F ⊤ V),
      Continuous (ContMDiffSection.fiberNorm σ))
    (σ τ ρ : ContMDiffSection I F ⊤ V) :
    dist σ ρ ≤ dist σ τ + dist τ ρ := by
  show supNorm (σ - ρ) ≤ supNorm (σ - τ) + supNorm (τ - ρ)
  have h : σ - ρ = (σ - τ) + (τ - ρ) := by abel
  rw [h]
  exact supNorm_add_le hcompat _ _

/--
If `dist σ τ = 0` then `σ = τ`: the distance separates points.

From `supNorm (σ - τ) = 0` and `supNorm_eq_zero_iff`, we get `σ - τ = 0`,
hence `σ = τ`. Requires `Nonempty M` (needed for `supNorm_eq_zero_iff`).
-/
theorem eq_of_dist_eq_zero [Nonempty M]
    (hcompat : ∀ (σ : ContMDiffSection I F ⊤ V),
      Continuous (ContMDiffSection.fiberNorm σ))
    {σ τ : ContMDiffSection I F ⊤ V}
    (h : dist σ τ = 0) : σ = τ := by
  have h0 : supNorm (σ - τ) = 0 := h
  rw [supNorm_eq_zero_iff hcompat] at h0
  exact sub_eq_zero.mp h0

omit [CompactSpace M] in
/-- `dist σ τ = supNorm (σ - τ)`: the distance agrees with the sup-norm of the difference. -/
theorem dist_eq
    (σ τ : ContMDiffSection I F ⊤ V) :
    dist σ τ = supNorm (σ - τ) := rfl

end JacobianChallenge.HolomorphicForms.SectionMetric
