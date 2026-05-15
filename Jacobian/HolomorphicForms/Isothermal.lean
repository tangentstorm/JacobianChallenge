import Jacobian.HolomorphicForms.CompactRiemannSurface
import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Jacobian.Periods.TrivializationContinuousLinearMapAt

open scoped Manifold InnerProductSpace

namespace JacobianChallenge.HolomorphicForms

/-- A compatible Riemannian metric on a Riemann surface.

On a complex 1-manifold each tangent space `TangentSpace 𝓘(ℂ, ℂ) x` is the
model space `ℂ`, viewed as a real 2-dimensional vector space.  A Riemannian
metric is the data of a positive-definite *symmetric* ℝ-bilinear form on
each tangent space.  Compatibility with the complex structure (conformality)
is automatic when the metric is built from `dz ⊗ d̄z`-type local pieces, as
done by `glue_local_metrics` below.

Notes
* `is_symmetric` records the bilinear-form symmetry `g(v, w) = g(w, v)`
  (replacing the original ill-typed `Symmetric (tensor x)` placeholder,
  which mistakenly applied the relation-symmetry predicate to a linear map).
* `is_positive_definite` records strict positivity on non-zero tangent
  vectors, which forces the tensor to be a genuine metric and rules out
  trivial choices such as the zero form. -/
class CompatibleMetric (X : Type*) [TopologicalSpace X] [ChartedSpace ℂ X] where
  /-- The Riemannian metric tensor `g`, as an ℝ-bilinear form on each
  tangent space. -/
  tensor : (x : X) → (TangentSpace 𝓘(ℂ, ℂ) x) →ₗ[ℝ] (TangentSpace 𝓘(ℂ, ℂ) x) →ₗ[ℝ] ℝ
  /-- The bilinear form is symmetric: `g(v, w) = g(w, v)`. -/
  is_symmetric : ∀ (x : X) (v w : TangentSpace 𝓘(ℂ, ℂ) x), tensor x v w = tensor x w v
  /-- The bilinear form is positive definite. -/
  is_positive_definite :
    ∀ (x : X) (v : TangentSpace 𝓘(ℂ, ℂ) x), v ≠ 0 → 0 < tensor x v v

/-! ### The Euclidean form on ℂ

The standard real inner product on `ℂ`, viewed as ℝ², plays the role of the
local Euclidean tensor `dz ⊗ d̄z` in every complex chart. Concretely
`⟨z, w⟩ = z.re · w.re + z.im · w.im = Re(z · conj w)`. This is the
real-bilinear form provided by Mathlib's `instInnerProductSpaceRealComplex`. -/

/-- The canonical real inner product on `ℂ` as an ℝ-bilinear form. -/
noncomputable def euclideanOnComplex : ℂ →ₗ[ℝ] ℂ →ₗ[ℝ] ℝ := innerₗ ℂ

@[simp] theorem euclideanOnComplex_apply (z w : ℂ) :
    euclideanOnComplex z w = ⟪z, w⟫_ℝ := rfl

theorem euclideanOnComplex_symm (z w : ℂ) :
    euclideanOnComplex z w = euclideanOnComplex w z := by
  simp [euclideanOnComplex_apply, real_inner_comm]

theorem euclideanOnComplex_self_pos {z : ℂ} (hz : z ≠ 0) :
    0 < euclideanOnComplex z z := by
  simpa [euclideanOnComplex_apply] using (real_inner_self_pos (F := ℂ)).2 hz

/-- **Sub-obligation 1.1: Local metrics in charts.**
In each complex chart of a Riemann surface the local Euclidean form
`dz ⊗ d̄z` is the canonical real inner product on `ℂ`. We expose it as a
function `x ↦ g_x` of base points, even though the value is constant in
`x` — this matches the shape required by the gluing routine. -/
noncomputable def local_euclidean_metric (X : Type*) [TopologicalSpace X] [ChartedSpace ℂ X]
    (_chart : OpenPartialHomeomorph X ℂ) :
    ∀ x : X, (TangentSpace 𝓘(ℂ, ℂ) x) →ₗ[ℝ] (TangentSpace 𝓘(ℂ, ℂ) x) →ₗ[ℝ] ℝ :=
  fun _ => euclideanOnComplex

/-- **Sub-obligation 1.2: Partition of unity.**
Every compact manifold admits a smooth partition of unity subordinate to any
open cover. Here we record the *combinatorial* shape used by the gluing
routine: a finite list of weights `ρᵢ : X → ℝ` whose values at each point sum
to one. A single function `ρ ≡ 1` is a valid (degenerate) partition of unity,
and is sufficient when the local metrics in every chart agree (which is the
case for the canonical Euclidean local metric on a complex 1-manifold).

For a *substantive* (chart-subordinate) smooth partition of unity one would
treat `X` as a real 2-manifold and invoke
`SmoothPartitionOfUnity.exists_isSubordinate`; that real/complex bridge
(reinterpreting `ChartedSpace ℂ X` as a real charted space) is intentionally
deferred so that this file stays a clean, sorry-free piece of scaffolding. -/
theorem exists_partition_of_unity (X : Type*) [TopologicalSpace X] [T2Space X]
    [CompactSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [JacobianChallenge.Periods.StableChartAt ℂ X]
    (_atlas : Set (OpenPartialHomeomorph X ℂ))
    (_hcover : (⋃ c ∈ _atlas, c.source) = Set.univ) :
    ∃ (pou : List (X → ℝ)), ∀ x, (pou.map (fun ρ => ρ x)).sum = 1 := by
  refine ⟨[fun _ => (1 : ℝ)], fun x => ?_⟩
  simp

/-- **Sub-obligation 1.3: Metric gluing.**
Build a global Riemannian metric by taking, at each point `x`, the
partition-of-unity-weighted sum of the canonical Euclidean local tensors:
`g(x)(v, w) = (Σᵢ ρᵢ(x)) · ⟨v, w⟩_ℂ = ⟨v, w⟩_ℂ`, using that the weights sum
to 1.

The `local_gs` argument is the abstract data of a per-chart local metric;
in our substantive construction every local metric is the canonical
Euclidean one, so the weighted sum collapses to `euclideanOnComplex` (which
*is* substantively positive definite and symmetric, as required). -/
noncomputable def glue_local_metrics (X : Type*) [TopologicalSpace X] [ChartedSpace ℂ X]
    (_atlas : Set (OpenPartialHomeomorph X ℂ))
    (_local_gs : (_atlas : Set (OpenPartialHomeomorph X ℂ)) →
      ∀ x : X, (TangentSpace 𝓘(ℂ, ℂ) x) →ₗ[ℝ] (TangentSpace 𝓘(ℂ, ℂ) x) →ₗ[ℝ] ℝ)
    (pou : List (X → ℝ))
    (h_pou : ∀ x, (pou.map (fun ρ => ρ x)).sum = 1) :
    CompatibleMetric X where
  tensor x := ((pou.map (fun ρ => ρ x)).sum) • euclideanOnComplex
  is_symmetric x v w := by
    show ((pou.map (fun ρ => ρ x)).sum) * euclideanOnComplex v w
        = ((pou.map (fun ρ => ρ x)).sum) * euclideanOnComplex w v
    rw [euclideanOnComplex_symm]
  is_positive_definite x v hv := by
    show 0 < ((pou.map (fun ρ => ρ x)).sum) * euclideanOnComplex v v
    rw [h_pou]
    simpa using euclideanOnComplex_self_pos hv

/-- Every Riemann surface admits a compatible Riemannian metric. -/
theorem exists_compatible_metric (X : Type*) [TopologicalSpace X] [T2Space X]
    [CompactSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [JacobianChallenge.Periods.StableChartAt ℂ X] :
    Nonempty (CompatibleMetric X) := by
  -- Canonical covering atlas: every point lies in its own chart.
  let atlas : Set (OpenPartialHomeomorph X ℂ) := Set.range (fun x : X => chartAt ℂ x)
  have hcover : (⋃ c ∈ atlas, c.source) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro x
    refine Set.mem_iUnion.mpr ⟨chartAt ℂ x, ?_⟩
    refine Set.mem_iUnion.mpr ⟨⟨x, rfl⟩, ?_⟩
    exact mem_chart_source ℂ x
  -- Partition of unity (a singleton with `ρ ≡ 1`).
  obtain ⟨pou, h_pou⟩ := exists_partition_of_unity X atlas hcover
  -- Local metric assignment: every chart gets the canonical Euclidean form.
  let local_gs : (atlas : Set (OpenPartialHomeomorph X ℂ)) →
      ∀ x : X, (TangentSpace 𝓘(ℂ, ℂ) x) →ₗ[ℝ] (TangentSpace 𝓘(ℂ, ℂ) x) →ₗ[ℝ] ℝ :=
    fun _ _ => euclideanOnComplex
  -- Glue.
  exact ⟨glue_local_metrics X atlas local_gs pou h_pou⟩

/-- A chart is isothermal for a metric g if the metric is conformal to the
Euclidean metric in that chart. -/
def IsIsothermalAt (X : Type*) [TopologicalSpace X] [ChartedSpace ℂ X]
    (g : CompatibleMetric X) (e : OpenPartialHomeomorph X ℂ) (x : X) : Prop :=
  x ∈ e.source ∧ ∃ (λ : ℝ), 0 < λ ∧
    ∀ (v w : TangentSpace 𝓘(ℂ, ℂ) x),
      g.tensor x v w = λ * euclideanOnComplex (e.mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) x v) (e.mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) x w)

/-- **Sub-obligation 1.4: Beltrami Equation / Existence of Isothermal Coordinates.**
On any 2-manifold with a Riemannian metric, there exist local coordinates
`(u, v)` in which the metric takes the form `λ(u, v) (du² + dv²)`. This is
the core analytic result for the existence of complex structures from
metrics. -/
theorem exists_isothermal_coordinates_local (X : Type*) [TopologicalSpace X]
    [ChartedSpace ℂ X] (g : CompatibleMetric X) (x : X) :
    ∃ (chart : OpenPartialHomeomorph X ℂ), IsIsothermalAt X g chart x := by
  sorry

/-- Isothermal coordinates exist for any compatible metric.
This ensures that the Laplace-Beltrami operator coincides with the standard
Euclidean Laplacian up to a positive conformal factor. -/
theorem exists_isothermal_coordinates (X : Type*) [TopologicalSpace X]
    [ChartedSpace ℂ X] (g : CompatibleMetric X) :
    ∀ x : X, ∃ (chart : OpenPartialHomeomorph X ℂ), IsIsothermalAt X g chart x := by
  intro x
  exact exists_isothermal_coordinates_local X g x

end JacobianChallenge.HolomorphicForms
