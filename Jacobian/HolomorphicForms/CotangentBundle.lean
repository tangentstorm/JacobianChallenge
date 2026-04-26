import Mathlib.Analysis.Complex.Basic
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Topology.VectorBundle.Hom
import Mathlib.Topology.VectorBundle.Constructions

/-!
# The cotangent bundle of a complex manifold

Queue C support. Defines `CotangentBundle X` for a complex manifold
`X` modeled on a complex normed space `E`, by composing the existing
Mathlib infrastructure:

- `TangentBundle 𝓘(ℂ, E) X` — the tangent bundle (PRESENT in Mathlib).
- `Bundle.Trivial X ℂ` — the trivial line bundle (PRESENT).
- `Bundle.ContinuousLinearMap` — the bundle of continuous linear maps
  between two vector bundles over the same base (PRESENT in
  `Mathlib/Topology/VectorBundle/Hom.lean`).

The cotangent bundle is `Bundle.ContinuousLinearMap (RingHom.id ℂ)`
applied to the tangent bundle and the trivial line bundle. Its
fiber at `x : X` is `TangentSpace 𝓘(ℂ, E) x →L[ℂ] ℂ`.

`VectorBundle ℂ (E →L[ℂ] ℂ) CotangentSpace` is then automatic via
`Bundle.ContinuousLinearMap.vectorBundle`.
-/

namespace JacobianChallenge.HolomorphicForms

/-- The cotangent space at `x : X`: continuous ℂ-linear functionals on
the tangent space at `x`. The model fiber `E` is exposed as an
explicit argument because Mathlib's `TangentSpace` indexes the model
through the `ModelWithCorners`. -/
abbrev CotangentSpace
    (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E]
    (X : Type*) [TopologicalSpace X] [ChartedSpace E X]
    (x : X) : Type _ :=
  TangentSpace (modelWithCornersSelf ℂ E) x →L[ℂ] (Bundle.Trivial X ℂ) x

/-- Model fiber of the cotangent bundle: `E →L[ℂ] ℂ`. -/
abbrev CotangentModelFiber
    (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E] : Type _ :=
  E →L[ℂ] ℂ

/-- Sanity check: the cotangent space inherits a `VectorBundle` structure
automatically from Mathlib's `Bundle.ContinuousLinearMap.vectorBundle`,
because the tangent bundle and the trivial line bundle are both
vector bundles over `X`. -/
example
    (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E]
    (X : Type*) [TopologicalSpace X] [ChartedSpace E X]
    [IsManifold (modelWithCornersSelf ℂ E) (⊤ : WithTop ℕ∞) X] :
    VectorBundle ℂ (CotangentModelFiber E) (CotangentSpace E X) :=
  inferInstance

end JacobianChallenge.HolomorphicForms
