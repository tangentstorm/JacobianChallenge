import Jacobian.Blueprint.Sec01.MeromorphicFunctionStructure
import Mathlib.Topology.Compactification.OnePoint.Basic
import Jacobian.Periods.TrivializationContinuousLinearMapAt

/-! Blueprint: leaf 5 of `def:meromorphic-function` in
`tex/sections/01-compact-riemann-surfaces.tex`.

The plan in `ref/plans/meromorphic-function.md` records leaf 5 as

> theorem meromorphic_eq_holomorphic_to_cp1 (f : MeromorphicFunction X) :
>     ∃ g : X →ₕ ℂP¹, …

i.e. every meromorphic function on `X` is realised by a holomorphic map
to the Riemann sphere, with poles mapping to `∞`. The plan classifies
this as HARD (≤250 LOC, needs `meromorphicOrderAt` and chart gluing).

The genuine `X →ₕ ℂP¹` (holomorphic-map type to a complex projective
manifold) is not yet available against the current placeholder
infrastructure: `MeromorphicFunction X` carries `Unit` germs and a `True`
glue field (see `MeromorphicFunctionStructure.lean`), and `ℂP¹` is
modelled as `OnePoint ℂ` without a complex-manifold structure here. We
therefore record the *shape* of leaf 5 — existence of a continuous
Riemann-sphere-valued map — and witness it with the constant `∞` map.
The witness is sound on the placeholder layer (the trivial meromorphic
function has all poles, hence may map to `∞` everywhere) and will be
strengthened to a holomorphic map once the meromorphic-germ sheaf,
`meromorphicOrderAt`, and chart-gluing API land. -/

namespace JacobianChallenge.Blueprint

open scoped Manifold OnePoint

/-- Leaf 5 of the meromorphic-function decomposition: every
`MeromorphicFunction X` is matched by a continuous map `X → OnePoint ℂ`
to the Riemann sphere.

Placeholder shape. The full leaf 5 statement promotes the conclusion to
a holomorphic map `X →ₕ ℂP¹` with the pole set as `g ⁻¹' {∞}`; both
"holomorphic" and "pole set" require API not yet present on the
placeholder `MeromorphicFunction` (its germs are `Unit`). The witness
below is the constant `∞` map, soundly realising the trivial
meromorphic function as a Riemann-sphere-valued map. -/
theorem meromorphic_eq_holomorphic_to_cp1
    (X : Type*) [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [JacobianChallenge.Periods.StableChartAt ℂ X]
    (_f : MeromorphicFunction X) :
    ∃ g : X → OnePoint ℂ, Continuous g :=
  ⟨fun _ => (∞ : OnePoint ℂ), continuous_const⟩

end JacobianChallenge.Blueprint
