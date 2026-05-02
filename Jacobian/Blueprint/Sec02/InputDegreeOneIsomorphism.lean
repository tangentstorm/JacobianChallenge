import Jacobian.Blueprint.Sec02.BranchedDegree
import Jacobian.Blueprint.Sec02.DegreeOneBijective
import Mathlib.Topology.Homeomorph.Lemmas

/-! # Blueprint stub: `input:degree-one-isomorphism`

Section 2 of `tex/sections/02-holomorphic-forms-and-genus.tex`.

Umbrella theorem: a continuous degree-one branched cover between
compact Hausdorff spaces is a homeomorphism. The classical proof
chain bundled by this umbrella:

1. **Degree-one ⇒ bijective** (`thm:degree-one-bijective`,
   eventually `Blueprint.degree_one_bijective`).
2. **Unramified ⇒ local biholomorphism** (`thm:local-biholo-unramified`,
   eventually `Blueprint.local_biholo_unramified`).
3. **Continuous bijection between compact Hausdorff spaces is a
   homeomorphism** (`thm:compact-bijection-homeo`, dischargable from
   Mathlib's `Continuous.homeoOfEquivCompactToT2`).

The conclusion here is the *topological* part — `Nonempty (X ≃ₜ Y)` —
since stating the analytic upgrade `≃ₘ⟨(modelWithCornersSelf ℂ ℂ), ⊤⟩`
to a biholomorphism requires the project's biholomorphism API, which
is not yet stable. Once that lands, the conclusion can be
strengthened in place. -/

namespace JacobianChallenge.Blueprint

/-- **Umbrella (MEDIUM).** A continuous degree-one branched cover of a
compact Hausdorff space onto a compact Hausdorff target is a
homeomorphism.

The unramified hypothesis forces injectivity (combinatorial leaf 7,
`branchedDegree_one_fiber_unique`), the surjectivity hypothesis closes
bijectivity, and `Continuous.homeoOfEquivCompactToT2` (Mathlib)
upgrades the continuous bijection to a homeomorphism. -/
theorem input_degree_one_isomorphism
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [CompactSpace X] [T2Space Y]
    {f : X → Y} [Nonempty Y] (h : BranchedCoverData X Y f)
    (_hdeg : branchedDegree h = 1)
    (_hsurj : Function.Surjective f)
    (_hcont : Continuous f) :
    Nonempty (X ≃ₜ Y) := by
  have hbij : Function.Bijective f := degree_one_bijective h _hdeg
  exact ⟨Continuous.homeoOfEquivCompactToT2 (f := Equiv.ofBijective f hbij) _hcont⟩

end JacobianChallenge.Blueprint
