import Jacobian.ComplexTorus.Defs
import Jacobian.HolomorphicForms.CompactRiemannSurface
import Jacobian.HolomorphicForms.AnalyticGenus

/-!
# Period lattice in the basis-aligned model

This module provides the period lattice of a compact Riemann surface,
transported into the basis-aligned model space `Fin (analyticGenus ℂ X) → ℂ`.

The basis-aligned model is the one used by `Jacobian/Challenge.lean` for the
charted-space and Lie-group instances on `Jacobian X`. Choosing the carrier
this way means the universe and chart-model bridges in
`Jacobian/Solution.lean` collapse to a single `ULift`.

This file owns the named obligations that the top-down `Solution.Jacobian`
definition delegates to. Following the project's preference for
*small* named obligations over a single monolithic helper, the
construction is split into separately named pieces:

* `periodSubgroup X` — the period subgroup (data, `opaque`);
* `periodSubgroup_isClosed` — closedness in the model space;
* `periodSubgroup_isDiscrete` — discreteness in the subspace topology;
* `periodFundamentalDomain X` — a chosen fundamental domain (data);
* `periodFundamentalDomain_isCompact` — compactness;
* `periodFundamentalDomain_covers` — the translates cover the model space;
* `periodFullComplexLattice X` — bundles the above into a
  `FullComplexLattice` with no further sorries of its own.

Each of these is the bottom-up obligation Aristotle (or local proof
work) can attack independently. The bottom-up content is, roughly:
period pairing (integration of holomorphic 1-forms over `H₁(X, ℤ)`) +
basis transport + Riemann bilinear nondegeneracy.
-/

namespace JacobianChallenge.Periods

open scoped Manifold
open JacobianChallenge.HolomorphicForms

variable (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]

/-- The period subgroup of a compact Riemann surface, expressed in the
basis-aligned model `Fin (analyticGenus ℂ X) → ℂ`.

Top-down obligation. Bottom-up: image of `H₁(X, ℤ)` under the period
pairing (integration of a basis of holomorphic 1-forms over a basis of
1-cycles). -/
opaque periodSubgroup : AddSubgroup (Fin (analyticGenus ℂ X) → ℂ)

/-- The period subgroup is closed in the model space.

Top-down obligation. Bottom-up: discreteness of the period image plus
finite-dimensionality. -/
lemma periodSubgroup_isClosed :
    IsClosed (periodSubgroup X : Set (Fin (analyticGenus ℂ X) → ℂ)) := sorry

/-- The period subgroup is discrete in the subspace topology.

Top-down obligation. Bottom-up: the period pairing image of `H₁(X, ℤ)`
has no accumulation point near zero — a consequence of the integrality
of period values on integral cycles. -/
instance periodSubgroup_isDiscrete :
    DiscreteTopology (periodSubgroup X) := sorry

/-- A fundamental domain for the period subgroup, in the basis-aligned model.

Top-down obligation. Bottom-up: explicit construction (e.g. closure of
`ZSpan.fundamentalDomain` against a chosen ℤ-basis of the subgroup). -/
opaque periodFundamentalDomain : Set (Fin (analyticGenus ℂ X) → ℂ)

/-- The fundamental domain is compact.

Top-down obligation. Bottom-up: bounded subset of a finite-dim
ℂ-vector space; bounded ⇒ compact in finite dimensions. -/
lemma periodFundamentalDomain_isCompact :
    IsCompact (periodFundamentalDomain X) := sorry

/-- The fundamental-domain translates cover the model space.

Top-down obligation. Bottom-up: full-rank / Riemann bilinear
nondegeneracy — the period subgroup contains 2g ℝ-linearly independent
vectors in the 2g-dimensional ℝ-vector space underlying
`Fin g → ℂ`. -/
lemma periodFundamentalDomain_covers :
    ∀ v : Fin (analyticGenus ℂ X) → ℂ,
      ∃ g ∈ periodSubgroup X, v - g ∈ periodFundamentalDomain X := sorry

/-- The period lattice of a compact Riemann surface, bundled as a
`FullComplexLattice` in the basis-aligned model `Fin (analyticGenus ℂ X) → ℂ`.

Pure assembly — every field delegates to one of the small named
obligations above; this declaration adds no new sorry. -/
noncomputable def periodFullComplexLattice :
    JacobianChallenge.ComplexTorus.FullComplexLattice
      (Fin (analyticGenus ℂ X) → ℂ) where
  subgroup := periodSubgroup X
  isClosed := periodSubgroup_isClosed X
  isDiscrete := periodSubgroup_isDiscrete X
  fundamentalDomain := periodFundamentalDomain X
  fundamentalDomain_isCompact := periodFundamentalDomain_isCompact X
  fundamentalDomain_covers := periodFundamentalDomain_covers X

end JacobianChallenge.Periods
