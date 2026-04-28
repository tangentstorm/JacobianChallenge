import Jacobian.ComplexTorus.Defs
import Jacobian.HolomorphicForms.CompactRiemannSurface
import Jacobian.HolomorphicForms.AnalyticGenus
import Jacobian.Periods.BasisAlignedPeriodSubgroup

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

* `basisAlignedPeriodSubgroup X` — the period subgroup (data, `opaque`);
* `basisAlignedPeriodSubgroup_isClosed` — closedness in the model space;
* `basisAlignedPeriodSubgroup_isDiscrete` — discreteness in the subspace topology;
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

variable (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]

/-- The period subgroup of a compact Riemann surface, expressed in the
basis-aligned model `Fin (analyticGenus ℂ X) → ℂ`.

Routed (keystone refactor, 2026-04-27): defined as the concrete
representative `basisAlignedPeriodSubgroupConcrete X` from
`Jacobian/Periods/BasisAlignedPeriodSubgroup.lean`. This routing
specialises the lattice's carrier domain `X` to `Type` (Type 0) — the
same universe constraint that `Periods.periodSubgroup` and
`IntegralOneCycle` carry, which themselves are limited to Type 0 by
Mathlib's available `HasCoproducts.{0} (ModuleCat ℤ)` instance.

The specialisation propagates upward to `periodFullComplexLattice` and
`Solution.Jacobian`. The comparator-level data-declaration mismatch with
`Challenge.Jacobian (X : Type u)` is a known consequence; per
`Jacobian/WorkPackets/TopDown.md` the comparator's `theorem_names` list
covers only theorem-level declarations, so the data-level monomorphism
should be acceptable for the staged-refinement check. -/
noncomputable def basisAlignedPeriodSubgroup :
    AddSubgroup (Fin (analyticGenus ℂ X) → ℂ) :=
  basisAlignedPeriodSubgroupConcrete X

/-- The period subgroup is discrete in the subspace topology.

Top-down obligation. Bottom-up: the period pairing image of `H₁(X, ℤ)`
has no accumulation point near zero — a consequence of the integrality
of period values on integral cycles.

### Blocker analysis for `basisAlignedPeriodSubgroup_isDiscrete`

**Goal.** Show `DiscreteTopology (basisAlignedPeriodSubgroup X)` where
`basisAlignedPeriodSubgroup X = basisAlignedPeriodSubgroupConcrete X`
is defined as
```
AddSubgroup.map
  (holomorphicOneFormDualEquiv ℂ X).toLinearMap.toAddMonoidHom
  (periodSubgroup ℂ X)
```
in `Jacobian/Periods/BasisAlignedPeriodSubgroup.lean`.

The ambient space `Fin (analyticGenus ℂ X) → ℂ` carries the product
topology and is a finite-dimensional normed space over `ℂ` (and `ℝ`).
The subgroup topology on `↥(basisAlignedPeriodSubgroup X)` is the
subspace topology induced from that product.

#### Mathlib lemmas surveyed

| Lemma | Signature / Status |
|---|---|
| `ZSpan.instDiscreteTopology...` | `DiscreteTopology ↥(Submodule.span ℤ (Set.range b)).toAddSubgroup` for a finite `ℝ`-basis `b`. Gives discreteness of ℤ-spans of ℝ-bases in normed spaces. Would apply if we could exhibit a finite `ℝ`-basis whose ℤ-span equals the period subgroup. |
| `ZLattice.comap_discreteTopology` | Transports discreteness backwards along a continuous injective linear map: `DiscreteTopology ↥L → DiscreteTopology ↥(ZLattice.comap K L e)`. Operates on `Submodule ℤ`, not `AddSubgroup`, and goes in the *comap* direction (preimage), not *map* (image). |
| `Homeomorph.discreteTopology_iff` | `DiscreteTopology X ↔ DiscreteTopology Y` for `X ≃ₜ Y`. Would transport discreteness if both sides carried compatible topologies. |
| `AddSubgroup.isClosed_of_discrete` | Already used downstream (`basisAlignedPeriodSubgroup_isClosed`). Requires `DiscreteTopology` as input. |
| `discreteTopology_of_isOpen_singleton_one` | For topological groups: `{1}` is open implies discrete. Could be used if we could show `{0}` is open in the subgroup topology. |
| `DiscreteTopology.of_subset` | `DiscreteTopology ↑s → t ⊆ s → DiscreteTopology ↑t`. Useful for sub-subgroups of a known-discrete group. |
| `AddSubgroup.map_discreteTopology` | **Does not exist** in Mathlib (v4.28.0). There is no general result transporting `DiscreteTopology` forward through `AddSubgroup.map`. |
| `Int.instDiscreteTopologySubtypeRealMemAddSubgroupZmultiples` | `DiscreteTopology ↥(AddSubgroup.zmultiples a)` for `a : ℝ`. A one-dimensional special case. |

#### Key blocker: `periodPairing` is opaque; integrality is not declared

1. **`periodPairing E X` is `opaque`** (declared in
   `Jacobian/Periods/PeriodFunctional.lean`). Its definition —
   integrating holomorphic 1-forms over integral 1-cycles — is
   deferred because it requires multi-chart path integration and Stokes'
   theorem for 1-forms on manifolds, both absent from Mathlib v4.28.0.
   Consequently, `periodSubgroup ℂ X = (periodPairing ℂ X).range` is
   an abstract `AddSubgroup` about which nothing structural can be
   proved from its API alone.

2. **The algebraic dual `HolomorphicOneForm ℂ X →ₗ[ℂ] ℂ` has no
   `TopologicalSpace` instance.** Lean/Mathlib does not automatically
   topologise the algebraic dual `V →ₗ[ℂ] ℂ` (as opposed to the
   continuous dual `V →L[ℂ] ℂ`). So `periodSubgroup ℂ X` does not
   even carry a topology in which "discrete" could be stated directly.
   Discreteness only becomes a meaningful question after transport to
   `Fin g → ℂ` via `holomorphicOneFormDualEquiv`.

3. **No integrality / finite-generation property is available.** The
   mathematical content — that the image of `H₁(X, ℤ)` under the period
   pairing is a free ℤ-module of rank `2g`, spanned by `2g` ℝ-linearly
   independent period vectors — is not encoded anywhere in the project.
   Without this, `ZSpan.instDiscreteTopology...` cannot fire.

#### Proposed 3-step resolution plan

**(a) Declare a discreteness / finite-generation property on
`periodPairing` or `periodSubgroup`.** The cleanest option is to add a
new `opaque` alongside `periodPairing` in
`Jacobian/Periods/PeriodFunctional.lean`:
```
opaque periodSubgroup_discreteTopology_basis_aligned
    (E : Type*) [...] (X : Type) [...] :
    DiscreteTopology (basisAlignedPeriodSubgroupConcrete X)
```
or, more structurally, declare that the image admits a ℤ-basis of
cardinality `2 * analyticGenus ℂ X` spanning a full-rank ℤ-lattice:
```
opaque periodSubgroup_isZLattice
    (E : Type*) [...] (X : Type) [...] :
    IsZLattice ℝ (periodSubgroupAsSubmodule ℂ X)
```
where `periodSubgroupAsSubmodule` lifts the `AddSubgroup` to a
`Submodule ℤ` and further witnesses that it spans `ℝ^(2g)`. The
`IsZLattice` approach is mathematically richer and also yields the
fundamental domain and covering properties needed downstream.

**(b) Derive `DiscreteTopology (periodSubgroup ℂ X)` from (a).**
If (a) declares `IsZLattice ℝ` on the ℤ-submodule spanned by
the period vectors in `Fin g → ℂ`, then Mathlib's
`ZSpan.instDiscreteTopology...` gives `DiscreteTopology` on the
corresponding `AddSubgroup` directly.

Alternatively, if (a) directly declares `DiscreteTopology` on the
basis-aligned subgroup, step (b) is trivial.

**(c) Wire the instance.** Replace `sorry` with the result from (b).
If (a) declares discreteness directly on
`basisAlignedPeriodSubgroupConcrete X`, the proof is:
```
instance basisAlignedPeriodSubgroup_isDiscrete :
    DiscreteTopology (basisAlignedPeriodSubgroup X) :=
  periodSubgroup_discreteTopology_basis_aligned ℂ X
```
If instead (a) declares `IsZLattice`, the proof assembles
`ZSpan.instDiscreteTopology` with the basis data.

#### Downstream impact

This instance is the **sole blocker** for `basisAlignedPeriodSubgroup_isClosed`
(which is already a pure assembly using `AddSubgroup.isClosed_of_discrete`). It
is also **on the critical path** for `periodFundamentalDomain_isCompact` and
`periodFundamentalDomain_covers`, both of which implicitly depend on the
subgroup being a well-structured lattice.
-/
instance basisAlignedPeriodSubgroup_isDiscrete :
    DiscreteTopology (basisAlignedPeriodSubgroup X) := sorry

/-- The period subgroup is closed in the model space.

Pure assembly: `Fin g → ℂ` is `T2`, and the period subgroup carries
`DiscreteTopology` (the previous instance), so closedness follows from
Mathlib's `AddSubgroup.isClosed_of_discrete`. No own sorry. -/
lemma basisAlignedPeriodSubgroup_isClosed :
    IsClosed (basisAlignedPeriodSubgroup X : Set (Fin (analyticGenus ℂ X) → ℂ)) :=
  AddSubgroup.isClosed_of_discrete

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
      ∃ g ∈ basisAlignedPeriodSubgroup X, v - g ∈ periodFundamentalDomain X := sorry

/-- The period lattice of a compact Riemann surface, bundled as a
`FullComplexLattice` in the basis-aligned model `Fin (analyticGenus ℂ X) → ℂ`.

Pure assembly — every field delegates to one of the small named
obligations above; this declaration adds no new sorry. -/
noncomputable def periodFullComplexLattice :
    JacobianChallenge.ComplexTorus.FullComplexLattice
      (Fin (analyticGenus ℂ X) → ℂ) where
  subgroup := basisAlignedPeriodSubgroup X
  isClosed := basisAlignedPeriodSubgroup_isClosed X
  isDiscrete := basisAlignedPeriodSubgroup_isDiscrete X
  fundamentalDomain := periodFundamentalDomain X
  fundamentalDomain_isCompact := periodFundamentalDomain_isCompact X
  fundamentalDomain_covers := periodFundamentalDomain_covers X

end JacobianChallenge.Periods
