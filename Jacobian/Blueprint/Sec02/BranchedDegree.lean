/-! # Blueprint stubs: `def:branched-degree` (TRIVIAL/SHORT leaves)

Section 2 of `tex/sections/02-holomorphic-forms-and-genus.tex`.

Pure placeholder declarations for the sub-leaves of the branched-degree
plan that the ChatGPT decomposition (`ref/plans/branched-degree.md`)
classified as **TRIVIAL** or **SHORT**:

* leaf 1 — `ramificationIndexStub` (TRIVIAL),
* leaf 2 — `BranchedCoverData` packaged interface (SHORT),
* leaf 3 — `branchedDegree` definition (SHORT),
* leaf 4 — `branchedDegree_eq_weightedFiberCard` rewrite (SHORT).

Each declaration here is a **named handle only**: `def`s return `Unit`
and `theorem`s conclude `True`. The real signatures and proofs are
deferred to a follow-up branch that wires in the analytic
infrastructure (`Set.Finite`, `Finset.sum`, `Classical.arbitrary`,
covering / connectedness tools). The placeholders make every blueprint
dep-graph node "pick-up-able": a contributor can `\lean{...}` the
matching name now, and the body can be replaced with the real
construction without renaming.

MEDIUM/HARD leaves of the plan (positivity, unramified-fiber
cardinality, degree-one unique fiber, analytic constructor) are
deliberately **not** stubbed here; they belong to dedicated worker
files once the API surface above stabilises.

Imports: this file is intentionally Mathlib-free. The downstream
replacement file will import the narrow Mathlib pieces listed in the
plan (`Mathlib.Data.Set.Finite.Basic`, `Mathlib.Data.Finset.Basic`,
`Mathlib.Topology.Connected.Basic`) once the real signatures land. -/

namespace JacobianChallenge.Blueprint

/-- **Plan leaf 1 (TRIVIAL).** Placeholder handle for the local
ramification / mapping multiplicity `e_x(f)` of a holomorphic map
between Riemann surfaces at a point.

Replacement target:
`noncomputable def ramificationIndexStub`
`    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]`
`    (f : X → Y) (x : X) : ℕ := 1`

The temporary `ℕ`-valued constant `1` lets the degree-one chain compile
before the analytic order-of-vanishing definition exists; the final
replacement will read the local power-series order
`w ∘ f ∘ z⁻¹ (t) = a · tᵉ + O(tᵉ⁺¹)`. -/
def ramificationIndexStub : Unit := ()

/-- **Plan leaf 2 (SHORT).** Placeholder handle for the packaged
branched-cover data structure that bundles ramification indices, finite
fibers, and the constancy theorem for the weighted fiber count.

Replacement target:
`structure BranchedCoverData`
`    (X Y : Type*) [TopologicalSpace X] [TopologicalSpace Y] (f : X → Y) where`
`  ramificationIndex : X → ℕ`
`  ramificationIndex_pos : ∀ x, 0 < ramificationIndex x`
`  finite_fiber : ∀ y : Y, Set.Finite (f ⁻¹' {y})`
`  weightedFiberCard : Y → ℕ := fun y =>`
`    Finset.sum ((finite_fiber y).toFinset) ramificationIndex`
`  weightedFiberCard_const :`
`    ∀ y₁ y₂ : Y, weightedFiberCard y₁ = weightedFiberCard y₂`

Packaging the constancy theorem as a structure field isolates the
blueprint API from the hard analytic proof (open mapping + connected
target), which is deferred to leaf 8. -/
def BranchedCoverData : Unit := ()

/-- **Plan leaf 3 (SHORT).** Placeholder handle for the branched degree
of a packaged cover: the weighted fiber cardinality at any base point.

Replacement target:
`noncomputable def branchedDegree`
`    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]`
`    {f : X → Y} (h : BranchedCoverData X Y f) : ℕ :=`
`  h.weightedFiberCard Classical.arbitrary`

Independence of the choice of base point is delivered by leaf 4 below,
which rewrites against an arbitrary `y : Y`. -/
def branchedDegree : Unit := ()

/-- **Plan leaf 4 (SHORT).** Placeholder handle for the main downstream
rewrite theorem: `branchedDegree h` equals the weighted fiber count at
**any** chosen `y : Y`.

Replacement target:
`theorem branchedDegree_eq_weightedFiberCard`
`    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]`
`    {f : X → Y} (h : BranchedCoverData X Y f) (y : Y) :`
`    branchedDegree h = h.weightedFiberCard y`

Proof sketch: unfold `branchedDegree`, then apply
`h.weightedFiberCard_const`. This lemma is the rewrite handle every
downstream node (degree-one bijection, Riemann-Hurwitz, push-pull) will
use to talk about a *specific* fiber rather than the abstract
`Classical.arbitrary` choice. -/
theorem branchedDegree_eq_weightedFiberCard : True := trivial

end JacobianChallenge.Blueprint
