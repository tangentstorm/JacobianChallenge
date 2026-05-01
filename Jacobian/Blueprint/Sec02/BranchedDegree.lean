import Mathlib.Data.Set.Finite.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Topology.Connected.Basic

/-! # Blueprint: `def:branched-degree` (TRIVIAL/SHORT/MEDIUM/HARD leaves)

Section 2 of `tex/sections/02-holomorphic-forms-and-genus.tex`.

Concrete (proof-bearing where TRIVIAL/SHORT, `sorry`-bearing where
MEDIUM/HARD) realisations of the eight sub-leaves catalogued in the
ChatGPT plan `ref/plans/branched-degree.md`:

* leaf 1 — `ramificationIndexStub` (TRIVIAL, proved)
* leaf 2 — `BranchedCoverData` (SHORT, structure)
* leaf 3 — `branchedDegree` (SHORT, proved)
* leaf 4 — `branchedDegree_eq_weightedFiberCard` (SHORT, proved)
* leaf 5 — `branchedDegree_pos` (MEDIUM, `sorry`)
* leaf 6 — `branchedDegree_eq_card_toFinset_of_unramified_fiber`
  (MEDIUM, `sorry`)
* leaf 7 — `branchedDegree_one_fiber_unique` (HARD, `sorry`)
* leaf 8 — `branchedCoverData_of_nonconstant_holomorphic` (HARD,
  `sorry`)

Imports are narrow (no `import Mathlib`): `Set.Finite` /
`Set.Finite.toFinset`, `Finset.sum` and `Finset.card`, and the
`TopologicalSpace` / `ConnectedSpace` typeclasses needed for the
constancy-on-connected-target story.

Downstream nodes (degree-one bijection, Riemann-Hurwitz, push-pull)
should depend on `branchedDegree_eq_weightedFiberCard` and
`branchedDegree_one_fiber_unique`, **not** on the unfolded
`Classical.arbitrary` choice. The analytic constructor (leaf 8) is
where the open-mapping theorem and isolated-zeros enter the project. -/

namespace JacobianChallenge.Blueprint

/-- **Plan leaf 1 (TRIVIAL).** Temporary placeholder for the local
ramification / mapping multiplicity `e_x(f)` of a holomorphic map
between Riemann surfaces. Constant `1` lets the degree-one chain
typecheck before the analytic order-of-vanishing definition lands; the
final replacement reads the local power-series order
`w ∘ f ∘ z⁻¹ (t) = a · tᵉ + O(tᵉ⁺¹)` and lives in the analytic frontier
file. -/
noncomputable def ramificationIndexStub
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (_f : X → Y) (_x : X) : ℕ := 1

/-- **Plan leaf 2 (SHORT).** Packaged data for a branched cover
`f : X → Y`: the local ramification indices, finiteness of every fibre,
and the constancy theorem for the weighted fibre count. Bundling the
constancy hypothesis as a structure field is the load-bearing trick
that lets `branchedDegree` exist before the analytic open-mapping
theorem is in place. -/
structure BranchedCoverData
    (X Y : Type*) [TopologicalSpace X] [TopologicalSpace Y]
    (f : X → Y) where
  /-- Local ramification / mapping multiplicity at each point. -/
  ramificationIndex : X → ℕ
  /-- Multiplicities are positive. -/
  ramificationIndex_pos : ∀ x, 0 < ramificationIndex x
  /-- Every fibre is finite (a deep fact for nonconstant holomorphic
  maps between compact Riemann surfaces). -/
  finite_fiber : ∀ y : Y, (f ⁻¹' {y}).Finite
  /-- Weighted cardinality of the fibre over `y`: sum of ramification
  indices of all preimages of `y`. -/
  weightedFiberCard : Y → ℕ := fun y =>
    ((finite_fiber y).toFinset).sum ramificationIndex
  /-- The weighted fibre count is constant on `Y` (the genuinely
  nontrivial part of the definition). -/
  weightedFiberCard_const :
    ∀ y₁ y₂ : Y, weightedFiberCard y₁ = weightedFiberCard y₂

/-- **Plan leaf 3 (SHORT).** The branched degree of a packaged cover:
the weighted fibre cardinality at any base point. We pick the base
point via `Classical.arbitrary`; independence of the choice is
expressed by `branchedDegree_eq_weightedFiberCard`. -/
noncomputable def branchedDegree
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {f : X → Y} [Nonempty Y] (h : BranchedCoverData X Y f) : ℕ :=
  h.weightedFiberCard (Classical.arbitrary Y)

/-- **Plan leaf 4 (SHORT).** Main downstream rewrite: `branchedDegree`
agrees with the weighted fibre count at **any** chosen base point
`y : Y`. Direct corollary of `weightedFiberCard_const`. -/
theorem branchedDegree_eq_weightedFiberCard
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {f : X → Y} [Nonempty Y] (h : BranchedCoverData X Y f) (y : Y) :
    branchedDegree h = h.weightedFiberCard y := by
  unfold branchedDegree
  exact h.weightedFiberCard_const _ y

/-- **Plan leaf 5 (MEDIUM).** Surjective covers have positive degree:
pick any `y : Y`, pick a preimage `x` over `y`, observe
`ramificationIndex x ≥ 1` is a positive summand in the finite
weighted-fibre sum.

Proof outline (≈70 LOC when discharged): reduce via
`branchedDegree_eq_weightedFiberCard` to showing the weighted fibre
sum at a chosen `y` is positive; surjectivity gives a witness `x` in
the fibre; positivity of the ramification index makes the corresponding
summand strictly positive; conclude with `Finset.sum_pos`. -/
theorem branchedDegree_pos
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {f : X → Y} [Nonempty Y] (h : BranchedCoverData X Y f)
    (_hsurj : Function.Surjective f) :
    0 < branchedDegree h := by
  sorry

/-- **Plan leaf 6 (MEDIUM).** On a fibre with no ramification, the
branched degree equals the (finite) cardinality of the fibre. We state
the fibre cardinality via `(h.finite_fiber y).toFinset.card` so the
file remains free of `Nat.card`/`SetTheory.Cardinal` imports.

Proof outline (≈80 LOC when discharged): rewrite via
`branchedDegree_eq_weightedFiberCard h y`, replace each summand
`ramificationIndex x` (for `x` in the fibre `Finset`) by `1` using
`hunram`, then `Finset.sum_const` and `Nat.smul_one_eq_cast`-style
plumbing. -/
theorem branchedDegree_eq_card_toFinset_of_unramified_fiber
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {f : X → Y} [Nonempty Y] (h : BranchedCoverData X Y f) (y : Y)
    (_hunram : ∀ x ∈ f ⁻¹' {y}, h.ramificationIndex x = 1) :
    branchedDegree h = (h.finite_fiber y).toFinset.card := by
  sorry

/-- **Plan leaf 7 (HARD).** A degree-one branched cover has a unique
preimage of every base point, and that preimage is unramified. The
combinatorial heart of the degree-one ⇒ bijective chain.

Proof outline (≈120-180 LOC when discharged): use
`branchedDegree_eq_weightedFiberCard` to reduce to the weighted fibre
sum at `y`; a sum of positive naturals equal to `1` forces a singleton
support and the unique summand to be `1`; convert back to
`f ⁻¹' {y}`. The `∃!` packaging combines existence (a witness in the
fibre) with uniqueness (any two preimages collapse). -/
theorem branchedDegree_one_fiber_unique
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {f : X → Y} [Nonempty Y] (h : BranchedCoverData X Y f) (y : Y)
    (_hdeg : branchedDegree h = 1) :
    ∃! x : X, f x = y ∧ h.ramificationIndex x = 1 := by
  sorry

/-- **Plan leaf 8 (HARD).** Analytic constructor for
`BranchedCoverData`: a nonconstant continuous map `f : X → Y` between
a compact Hausdorff `X` and a connected `Y` (the topological skeleton
of the analytic hypothesis) can be packaged as a branched-cover datum.

The eventual proof requires the open-mapping theorem for analytic maps
(absent in Mathlib v4.28.0), the isolated-zeros theorem, and a local
normal-form lemma — all of which live in the analytic frontier.
Stated here so downstream code can refer to it; the `sorry` is the
single biggest analytic gap in the branched-degree story.

The `_hf` hypothesis is intentionally a `True` placeholder: we leave
the precise analytic hypothesis (nonconstant holomorphic) to be
sharpened once the holomorphic-map predicate stabilises in the
project. -/
noncomputable def branchedCoverData_of_nonconstant_holomorphic
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [CompactSpace X] [T2Space X] [ConnectedSpace Y]
    (f : X → Y) (_hcont : Continuous f) (_hf : True) :
    BranchedCoverData X Y f := by
  sorry

end JacobianChallenge.Blueprint
