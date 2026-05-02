import Mathlib.Data.Set.Finite.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
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
* leaf 5 — `branchedDegree_pos` (MEDIUM, proved)
* leaf 6 — `branchedDegree_eq_card_toFinset_of_unramified_fiber`
  (MEDIUM, proved)
* leaf 7 — `branchedDegree_one_fiber_unique` (HARD, proved via
  `branchedDegree_one_fiber_singleton`)
* leaf 8 — `branchedCoverData_of_nonconstant_holomorphic` lives in a
  separate file `Jacobian/Blueprint/Sec02/BranchedDegreeFromHolomorphic.lean`
  so this file remains free of manifold imports.

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
  /-- `weightedFiberCard` agrees with the explicit fibre sum.  When the
  default value of `weightedFiberCard` is used this is `fun _ => rfl`;
  the field is exposed so that downstream consumers can reason about
  the explicit sum without unfolding `weightedFiberCard`. -/
  weightedFiberCard_eq :
    ∀ y, weightedFiberCard y = ((finite_fiber y).toFinset).sum ramificationIndex
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
weighted-fibre sum. -/
theorem branchedDegree_pos
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {f : X → Y} [Nonempty Y] (h : BranchedCoverData X Y f)
    (hsurj : Function.Surjective f) :
    0 < branchedDegree h := by
  set y : Y := Classical.arbitrary Y with hy
  rw [branchedDegree_eq_weightedFiberCard h y, h.weightedFiberCard_eq]
  obtain ⟨x, hx⟩ := hsurj y
  refine Finset.sum_pos (fun z _ => h.ramificationIndex_pos z) ⟨x, ?_⟩
  rw [Set.Finite.mem_toFinset]
  exact hx

/-- **Plan leaf 6 (MEDIUM).** On a fibre with no ramification, the
branched degree equals the (finite) cardinality of the fibre. We state
the fibre cardinality via `(h.finite_fiber y).toFinset.card` so the
file remains free of `Nat.card`/`SetTheory.Cardinal` imports. -/
theorem branchedDegree_eq_card_toFinset_of_unramified_fiber
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {f : X → Y} [Nonempty Y] (h : BranchedCoverData X Y f) (y : Y)
    (hunram : ∀ x ∈ f ⁻¹' {y}, h.ramificationIndex x = 1) :
    branchedDegree h = (h.finite_fiber y).toFinset.card := by
  rw [branchedDegree_eq_weightedFiberCard h y, h.weightedFiberCard_eq]
  have hcongr : ((h.finite_fiber y).toFinset).sum h.ramificationIndex
      = ((h.finite_fiber y).toFinset).sum (fun _ : X => (1 : ℕ)) := by
    refine Finset.sum_congr rfl (fun x hx => ?_)
    rw [Set.Finite.mem_toFinset] at hx
    exact hunram x hx
  rw [hcongr]
  simp

/-- Helper for leaf 7: when `branchedDegree h = 1`, the fibre `Finset`
over any `y : Y` is a singleton `{x}` and the unique element has
ramification index `1`.  This is the load-bearing combinatorial fact
behind both `branchedDegree_one_fiber_unique` and the downstream
`degree_one_bijective`. -/
theorem branchedDegree_one_fiber_singleton
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {f : X → Y} [Nonempty Y] (h : BranchedCoverData X Y f) (y : Y)
    (hdeg : branchedDegree h = 1) :
    ∃ x, (h.finite_fiber y).toFinset = {x} ∧ h.ramificationIndex x = 1 := by
  have hsum : ((h.finite_fiber y).toFinset).sum h.ramificationIndex = 1 := by
    rw [← h.weightedFiberCard_eq, ← branchedDegree_eq_weightedFiberCard h y]
    exact hdeg
  set s := (h.finite_fiber y).toFinset with hs
  have hcard_le_sum : s.card ≤ s.sum h.ramificationIndex := by
    have hconst : s.card = s.sum (fun _ : X => (1 : ℕ)) := by simp
    rw [hconst]
    exact Finset.sum_le_sum (fun x _ => h.ramificationIndex_pos x)
  rw [hsum] at hcard_le_sum
  have hne : s.Nonempty := by
    by_contra hempty
    rw [Finset.not_nonempty_iff_eq_empty] at hempty
    rw [hempty, Finset.sum_empty] at hsum
    exact zero_ne_one hsum
  have hcard : s.card = 1 :=
    le_antisymm hcard_le_sum hne.card_pos
  rw [Finset.card_eq_one] at hcard
  obtain ⟨x, hx⟩ := hcard
  refine ⟨x, hx, ?_⟩
  rw [hx, Finset.sum_singleton] at hsum
  exact hsum

/-- **Plan leaf 7 (HARD).** A degree-one branched cover has a unique
preimage of every base point, and that preimage is unramified. The
combinatorial heart of the degree-one ⇒ bijective chain. -/
theorem branchedDegree_one_fiber_unique
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {f : X → Y} [Nonempty Y] (h : BranchedCoverData X Y f) (y : Y)
    (hdeg : branchedDegree h = 1) :
    ∃! x : X, f x = y ∧ h.ramificationIndex x = 1 := by
  obtain ⟨x, hxs, hrx⟩ := branchedDegree_one_fiber_singleton h y hdeg
  have hx_mem : x ∈ (h.finite_fiber y).toFinset := by
    rw [hxs]; exact Finset.mem_singleton_self x
  rw [Set.Finite.mem_toFinset] at hx_mem
  refine ⟨x, ⟨hx_mem, hrx⟩, ?_⟩
  rintro x' ⟨hfx', _⟩
  have hx'_mem : x' ∈ (h.finite_fiber y).toFinset := by
    rw [Set.Finite.mem_toFinset]; exact hfx'
  rw [hxs, Finset.mem_singleton] at hx'_mem
  exact hx'_mem

end JacobianChallenge.Blueprint
