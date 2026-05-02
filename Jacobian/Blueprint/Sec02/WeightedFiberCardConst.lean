import Jacobian.Blueprint.Sec02.BranchedDegree
import Jacobian.HolomorphicForms.HolomorphicMap
import Mathlib.Topology.LocallyConstant.Basic

/-! # Blueprint: well-definedness of the branched degree (4-step decomposition)

Section 2 of `tex/sections/02-holomorphic-forms-and-genus.tex`.

This file decomposes the proof of `weightedFiberCard_const` (the
remaining `sorry` in `Sec02/BranchedDegreeFromHolomorphic.lean`) into
four sub-leaves, each stated as a `sorry`-bearing theorem.  Together
they give the well-definedness of the branched degree:

  1. **Branch locus finite** (`mapAnalyticOrderAt_ramified_finite`):
     for a nonconstant holomorphic map between compact preconnected
     complex 1-manifolds, the source-side ramified set
     `{x | mapAnalyticOrderAt f x ≠ 1}` is finite.  Standard proof:
     in each chart, `e_x(f) ≥ 2` is equivalent to vanishing of the
     chart-pulled derivative `(ψ ∘ f ∘ φ⁻¹)'(φ x)`; the derivative is
     itself analytic, so its zero set is discrete by the analytic
     identity principle (`AnalyticAt.eventually_ne` in Mathlib).
     Discrete-in-each-chart + compactness ⇒ finite.

  2. **Local injectivity at unramified points**
     (`IsHolomorphicAt.exists_local_inj_of_unramified`): if
     `mapAnalyticOrderAt f x = 1`, there's an open neighborhood `U`
     of `x` and an open neighborhood `V` of `f x` such that for every
     `y ∈ V`, the set `U ∩ f⁻¹ {y}` is a singleton.  Standard proof:
     order-1 ⇒ chart-local derivative nonzero at chart `x`; Mathlib's
     `AnalyticAt.localInverse` / inverse-function theorem on `ℂ` ⇒
     local biholomorphism; transport back through charts.

  3. **Local k-fold structure at ramified points**
     (`IsHolomorphicAt.exists_local_kfold_of_ramified`): if
     `mapAnalyticOrderAt f x = k` with `k ≥ 1`, there's a neighborhood
     `U` of `x` and a neighborhood `V` of `f x` such that for every
     `y ∈ V` with `y ≠ f x`, the set `U ∩ f⁻¹ {y}` consists of exactly
     `k` distinct unramified preimages.  Standard proof: in suitable
     local chart-coordinates, `f` looks like `t ↦ t^k` near `0`
     (Mathlib's `AnalyticAt.analyticOrderAt_eq_natCast` gives the
     local power-series form `f(t) = t^k · g(t)` with `g(0) ≠ 0`,
     then a holomorphic local change-of-variables flattens `g` to a
     constant).  The map `t ↦ t^k` has exactly `k` simple preimages
     of any nonzero target.

  4. **Local conservation of weighted fibre count**
     (`isHolomorphic_weightedFiberSum_isLocallyConstant`): combining
     leaves 2 and 3, the weighted fibre sum `∑_{x ∈ f⁻¹{y}} e_x(f)`
     is locally constant on `Y`.  Proof: at each `y₀ : Y`, the fibre
     `f⁻¹{y₀}` is finite (by `isHolomorphic_finite_fiber`); choose
     disjoint open neighborhoods of each preimage; each unramified
     preimage contributes `1` to the local count for `y` near `y₀`
     (leaf 2); each ramified preimage of order `k` contributes `k`
     simple preimages (leaf 3) summing to `k` again.  The total
     weighted count at `y` equals the total weighted count at `y₀`.

The final theorem `isHolomorphic_weightedFiberSum_const` follows
from leaf 4 plus `IsLocallyConstant.apply_eq_of_preconnectedSpace`,
and is exactly the field needed to discharge the remaining `sorry`
in `branchedCoverData_of_nonconstant_holomorphic`. -/

namespace JacobianChallenge.Blueprint

open scoped Manifold ContDiff
open Set Filter
open JacobianChallenge.HolomorphicForms.HolomorphicMap

/-- **Sub-leaf 1 (sorry).** For a nonconstant holomorphic map between
compact preconnected complex 1-manifolds, the source-side ramified
set `{x | mapAnalyticOrderAt f x ≠ 1}` is finite.

Proof sketch (≈150 LOC when discharged): order ≠ 1 at `x` is
equivalent to vanishing of the chart-pulled derivative at `chartAt ℂ x x`
(`AnalyticAt.analyticOrderAt_sub_eq_one_of_deriv_ne_zero` characterises
order = 1 by deriv ≠ 0).  The derivative is itself analytic, so its
zero set is discrete (`AnalyticAt.eventually_ne` after the global
identity principle has been used to rule out f globally constant).
Discrete subset of compact ⇒ finite. -/
theorem mapAnalyticOrderAt_ramified_finite
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [ChartedSpace ℂ X] [ChartedSpace ℂ Y]
    [IsManifold 𝓘(ℂ) ω X] [IsManifold 𝓘(ℂ) ω Y]
    [CompactSpace X] [PreconnectedSpace X] [T2Space Y]
    {f : X → Y} (_hf : IsHolomorphic f)
    (_hnonconst : ¬ ∃ y₀ : Y, ∀ x, f x = y₀) :
    {x : X | mapAnalyticOrderAt f x ≠ 1}.Finite := by
  sorry

/-- **Sub-leaf 2 (sorry).** Local injectivity at an unramified point:
if `mapAnalyticOrderAt f x = 1`, there is an open neighborhood `U` of
`x` and an open neighborhood `V` of `f x` such that for every `y ∈ V`,
`U ∩ f⁻¹ {y}` is a singleton.

Proof sketch (≈100 LOC when discharged): order = 1 means the
chart-local power-series expansion is `f(t) = a · t + O(t²)` with
`a ≠ 0`, i.e. `deriv f ≠ 0` at the chart image of `x`.  Apply Mathlib's
analytic inverse function theorem (`AnalyticAt.localInverse` in
`Analysis/Analytic/Inverse.lean`) to get a chart-local inverse on a
neighborhood; transport back through the charts on `X` and `Y`. -/
theorem IsHolomorphicAt.exists_local_inj_of_unramified
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [ChartedSpace ℂ X] [ChartedSpace ℂ Y]
    [IsManifold 𝓘(ℂ) ω X] [IsManifold 𝓘(ℂ) ω Y]
    {f : X → Y} (_hf : IsHolomorphic f) {x : X}
    (_hramx : mapAnalyticOrderAt f x = 1) :
    ∃ U : Set X, IsOpen U ∧ x ∈ U ∧
    ∃ V : Set Y, IsOpen V ∧ f x ∈ V ∧
    ∀ y ∈ V, ∃! x' : X, x' ∈ U ∧ f x' = y := by
  sorry

/-- **Sub-leaf 3 (sorry).** Local `k`-fold structure at a ramified
point: if `mapAnalyticOrderAt f x = k` (with `k ≥ 1`, the typical
case), there is a neighborhood `U` of `x` and a neighborhood `V` of
`f x` such that for every `y ∈ V` with `y ≠ f x`, the set
`U ∩ f⁻¹ {y}` has exactly `k` elements, each unramified.

Proof sketch (≈250 LOC when discharged): Mathlib's
`AnalyticAt.analyticOrderAt_eq_natCast` gives the local power-series
form `f(t) = t^k · g(t)` near `chart x x` with `g(chart x x) ≠ 0`.
A holomorphic `k`-th root of `g` exists locally (composition of
`g` with a `k`-th root branch, which exists since `g(chart x x) ≠ 0`),
producing a holomorphic local change of variables `s = t · h(t)` with
`h(chart x x) ≠ 0` and `f` becoming `s ↦ s^k` in the new coordinate.
The map `s ↦ s^k` has exactly `k` distinct simple preimages of any
nonzero target.  Transport back through charts. -/
theorem IsHolomorphicAt.exists_local_kfold_of_ramified
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [ChartedSpace ℂ X] [ChartedSpace ℂ Y]
    [IsManifold 𝓘(ℂ) ω X] [IsManifold 𝓘(ℂ) ω Y]
    {f : X → Y} (_hf : IsHolomorphic f) {x : X}
    {k : ℕ} (_hk_pos : 0 < k) (_hramx : mapAnalyticOrderAt f x = k) :
    ∃ U : Set X, IsOpen U ∧ x ∈ U ∧
    ∃ V : Set Y, IsOpen V ∧ f x ∈ V ∧
    ∀ y ∈ V, y ≠ f x →
    ∃ s : Finset X, s.card = k ∧ ↑s ⊆ U ∧
      (∀ x' ∈ s, f x' = y ∧ mapAnalyticOrderAt f x' = 1) ∧
      (∀ x' ∈ U, f x' = y → x' ∈ s) := by
  sorry

/-- **Sub-leaf 4 (sorry).** Local conservation: combining leaves 2
and 3, the weighted fibre sum is locally constant on `Y`.

Proof sketch (≈300 LOC when discharged): for each `y₀ : Y`, the fibre
`f⁻¹ {y₀}` is finite (`isHolomorphic_finite_fiber`).  Use `T2Space X`
to choose pairwise-disjoint open neighborhoods `U_x` of each
`x ∈ f⁻¹ {y₀}`, with `U_x` small enough that:

  * if `mapAnalyticOrderAt f x = 1`, leaf 2 applies on `U_x`,
    contributing `1` to `weightedFiberSum y` for `y` in a small
    neighborhood `V_x` of `y₀ = f x`;
  * if `mapAnalyticOrderAt f x = k > 1`, leaf 3 applies on `U_x`,
    contributing `k` to `weightedFiberSum y` for `y` in a small
    neighborhood `V_x` of `y₀ = f x` with `y ≠ y₀`, and `k` again at
    `y₀` itself (the single ramified preimage with weight `k`).

Take `V := ⋂ x ∈ f⁻¹ {y₀}, V_x`; on `V`, the weighted fibre sum at
`y` matches the weighted fibre sum at `y₀`.  Properness of `f` on
compact `X` ensures no preimages of `y` near `y₀` lie outside the
chosen neighborhoods. -/
theorem isHolomorphic_weightedFiberSum_isLocallyConstant
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [ChartedSpace ℂ X] [ChartedSpace ℂ Y]
    [IsManifold 𝓘(ℂ) ω X] [IsManifold 𝓘(ℂ) ω Y]
    [CompactSpace X] [T2Space X] [PreconnectedSpace X] [T2Space Y]
    {f : X → Y} (hf : IsHolomorphic f)
    (hnonconst : ¬ ∃ y₀ : Y, ∀ x, f x = y₀) :
    IsLocallyConstant (fun y : Y =>
      ((isHolomorphic_finite_fiber hf hnonconst y).toFinset).sum
        (mapAnalyticOrderAt f)) := by
  sorry

/-- **Final assembly.** Combining sub-leaf 4 with preconnectedness of
`Y`: the weighted fibre sum is constant on `Y`. -/
theorem isHolomorphic_weightedFiberSum_const
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [ChartedSpace ℂ X] [ChartedSpace ℂ Y]
    [IsManifold 𝓘(ℂ) ω X] [IsManifold 𝓘(ℂ) ω Y]
    [CompactSpace X] [T2Space X] [PreconnectedSpace X]
    [T2Space Y] [PreconnectedSpace Y]
    {f : X → Y} (hf : IsHolomorphic f)
    (hnonconst : ¬ ∃ y₀ : Y, ∀ x, f x = y₀) (y₁ y₂ : Y) :
    ((isHolomorphic_finite_fiber hf hnonconst y₁).toFinset).sum
      (mapAnalyticOrderAt f) =
    ((isHolomorphic_finite_fiber hf hnonconst y₂).toFinset).sum
      (mapAnalyticOrderAt f) :=
  (isHolomorphic_weightedFiberSum_isLocallyConstant hf hnonconst).apply_eq_of_preconnectedSpace
    y₁ y₂

end JacobianChallenge.Blueprint
