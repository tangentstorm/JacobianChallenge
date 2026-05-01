import Jacobian.Blueprint.Sec01.PrincipalDivisor
import Jacobian.Blueprint.Sec01.DivisorDegree
import Jacobian.Blueprint.Sec01.MeromorphicToCp1
import Jacobian.Blueprint.Sec02.BranchedDegree

/-! # Blueprint: sub-leaves of `thm:principal-degree-zero`

Section 1 of `tex/sections/01-compact-riemann-surfaces.tex`.

The umbrella theorem `thm:principal-degree-zero` is classified
**DECOMPOSE** in `ref/scope-out.md`. The seven-leaf decomposition is in
`ref/plans/principal-degree-zero.md`; this file gives every leaf a
concrete Lean handle.

The route taken here is the **CP¹ branched-cover route**, not the
residue / argument-principle route. Reason: the residue route depends
transitively on `thm:stokes-on-rs-with-boundary` and on differential-form
integration, both **ABSENT** in pinned Mathlib v4.28.0
(`ref/plans/stokes-on-rs-with-boundary.md`, §2). The branched-cover
route bottoms out on `Sec02/BranchedDegree.lean`'s already-scaffolded
`BranchedCoverData` API and the chart-local Laurent normal form
(present in Mathlib as `meromorphicOrderAt`).

Sub-leaves:

* leaf 1 — `principalDivisor_zero_of_underlying_zero` (SHORT, proved)
* leaf 2 — `liftToCp1_branchedCoverData` (HARD, `sorry`-bearing,
  reduces to Sec02 leaf 8 once the holomorphicity hypothesis is wired)
* leaf 3 — `vanishingOrder_eq_ramificationIndex_at_zero` (HARD,
  `sorry`-bearing, chart-local Laurent normal form)
* leaf 4 — `vanishingOrder_eq_neg_ramificationIndex_at_pole` (HARD,
  `sorry`-bearing, chart-on-`OnePoint ℂ`-at-`∞` normal form)
* leaf 5 — `principalDivisor_support_subset_zeros_union_poles`
  (MEDIUM, `sorry`-bearing)
* leaf 6 — `degree_principalDivisor_eq_zeros_minus_poles` (MEDIUM,
  `sorry`-bearing, Finsupp / fibre algebra above leaves 3, 4, 5)
* leaf 7 — `principal_degree_zero` (the umbrella, SHORT assembly above
  the previous leaves; remains `sorry`-bearing until leaves 1, 2, 6
  land)

Imports are deliberately narrow per integrator policy. -/

namespace JacobianChallenge.Blueprint

open scoped Manifold
open scoped OnePoint

/-! ## Sub-leaf #1 (SHORT) — constant-zero case. -/

/-- **Sub-leaf #1 of `thm:principal-degree-zero` (plan class: SHORT).**

When the underlying ℂ-valued projection of `f` is identically `0` the
`principalDivisor` constructor takes its second `by_cases` branch and
returns the zero divisor; its degree is then `0` definitionally.

This handles the constant-`0` case of the umbrella theorem so the
branched-cover route in leaves 2–7 only has to deal with nonzero
projections. -/
theorem principalDivisor_zero_of_underlying_zero
    (X : Type*) [TopologicalSpace X] [CompactSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (f : MeromorphicFunctionType X)
    (hf : ¬ ∃ x, (f x).getD 0 ≠ 0) :
    Divisor.degree (principalDivisor X f) = 0 := by
  classical
  unfold principalDivisor
  split_ifs with h
  · exact absurd h hf
  · exact map_zero _

/-! ## Sub-leaf #2 (HARD) — branched-cover packaging of the CP¹ lift. -/

/-- **Sub-leaf #2 of `thm:principal-degree-zero` (plan class: HARD).**

A nonzero, nonconstant meromorphic function on a compact Riemann
surface lifts to a holomorphic map `meromorphicToCp1 X f : X → OnePoint ℂ`
(via `def:meromorphic-to-cp1`) which is automatically a branched cover.

The hypothesis `_hholo : True` is a placeholder for "the lift is
holomorphic" while the holomorphic-map predicate on `OnePoint ℂ`
stabilises in this project; the eventual replacement is the same
predicate that feeds `Sec02/BranchedDegree.lean` leaf 8
(`branchedCoverData_of_nonconstant_holomorphic`).

Discharge route: combine `meromorphic_as_cp1_map` (preserves
nonconstancy) with `branchedCoverData_of_nonconstant_holomorphic`. -/
noncomputable def liftToCp1_branchedCoverData
    (X : Type*) [TopologicalSpace X] [CompactSpace X] [T2Space X]
    [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (f : MeromorphicFunctionType X)
    (_hf_nonconstant : ¬ ∃ c : OnePoint ℂ, ∀ x, f x = c)
    (_hholo : True) :
    BranchedCoverData X (OnePoint ℂ) (meromorphicToCp1 X f) := by
  sorry

/-! ## Sub-leaf #3 (HARD) — Laurent order at zeros equals ramification. -/

/-- **Sub-leaf #3 of `thm:principal-degree-zero` (plan class: HARD).**

For a point `p` mapped to `0 ∈ OnePoint ℂ` by the CP¹ lift, the
chart-local Laurent order of the underlying ℂ-valued projection equals
the ramification index of the lift at `p`.

Mathematically: in a chart at `p`, `f(z) = a · z^e + O(z^{e+1})` with
`a ≠ 0` and `e = h.ramificationIndex p`, so `vanishingOrder` reads off
`e` directly.

The `WithTop.untopD 0` projection is well-defined here because at a
zero (not a pole) the `vanishingOrder` is a finite nonnegative integer;
see leaf 5 for the support-side bookkeeping. -/
theorem vanishingOrder_eq_ramificationIndex_at_zero
    (X : Type*) [TopologicalSpace X] [CompactSpace X] [T2Space X]
    [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (f : MeromorphicFunctionType X)
    (hf_nonconstant : ¬ ∃ c : OnePoint ℂ, ∀ x, f x = c)
    (hholo : True)
    (p : X) (_hp : meromorphicToCp1 X f p = ((0 : ℂ) : OnePoint ℂ)) :
    let h := liftToCp1_branchedCoverData X f hf_nonconstant hholo
    (vanishingOrder X p (fun q => (f q).getD 0)).untopD 0
      = (h.ramificationIndex p : ℤ) := by
  sorry

/-! ## Sub-leaf #4 (HARD) — Laurent order at poles equals minus ramification. -/

/-- **Sub-leaf #4 of `thm:principal-degree-zero` (plan class: HARD).**

Symmetric to leaf 3: at a point `p` mapped to `∞ ∈ OnePoint ℂ`, the
chart-local Laurent order of the underlying ℂ-valued projection equals
the negative of the ramification index of the lift at `p`.

The chart on `OnePoint ℂ` at `∞` is `1/w`, so the local normal form for
the lift becomes `f(z) = c · z^{-e} + …` with `c ≠ 0`. The
`WithTop.untopD 0` projection lands on the integer `-e`. -/
theorem vanishingOrder_eq_neg_ramificationIndex_at_pole
    (X : Type*) [TopologicalSpace X] [CompactSpace X] [T2Space X]
    [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (f : MeromorphicFunctionType X)
    (hf_nonconstant : ¬ ∃ c : OnePoint ℂ, ∀ x, f x = c)
    (hholo : True)
    (p : X) (_hp : meromorphicToCp1 X f p = (∞ : OnePoint ℂ)) :
    let h := liftToCp1_branchedCoverData X f hf_nonconstant hholo
    (vanishingOrder X p (fun q => (f q).getD 0)).untopD 0
      = -(h.ramificationIndex p : ℤ) := by
  sorry

/-! ## Sub-leaf #5 (MEDIUM) — support of the principal divisor. -/

/-- **Sub-leaf #5 of `thm:principal-degree-zero` (plan class: MEDIUM).**

The support of `principalDivisor X f` is contained in the union of the
zero-fibre and the pole-fibre of the CP¹ lift.

Equivalently: outside `(meromorphicToCp1 X f)⁻¹{0,∞}`, the function `f`
is locally a nonvanishing holomorphic germ, whose Laurent order in any
chart is `0`, so `vanishingOrder ... = 0` at every such point and the
`Finsupp.onFinset` constructor leaves the coefficient at `0`.

This is the bookkeeping leaf that lets the degree sum in leaf 6 be
split into the two finite fibre sums. -/
theorem principalDivisor_support_subset_zeros_union_poles
    (X : Type*) [TopologicalSpace X] [CompactSpace X] [T2Space X]
    [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (f : MeromorphicFunctionType X)
    (_hf_nonconstant : ¬ ∃ c : OnePoint ℂ, ∀ x, f x = c)
    (_hholo : True) :
    ((principalDivisor X f).support : Set X) ⊆
      (meromorphicToCp1 X f) ⁻¹' {((0 : ℂ) : OnePoint ℂ)} ∪
      (meromorphicToCp1 X f) ⁻¹' {(∞ : OnePoint ℂ)} := by
  sorry

/-! ## Sub-leaf #6 (MEDIUM) — degree as zeros-sum minus poles-sum. -/

/-- **Sub-leaf #6 of `thm:principal-degree-zero` (plan class: MEDIUM).**

Assembly leaf above 3, 4, 5. Under the same hypotheses as leaves 2–5,

```
Divisor.degree (principalDivisor X f)
  = (Σ_{p ∈ (meromorphicToCp1 X f)⁻¹{0}} h.ramificationIndex p)
  − (Σ_{p ∈ (meromorphicToCp1 X f)⁻¹{∞}} h.ramificationIndex p)
```

where both fibres are finite via `h.finite_fiber`. The proof is pure
`Finsupp` / `Finset.sum` algebra: split the support along leaf 5,
substitute leaves 3 and 4 for the coefficient values, and use the
disjointness `0 ≠ ∞` in `OnePoint ℂ` to keep the two sums separate. -/
theorem degree_principalDivisor_eq_zeros_minus_poles
    (X : Type*) [TopologicalSpace X] [CompactSpace X] [T2Space X]
    [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (f : MeromorphicFunctionType X)
    (hf_nonconstant : ¬ ∃ c : OnePoint ℂ, ∀ x, f x = c)
    (hholo : True) :
    let h := liftToCp1_branchedCoverData X f hf_nonconstant hholo
    Divisor.degree (principalDivisor X f)
      = (((h.finite_fiber ((0 : ℂ) : OnePoint ℂ)).toFinset).sum
            (fun p => (h.ramificationIndex p : ℤ)))
        - (((h.finite_fiber (∞ : OnePoint ℂ)).toFinset).sum
            (fun p => (h.ramificationIndex p : ℤ))) := by
  sorry

/-! ## Sub-leaf #7 (SHORT) — the umbrella `principal_degree_zero`. -/

/-- Principal divisors have degree zero.

Now that `principalDivisor` is the genuine `Σ_p ord_p(f) · p`
`Finsupp.onFinset` (`Sec01/PrincipalDivisor.lean`), the previous
`show … 0` definitional trick no longer applies. The proof is the
**CP¹ branched-cover** identity `Σ_Z e_p − Σ_P e_p = 0`, packaged as
sub-leaves 1–6 above; the final step rewrites each fibre sum as
`(branchedDegree h : ℤ)` via `branchedDegree_eq_weightedFiberCard` and
cancels.

BLOCKERS (transitive, listed in `ref/plans/principal-degree-zero.md`):

* Leaf 2 reduces to `Sec02/BranchedDegree.lean` leaf 8
  (`branchedCoverData_of_nonconstant_holomorphic`, HARD: open-mapping +
  isolated-zeros + compactness-of-fibres on a compact RS).
* Leaves 3, 4 reduce to the chart-local Laurent normal form
  `f(z) = a · z^{±e} + …` and the chart-on-`OnePoint ℂ`-at-`∞` API;
  the order-extraction lemma `meromorphicOrderAt` is PRESENT in
  Mathlib but the chart-on-`∞` plumbing is project-side work.
* Leaves 5, 6 are MEDIUM Finsupp / Finset assembly above leaves 3, 4.

The umbrella body remains `sorry` until leaves 2 + 6 land. The
constant-`0` case in the assembly is discharged by leaf 1. -/
theorem principal_degree_zero
    (X : Type*) [TopologicalSpace X] [ConnectedSpace X] [CompactSpace X]
    [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (f : MeromorphicFunctionType X) :
    Divisor.degree (principalDivisor X f) = 0 := by
  sorry

end JacobianChallenge.Blueprint
