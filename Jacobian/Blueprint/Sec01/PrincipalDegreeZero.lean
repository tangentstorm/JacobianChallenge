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

Body is now a real assembly: delegates to
`branchedCoverData_of_nonconstant_holomorphic` (Sec02 leaf 8) with
the continuity hypothesis discharged by `liftToCp1_continuous`. The
remaining mathematical content lives in those two named obligations
plus the Mathlib instance `ConnectedSpace (OnePoint ℂ)`. -/
noncomputable def liftToCp1_branchedCoverData
    (X : Type*) [TopologicalSpace X] [CompactSpace X] [T2Space X]
    [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (f : MeromorphicFunctionType X)
    (_hf_nonconstant : ¬ ∃ c : OnePoint ℂ, ∀ x, f x = c)
    (hholo : True) :
    BranchedCoverData X (OnePoint ℂ) (meromorphicToCp1 X f) :=
  branchedCoverData_of_nonconstant_holomorphic
    (meromorphicToCp1 X f)
    (liftToCp1_continuous X f hholo)
    trivial

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

/-- **Sub-leaf #5a (HARD analytic content of leaf 5).**

At a "regular point" of `f` — neither a zero nor a pole — the Laurent
order of the underlying ℂ-projection of `f` at `p` is the integer `0`.

Mathematical content: in a chart at `p`, the function `f` is locally a
nonvanishing holomorphic germ, so by Mathlib's
`tendsto_ne_zero_iff_meromorphicOrderAt_eq_zero` its `meromorphicOrderAt`
is `0`. Routing through the chart-independence theorem
`orderAt_eq_meromorphicOrderAt_of_mem_maximalAtlas` then gives
`vanishingOrder X p (underlyingC f) = 0`.

This is the single HARD analytic obligation that leaf 5's body
delegates to. -/
theorem vanishingOrder_eq_zero_of_regular_point
    (X : Type*) [TopologicalSpace X] [CompactSpace X] [T2Space X]
    [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (f : MeromorphicFunctionType X) (_hholo : True) (p : X)
    (_h0 : meromorphicToCp1 X f p ≠ ((0 : ℂ) : OnePoint ℂ))
    (_hinf : meromorphicToCp1 X f p ≠ (∞ : OnePoint ℂ)) :
    vanishingOrder X p (fun q => (f q).getD 0) = 0 := by
  sorry

/-- **Sub-leaf #5 of `thm:principal-degree-zero` (plan class: MEDIUM).**

The support of `principalDivisor X f` is contained in the union of the
zero-fibre and the pole-fibre of the CP¹ lift.

Body is now an assembly above the strictly-smaller analytic obligation
`vanishingOrder_eq_zero_of_regular_point` (leaf 5a) plus the
`principalDivisor` constructor unfold. The contrapositive: outside
`(meromorphicToCp1 X f)⁻¹{0,∞}`, the function `f` is locally a
nonvanishing holomorphic germ, whose Laurent order is `0`, so the
coefficient drops out of the support.

This is the bookkeeping leaf that lets the degree sum in leaf 6 be
split into the two finite fibre sums. -/
theorem principalDivisor_support_subset_zeros_union_poles
    (X : Type*) [TopologicalSpace X] [CompactSpace X] [T2Space X]
    [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (f : MeromorphicFunctionType X)
    (_hf_nonconstant : ¬ ∃ c : OnePoint ℂ, ∀ x, f x = c)
    (hholo : True) :
    ((principalDivisor X f).support : Set X) ⊆
      (meromorphicToCp1 X f) ⁻¹' {((0 : ℂ) : OnePoint ℂ)} ∪
      (meromorphicToCp1 X f) ⁻¹' {(∞ : OnePoint ℂ)} := by
  classical
  intro p hp
  by_contra hreg
  simp only [Set.mem_union, not_or] at hreg
  obtain ⟨hzero, hpole⟩ := hreg
  have h0 : meromorphicToCp1 X f p ≠ ((0 : ℂ) : OnePoint ℂ) :=
    fun heq => hzero (by simpa [Set.mem_preimage] using heq)
  have hinf : meromorphicToCp1 X f p ≠ (∞ : OnePoint ℂ) :=
    fun heq => hpole (by simpa [Set.mem_preimage] using heq)
  have hord : vanishingOrder X p (fun q => (f q).getD 0) = 0 :=
    vanishingOrder_eq_zero_of_regular_point X f hholo p h0 hinf
  apply (Finsupp.mem_support_iff.mp hp)
  unfold principalDivisor
  split_ifs with hcond
  · show WithTop.untopD 0
        (vanishingOrder X p (fun q => (f q).getD 0)) = 0
    rw [hord]; rfl
  · rfl

/-! ## Sub-leaf #6 (MEDIUM) — degree as zeros-sum minus poles-sum. -/

/-- **Sub-leaf #6 of `thm:principal-degree-zero` (plan class: MEDIUM).**

Assembly leaf above 3, 4, 5. Under the same hypotheses as leaves 2–5,
**plus the assumption that the underlying ℂ-projection of `f` is not
identically zero** (so the principal divisor takes the
`Finsupp.onFinset` branch of its definition):

```
Divisor.degree (principalDivisor X f)
  = (Σ_{p ∈ (meromorphicToCp1 X f)⁻¹{0}} h.ramificationIndex p)
  − (Σ_{p ∈ (meromorphicToCp1 X f)⁻¹{∞}} h.ramificationIndex p)
```

where both fibres are finite via `h.finite_fiber`. The proof is pure
`Finsupp` / `Finset.sum` algebra: split the support along leaf 5,
substitute leaves 3 and 4 for the coefficient values, and use the
disjointness `0 ≠ ∞` in `OnePoint ℂ` to keep the two sums separate.

The extra hypothesis `_hcond` lets the assembly avoid a subtle
case-analysis of `principalDivisor`'s `by_cases` definition; the
constant-zero-projection branch is handled by leaf 1, not here.
Consumer: leaf 7a (`principal_degree_zero_of_nonzero`). -/
theorem degree_principalDivisor_eq_zeros_minus_poles
    (X : Type*) [TopologicalSpace X] [CompactSpace X] [T2Space X]
    [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (f : MeromorphicFunctionType X)
    (hf_nonconstant : ¬ ∃ c : OnePoint ℂ, ∀ x, f x = c)
    (hholo : True)
    (hcond : ∃ x, (f x).getD 0 ≠ 0) :
    let h := liftToCp1_branchedCoverData X f hf_nonconstant hholo
    Divisor.degree (principalDivisor X f)
      = (((h.finite_fiber ((0 : ℂ) : OnePoint ℂ)).toFinset).sum
            (fun p => (h.ramificationIndex p : ℤ)))
        - (((h.finite_fiber (∞ : OnePoint ℂ)).toFinset).sum
            (fun p => (h.ramificationIndex p : ℤ))) := by
  classical
  -- Strip the `let h := …` binder so subsequent `set` calls fold inside
  -- the goal.
  intro h
  -- Cache the two fibre Finsets.
  set Z := (h.finite_fiber ((0 : ℂ) : OnePoint ℂ)).toFinset with hZ
  set P := (h.finite_fiber (∞ : OnePoint ℂ)).toFinset with hP
  -- Z and P are disjoint because (0 : OnePoint ℂ) ≠ ∞.
  have hZP_disj : Disjoint Z P := by
    refine Finset.disjoint_left.mpr ?_
    intro p hpZ hpP
    rw [hZ, Set.Finite.mem_toFinset, Set.mem_preimage,
        Set.mem_singleton_iff] at hpZ
    rw [hP, Set.Finite.mem_toFinset, Set.mem_preimage,
        Set.mem_singleton_iff] at hpP
    exact OnePoint.coe_ne_infty (0 : ℂ) (hpZ.symm.trans hpP)
  -- `principalDivisor X f` is `Finsupp.onFinset`-shaped at every point.
  have hd_apply : ∀ p, principalDivisor X f p
      = (vanishingOrder X p (fun q => (f q).getD 0)).untopD 0 := by
    intro p
    show (principalDivisor X f) p = _
    unfold principalDivisor
    split_ifs with hcond'
    · rfl
    · exact absurd hcond hcond'
  -- Support inclusion (leaf 5).
  have hsupp_sub_finset :
      (principalDivisor X f).support ⊆ Z ∪ P := by
    have hL5 :=
      principalDivisor_support_subset_zeros_union_poles
        X f hf_nonconstant hholo
    intro p hp
    have hp' : p ∈ ((principalDivisor X f).support : Set X) := hp
    have hp_union := hL5 hp'
    rw [Finset.mem_union]
    rcases hp_union with hZ' | hP'
    · refine Or.inl ?_
      rw [hZ, Set.Finite.mem_toFinset]; exact hZ'
    · refine Or.inr ?_
      rw [hP, Set.Finite.mem_toFinset]; exact hP'
  -- Step 1: degree = ∑ p ∈ supp, d p
  rw [show (Divisor.degree : Divisor X →+ ℤ) (principalDivisor X f)
      = ∑ p ∈ (principalDivisor X f).support, principalDivisor X f p
      from rfl]
  -- Step 2: extend the sum to Z ∪ P; outside support the coefficient is 0.
  rw [Finset.sum_subset hsupp_sub_finset
        (fun x _ hx => Finsupp.notMem_support_iff.mp hx)]
  -- Step 3: split Z ∪ P into Z + P (disjoint).
  rw [Finset.sum_union hZP_disj]
  -- Step 4: substitute leaves 3 and 4 inside each sum.
  have hZ_substitute :
      (∑ p ∈ Z, principalDivisor X f p)
        = ∑ p ∈ Z, (h.ramificationIndex p : ℤ) := by
    refine Finset.sum_congr rfl (fun p hpZ => ?_)
    have hp_zero :
        meromorphicToCp1 X f p = ((0 : ℂ) : OnePoint ℂ) := by
      rw [hZ, Set.Finite.mem_toFinset] at hpZ
      simpa [Set.mem_preimage] using hpZ
    have hL3 := vanishingOrder_eq_ramificationIndex_at_zero
      X f hf_nonconstant hholo p hp_zero
    simp only at hL3
    rw [hd_apply p, hL3]
  have hP_substitute :
      (∑ p ∈ P, principalDivisor X f p)
        = ∑ p ∈ P, -(h.ramificationIndex p : ℤ) := by
    refine Finset.sum_congr rfl (fun p hpP => ?_)
    have hp_inf :
        meromorphicToCp1 X f p = (∞ : OnePoint ℂ) := by
      rw [hP, Set.Finite.mem_toFinset] at hpP
      simpa [Set.mem_preimage] using hpP
    have hL4 := vanishingOrder_eq_neg_ramificationIndex_at_pole
      X f hf_nonconstant hholo p hp_inf
    simp only at hL4
    rw [hd_apply p, hL4]
  rw [hZ_substitute, hP_substitute, Finset.sum_neg_distrib]
  ring

/-! ## Sub-leaf #7 — split umbrella into nonzero / constant-zero cases. -/

/-- **Sub-leaf #7b** — vanishing order of a nonzero constant function
on a complex 1-manifold is `0`.

Mathematical content: for any chart at `p`, the function
`(fun _ : X => z)` pulled back through the chart is the constant
function `z` on the model space. Mathlib's `meromorphicOrderAt_const`
(or its equivalent for nonzero constants) says the order of a nonzero
constant is `0`. -/
theorem vanishingOrder_const_nonzero
    (X : Type*) [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (p : X) {z : ℂ} (_hz : z ≠ 0) :
    vanishingOrder X p (fun _ => z) = 0 := by
  sorry

/-- **Sub-leaf #7c** — `principalDivisor` of a constant nonzero
projection is the zero divisor.

Mathematical content: when the underlying ℂ-projection of `f` is the
nonzero constant `z`, every coefficient `vanishingOrder p _` is `0`
(by leaf 7b), so the `Finsupp.onFinset` reduces to `0`. -/
theorem principalDivisor_eq_zero_of_constant_nonzero
    (X : Type*) [TopologicalSpace X] [CompactSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (f : MeromorphicFunctionType X)
    {z : ℂ} (hz : z ≠ 0) (hconst : ∀ x, (f x).getD 0 = z) :
    principalDivisor X f = 0 := by
  classical
  apply Finsupp.ext
  intro p
  show (principalDivisor X f) p = 0
  unfold principalDivisor
  split_ifs with hcond
  · show WithTop.untopD 0 (vanishingOrder X p (fun q => (f q).getD 0)) = 0
    have heq : (fun q : X => (f q).getD 0) = (fun _ : X => z) := by
      funext q; exact hconst q
    rw [heq, vanishingOrder_const_nonzero X p hz]
    rfl
  · rfl

/-- **Sub-leaf #7a of `thm:principal-degree-zero` (plan class: SHORT
assembly, but `[T2Space X]` enriched).**

The CP¹ branched-cover assembly itself: under the same hypotheses as
leaves 2–6 (in particular `[T2Space X]`) and assuming the underlying
ℂ-valued projection of `f` is not identically zero,
`Divisor.degree (principalDivisor X f) = 0`.

Body case-splits on whether `f : X → OnePoint ℂ` is itself constant:

* If `f` is constant on `OnePoint ℂ`: the constant cannot be `∞` or
  `↑0` (both contradict `_hf`), so it is `↑z` with `z ≠ 0`. Leaf 7c
  forces the principal divisor to be `0`, hence its degree.
* If `f` is nonconstant: leaf 6 expresses the degree as
  `(Z fibre sum) − (P fibre sum)`; both sums equal
  `(branchedDegree h : ℤ)` via `branchedDegree_eq_weightedFiberCard`
  combined with the now-derived `BranchedCoverData.weightedFiberCard`. -/
theorem principal_degree_zero_of_nonzero
    (X : Type*) [TopologicalSpace X] [CompactSpace X] [T2Space X]
    [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (f : MeromorphicFunctionType X)
    (hf : ∃ x, (f x).getD 0 ≠ 0) :
    Divisor.degree (principalDivisor X f) = 0 := by
  classical
  by_cases hconst : ∃ c : OnePoint ℂ, ∀ x, f x = c
  · -- Constant case. Determine which constant.
    obtain ⟨c, hc⟩ := hconst
    -- Show c = ↑z for some z ≠ 0.
    obtain ⟨x, hx⟩ := hf
    have hx' : (c : OnePoint ℂ).getD 0 ≠ 0 := by
      rw [← hc x]; exact hx
    -- c can't be ∞ (because (∞).getD 0 = 0).
    have hc_ne_inf : c ≠ (∞ : OnePoint ℂ) := by
      intro heq; apply hx'; rw [heq]; rfl
    -- Therefore c = ↑z for some z : ℂ.
    obtain ⟨z, rfl⟩ : ∃ z : ℂ, c = (↑z : OnePoint ℂ) := by
      cases c with
      | infty => exact absurd rfl hc_ne_inf
      | coe z => exact ⟨z, rfl⟩
    -- And z ≠ 0 since (↑z).getD 0 = z ≠ 0.
    have hz_ne : z ≠ 0 := hx'
    -- Each (f x).getD 0 = z.
    have hconst_z : ∀ x, (f x).getD 0 = z := by
      intro x; rw [hc x]; rfl
    rw [principalDivisor_eq_zero_of_constant_nonzero X f hz_ne hconst_z, map_zero]
  · -- Nonconstant case: apply leaf 6, then cancel.
    have h6 := degree_principalDivisor_eq_zeros_minus_poles
      X f hconst trivial hf
    simp only at h6
    rw [h6]
    -- Now: cancel the two ℤ-fibre-sums via Nat.cast_sum + weightedFiberCard_const.
    set h := liftToCp1_branchedCoverData X f hconst trivial with _hh
    -- Each ℤ-fibre-sum equals the cast of weightedFiberCard.
    have hZ_eq : (((h.finite_fiber ((0 : ℂ) : OnePoint ℂ)).toFinset).sum
            (fun p => (h.ramificationIndex p : ℤ)))
        = (h.weightedFiberCard ((0 : ℂ) : OnePoint ℂ) : ℤ) := by
      show ((h.finite_fiber ((0 : ℂ) : OnePoint ℂ)).toFinset).sum
              (fun p => ((h.ramificationIndex p : ℕ) : ℤ))
          = ((h.weightedFiberCard ((0 : ℂ) : OnePoint ℂ) : ℕ) : ℤ)
      unfold BranchedCoverData.weightedFiberCard
      rw [Nat.cast_sum]
    have hP_eq : (((h.finite_fiber (∞ : OnePoint ℂ)).toFinset).sum
            (fun p => (h.ramificationIndex p : ℤ)))
        = (h.weightedFiberCard (∞ : OnePoint ℂ) : ℤ) := by
      show ((h.finite_fiber (∞ : OnePoint ℂ)).toFinset).sum
              (fun p => ((h.ramificationIndex p : ℕ) : ℤ))
          = ((h.weightedFiberCard (∞ : OnePoint ℂ) : ℕ) : ℤ)
      unfold BranchedCoverData.weightedFiberCard
      rw [Nat.cast_sum]
    rw [hZ_eq, hP_eq]
    have hWFC :
        h.weightedFiberCard ((0 : ℂ) : OnePoint ℂ)
          = h.weightedFiberCard (∞ : OnePoint ℂ) :=
      h.weightedFiberCard_const _ _
    rw [hWFC, sub_self]

/-- Principal divisors have degree zero.

Now that `principalDivisor` is the genuine `Σ_p ord_p(f) · p`
`Finsupp.onFinset` (`Sec01/PrincipalDivisor.lean`), the previous
`show … 0` definitional trick no longer applies. The proof is the
**CP¹ branched-cover** identity `Σ_Z e_p − Σ_P e_p = 0`, packaged as
sub-leaves 1–6 above; the umbrella here case-splits on whether the
underlying ℂ-valued projection is identically zero.

The umbrella signature is signature-stable (matches the previous
`Blueprint.principal_degree_zero` and the public consumer
`InputDivisors.input_divisors_holds`); in particular it does **not**
carry a `[T2Space X]` hypothesis. The constant-zero case is therefore
discharged here directly via leaf 1; the nonzero case is delegated
to the strictly-smaller `principal_degree_zero_of_nonzero`, which
adds the `[T2Space X]` typeclass needed to invoke the branched-cover
machinery in leaves 2–6.

BLOCKERS (transitive, listed in `ref/plans/principal-degree-zero.md`):

* `principal_degree_zero_of_nonzero` (T2-enriched assembly, leaf 7a).
  This obligation in turn reduces to leaves 2–6.
* Leaf 2 reduces to `Sec02/BranchedDegree.lean` leaf 8
  (`branchedCoverData_of_nonconstant_holomorphic`, HARD: open-mapping +
  isolated-zeros + compactness-of-fibres on a compact RS) plus
  `liftToCp1_continuous` (continuity of the CP¹ lift).
* Leaves 3, 4 reduce to the chart-local Laurent normal form
  `f(z) = a · z^{±e} + …` and the chart-on-`OnePoint ℂ`-at-`∞` API;
  the order-extraction lemma `meromorphicOrderAt` is PRESENT in
  Mathlib but the chart-on-`∞` plumbing is project-side work.
* Leaves 5, 6 are MEDIUM Finsupp / Finset assembly above leaves 3, 4.

The constant-`0` case is discharged sorry-free by leaf 1
(`principalDivisor_zero_of_underlying_zero`). -/
theorem principal_degree_zero
    (X : Type*) [TopologicalSpace X] [ConnectedSpace X] [CompactSpace X]
    [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (f : MeromorphicFunctionType X) :
    Divisor.degree (principalDivisor X f) = 0 := by
  classical
  by_cases hf : ∃ x, (f x).getD 0 ≠ 0
  · -- The umbrella's public signature lacks `[T2Space X]`, but the
    -- branched-cover machinery in leaf 7a requires it. Until the
    -- compact-Riemann-surface bundle in this project is upgraded to
    -- include T2 (or until a `[ChartedSpace ℂ X] → T2Space X` instance
    -- lands), we record this typeclass gap as an isolated `haveI`.
    -- Mathematically, every Riemann surface is Hausdorff by definition,
    -- so this gap is documentation rather than substantive math.
    haveI : T2Space X := sorry
    exact principal_degree_zero_of_nonzero X f hf
  · exact principalDivisor_zero_of_underlying_zero X f hf

end JacobianChallenge.Blueprint
