import Jacobian.Blueprint.Sec01.PrincipalDivisor
import Jacobian.Blueprint.Sec01.DivisorDegree
import Jacobian.Blueprint.Sec01.MeromorphicToCp1
import Jacobian.Blueprint.Sec02.BranchedDegree
import Jacobian.Blueprint.Sec02.BranchedDegreeFromHolomorphic

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
* leaf 2 — `liftToCp1_branchedCoverData` (HARD assembly, proved
  relative to the named `liftToCp1_isHolomorphic` obligation)
* leaf 3 — `vanishingOrder_eq_ramificationIndex_at_zero` (HARD wrapper,
  proved relative to `vanishingOrder_eq_mapAnalyticOrderAt_at_zero`)
* leaf 4 — `vanishingOrder_eq_neg_ramificationIndex_at_pole` (HARD
  wrapper, proved relative to `vanishingOrder_eq_neg_mapAnalyticOrderAt_at_pole`)
* leaf 5 — `principalDivisor_support_subset_zeros_union_poles`
  (MEDIUM assembly, proved relative to leaf 5a)
* leaf 6 — `degree_principalDivisor_eq_zeros_minus_poles` (MEDIUM
  Finsupp / fibre algebra assembly above leaves 3, 4, 5, proved)
* leaf 7 — `principal_degree_zero` (SHORT umbrella assembly, proved)

Imports are deliberately narrow per integrator policy. -/

namespace JacobianChallenge.Blueprint

open scoped Manifold
open scoped OnePoint
open scoped Topology
open Filter
open JacobianChallenge.HolomorphicForms.VanishingOrder
open JacobianChallenge.HolomorphicForms.HolomorphicMap

/-! ## Sub-leaf #1 (SHORT) — constant-zero case. -/

/-- **Sub-leaf #1 of `thm:principal-degree-zero` (plan class: SHORT).**

When the discriminant of `principalDivisor`'s `by_cases` is false —
either the projection fails to be meromorphic at some point, or its
Laurent order is `⊤` everywhere (i.e. the projection is identically
zero on a punctured neighbourhood of every point) — the constructor
takes its `else` branch and returns the zero divisor; its degree is
then `0` definitionally.

In our setup the meromorphicity conjunct is always provided by
`f.isMeromorphic`, so in practice the only way this leaf fires is when
the projection has `vanishingOrder = ⊤` at every point (e.g. the
literal zero meromorphic function). -/
theorem principalDivisor_zero_of_underlying_zero
    (X : Type*) [TopologicalSpace X] [ConnectedSpace X] [CompactSpace X]
    [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (f : MeromorphicFunctionType X)
    (hf : ¬ ((∀ q : X, MeromorphicAtX (fun p => (f p).getD 0) q) ∧
              (∃ p : X, vanishingOrder X p (fun p => (f p).getD 0) ≠ ⊤))) :
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
the holomorphicity hypothesis discharged by `liftToCp1_isHolomorphic`.
The remaining mathematical content lives in that named obligation plus
the already-refined Sec02 analytic constructor. -/
noncomputable def liftToCp1_branchedCoverData
    (X : Type*) [TopologicalSpace X] [ConnectedSpace X] [CompactSpace X]
    [T2Space X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (f : MeromorphicFunctionType X)
    (_hf_nonconstant : ¬ ∃ c : OnePoint ℂ, ∀ x, f x = c)
    (_hholo : True) :
    BranchedCoverData X (OnePoint ℂ) (meromorphicToCp1 X f) := by
  exact branchedCoverData_of_nonconstant_holomorphic
    (liftToCp1_isHolomorphic X f _hholo) _hf_nonconstant

/-! ## Sub-leaf #3 (HARD) — Laurent order at zeros equals ramification. -/

/-- Primitive finite-chart order comparison for leaf 3.

After unfolding both definitions, this is the local statement that the
meromorphic order of the ℂ-projection at a finite zero agrees with the
analytic order of the CP¹ lift in the finite target chart. -/
theorem vanishingOrder_untopD_eq_mapAnalyticOrderAt_finiteChart
    (X : Type*) [TopologicalSpace X] [ConnectedSpace X] [CompactSpace X]
    [T2Space X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (f : MeromorphicFunctionType X)
    (_hf_nonconstant : ¬ ∃ c : OnePoint ℂ, ∀ x, f x = c)
    (_hholo : True)
    (p : X) (_hp : meromorphicToCp1 X f p = ((0 : ℂ) : OnePoint ℂ)) :
    (vanishingOrder X p (fun q => (f q).getD 0)).untopD 0
      = (mapAnalyticOrderAt (meromorphicToCp1 X f) p : ℤ) := by
  classical
  set c : ℂ := chartAt ℂ p p with hc
  set g : ℂ → ℂ :=
    (fun q : X => (f q).getD 0) ∘ (chartAt ℂ p).symm with hg
  set F : X → OnePoint ℂ := meromorphicToCp1 X f with hF
  have hg_an : AnalyticAt ℂ g c := by
    rw [hg, hc]
    exact liftToCp1_finite_projection_analytic X f _hholo p _hp
  have hchart_eq :
      g =ᶠ[𝓝 c]
        ((Function.invFunOn (fun x : ℂ => (x : OnePoint ℂ)) Set.univ) ∘
          (f.toFun ∘ (chartAt ℂ p).symm)) := by
    rw [hg, hc]
    exact liftToCp1_finite_chartLocal_eventuallyEq_projection X f _hholo p _hp
  have htarget_center :
      ((Function.invFunOn (fun x : ℂ => (x : OnePoint ℂ)) Set.univ) ∘
          (f.toFun ∘ (chartAt ℂ p).symm)) c = 0 := by
    rw [hc, Function.comp_apply, Function.comp_apply]
    have hsymm :
        (chartAt ℂ p).symm (chartAt ℂ p p) = p :=
      (chartAt ℂ p).left_inv (mem_chart_source ℂ p)
    rw [hsymm]
    have hp' : f.toFun p = ((0 : ℂ) : OnePoint ℂ) := by
      simpa [meromorphicToCp1] using _hp
    rw [hp']
    change Function.invFunOn (fun x : ℂ => (x : OnePoint ℂ)) Set.univ
        ((0 : ℂ) : OnePoint ℂ) = 0
    simp +decide [Function.invFunOn]
  have hchart_sub_eq :
      (fun t : ℂ =>
          ((Function.invFunOn (fun x : ℂ => (x : OnePoint ℂ)) Set.univ) ∘
            (f.toFun ∘ (chartAt ℂ p).symm)) t
            - ((Function.invFunOn (fun x : ℂ => (x : OnePoint ℂ)) Set.univ) ∘
                (f.toFun ∘ (chartAt ℂ p).symm)) c)
        =ᶠ[𝓝 c] g := by
    filter_upwards [hchart_eq.symm] with t ht
    rw [ht, htarget_center, sub_zero]
  have hmap_order :
      mapAnalyticOrderAt F p = analyticOrderNatAt g c := by
    have hp' : meromorphicToCp1 X f p = ((0 : ℂ) : OnePoint ℂ) := by
      rw [← hF]
      exact _hp
    rw [hF]
    unfold mapAnalyticOrderAt chartLocalAt
    rw [hp', hc]
    change analyticOrderNatAt
        (fun t : ℂ =>
          ((Function.invFunOn (fun x : ℂ => (x : OnePoint ℂ)) Set.univ) ∘
            (f.toFun ∘ (chartAt ℂ p).symm)) t -
          ((Function.invFunOn (fun x : ℂ => (x : OnePoint ℂ)) Set.univ) ∘
            (f.toFun ∘ (chartAt ℂ p).symm)) c)
        c = analyticOrderNatAt g c
    unfold analyticOrderNatAt
    rw [analyticOrderAt_congr hchart_sub_eq]
  have hmero_order :
      meromorphicOrderAt g c = (analyticOrderAt g c).map (↑) :=
    hg_an.meromorphicOrderAt_eq
  unfold vanishingOrder
  rw [JacobianChallenge.HolomorphicForms.VanishingOrder.orderAt_eq_chartAt]
  rw [← hg, ← hc, hmero_order, hmap_order]
  cases horder : analyticOrderAt g c
  · simp [analyticOrderNatAt, horder]
  · rename_i n
    rw [ENat.map_coe, WithTop.untopD_coe]
    simp [analyticOrderNatAt, horder]

/-- Analytic core of leaf 3: at a finite zero of the CP¹ lift, the
vanishing order of the underlying ℂ-projection is the chart-local
analytic order of the lift.

This removes the `BranchedCoverData` wrapper from the statement; the
remaining proof is the local Laurent normal form in finite target chart. -/
theorem vanishingOrder_eq_mapAnalyticOrderAt_at_zero
    (X : Type*) [TopologicalSpace X] [ConnectedSpace X] [CompactSpace X]
    [T2Space X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (f : MeromorphicFunctionType X)
    (_hf_nonconstant : ¬ ∃ c : OnePoint ℂ, ∀ x, f x = c)
    (_hholo : True)
    (p : X) (_hp : meromorphicToCp1 X f p = ((0 : ℂ) : OnePoint ℂ)) :
    (vanishingOrder X p (fun q => (f q).getD 0)).untopD 0
      = (mapAnalyticOrderAt (meromorphicToCp1 X f) p : ℤ) := by
  exact
    vanishingOrder_untopD_eq_mapAnalyticOrderAt_finiteChart
      X f _hf_nonconstant _hholo p _hp

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
    (X : Type*) [TopologicalSpace X] [ConnectedSpace X] [CompactSpace X]
    [T2Space X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (f : MeromorphicFunctionType X)
    (hf_nonconstant : ¬ ∃ c : OnePoint ℂ, ∀ x, f x = c)
    (hholo : True)
    (p : X) (_hp : meromorphicToCp1 X f p = ((0 : ℂ) : OnePoint ℂ)) :
    let h := liftToCp1_branchedCoverData X f hf_nonconstant hholo
    (vanishingOrder X p (fun q => (f q).getD 0)).untopD 0
      = (h.ramificationIndex p : ℤ) := by
  intro h
  simpa [h, liftToCp1_branchedCoverData,
    branchedCoverData_of_nonconstant_holomorphic]
    using
      vanishingOrder_eq_mapAnalyticOrderAt_at_zero
        X f hf_nonconstant hholo p _hp

/-! ## Sub-leaf #4 (HARD) — Laurent order at poles equals minus ramification. -/

/-- Primitive inversion-chart order comparison for leaf 4.

At a pole, the CP¹ lift is read in the inversion chart.  This local
statement says the integer Laurent order of the ℂ-projection is the
negative of the analytic order of that inversion-chart map. -/
theorem vanishingOrder_untopD_eq_neg_mapAnalyticOrderAt_inftyChart
    (X : Type*) [TopologicalSpace X] [ConnectedSpace X] [CompactSpace X]
    [T2Space X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (f : MeromorphicFunctionType X)
    (_hf_nonconstant : ¬ ∃ c : OnePoint ℂ, ∀ x, f x = c)
    (_hholo : True)
    (p : X) (_hp : meromorphicToCp1 X f p = (∞ : OnePoint ℂ)) :
    (vanishingOrder X p (fun q => (f q).getD 0)).untopD 0
      = -(mapAnalyticOrderAt (meromorphicToCp1 X f) p : ℤ) := by
  classical
  set c : ℂ := chartAt ℂ p p with hc
  set g : ℂ → ℂ :=
    (fun q : X => (f q).getD 0) ∘ (chartAt ℂ p).symm with hg
  set F : X → OnePoint ℂ := meromorphicToCp1 X f with hF
  have hmero : MeromorphicAt g c := by
    rw [hg, hc]
    have h := f.isMeromorphic p
    unfold JacobianChallenge.HolomorphicForms.VanishingOrder.MeromorphicAtX at h
    rwa [JacobianChallenge.HolomorphicForms.VanishingOrder.extChartAt_symm_eq_chartAt_symm,
      JacobianChallenge.HolomorphicForms.VanishingOrder.extChartAt_eq_chartAt] at h
  have htarget_an :
      AnalyticAt ℂ
        (JacobianChallenge.HolomorphicForms.invFwd ∘
          (f.toFun ∘ (chartAt ℂ p).symm)) c := by
    rw [hc]
    exact liftToCp1_infty_chartLocal_analytic X f _hholo p _hp
  have heq_inv :
      g⁻¹ =ᶠ[𝓝 c]
        (JacobianChallenge.HolomorphicForms.invFwd ∘
          (f.toFun ∘ (chartAt ℂ p).symm)) := by
    rw [hg, hc]
    filter_upwards with t
    cases hval : f.toFun ((chartAt ℂ p).symm t) with
    | infty =>
        simp [Pi.inv_apply, Function.comp_apply, hval,
          JacobianChallenge.HolomorphicForms.invFwd]
        change (0 : ℂ) = 0
        rfl
    | coe z =>
        simp [Pi.inv_apply, Function.comp_apply, hval,
          JacobianChallenge.HolomorphicForms.invFwd]
        change z = z
        rfl
  have hginv_an : AnalyticAt ℂ g⁻¹ c :=
    htarget_an.congr heq_inv.symm
  have hmap_order :
      mapAnalyticOrderAt F p = analyticOrderNatAt g⁻¹ c := by
    have hp' : meromorphicToCp1 X f p = (∞ : OnePoint ℂ) := by
      rw [← hF]
      exact _hp
    rw [hF]
    unfold mapAnalyticOrderAt chartLocalAt
    rw [hp', hc]
    change analyticOrderNatAt
        (fun t : ℂ =>
          (JacobianChallenge.HolomorphicForms.invFwd ∘
            (f.toFun ∘ (chartAt ℂ p).symm)) t -
          (JacobianChallenge.HolomorphicForms.invFwd ∘
            (f.toFun ∘ (chartAt ℂ p).symm)) c)
        c = analyticOrderNatAt g⁻¹ c
    have hcenter :
        (JacobianChallenge.HolomorphicForms.invFwd ∘
            (f.toFun ∘ (chartAt ℂ p).symm)) c = 0 := by
      rw [hc, Function.comp_apply, Function.comp_apply]
      have hsymm :
          (chartAt ℂ p).symm (chartAt ℂ p p) = p :=
        (chartAt ℂ p).left_inv (mem_chart_source ℂ p)
      rw [hsymm]
      have hp'' : f.toFun p = (∞ : OnePoint ℂ) := by
        simpa [meromorphicToCp1] using _hp
      rw [hp'']
      simp [JacobianChallenge.HolomorphicForms.invFwd]
    have hsub_eq :
        (fun t : ℂ =>
          (JacobianChallenge.HolomorphicForms.invFwd ∘
            (f.toFun ∘ (chartAt ℂ p).symm)) t -
          (JacobianChallenge.HolomorphicForms.invFwd ∘
            (f.toFun ∘ (chartAt ℂ p).symm)) c)
          =ᶠ[𝓝 c] g⁻¹ := by
      filter_upwards [heq_inv.symm] with t ht
      rw [ht, hcenter, sub_zero]
    unfold analyticOrderNatAt
    rw [analyticOrderAt_congr hsub_eq]
  have hginv_order :
      meromorphicOrderAt g⁻¹ c = (analyticOrderAt g⁻¹ c).map (↑) :=
    hginv_an.meromorphicOrderAt_eq
  have hg_order :
      meromorphicOrderAt g c = -((analyticOrderAt g⁻¹ c).map (↑) : WithTop ℤ) := by
    have h := meromorphicOrderAt_inv (f := g) (x := c)
    rw [hginv_order] at h
    simpa using congrArg Neg.neg h.symm
  unfold vanishingOrder
  rw [JacobianChallenge.HolomorphicForms.VanishingOrder.orderAt_eq_chartAt]
  rw [← hg, ← hc, hg_order, hmap_order]
  cases horder : analyticOrderAt g⁻¹ c
  · simp [analyticOrderNatAt, horder]
  · rename_i n
    rw [ENat.map_coe]
    have hn : analyticOrderNatAt g⁻¹ c = n := by
      simp [analyticOrderNatAt, horder]
    have hneg :
        (-(↑(n : ℤ) : WithTop ℤ)) = ((-(n : ℤ) : ℤ) : WithTop ℤ) := rfl
    rw [hn, hneg, WithTop.untopD_coe]

/-- Analytic core of leaf 4: at a pole of the CP¹ lift, the vanishing
order of the underlying ℂ-projection is the negative of the chart-local
analytic order of the lift.

This removes the `BranchedCoverData` wrapper from the statement; the
remaining proof is the local Laurent normal form in the inversion chart
at `∞`. -/
theorem vanishingOrder_eq_neg_mapAnalyticOrderAt_at_pole
    (X : Type*) [TopologicalSpace X] [ConnectedSpace X] [CompactSpace X]
    [T2Space X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (f : MeromorphicFunctionType X)
    (_hf_nonconstant : ¬ ∃ c : OnePoint ℂ, ∀ x, f x = c)
    (_hholo : True)
    (p : X) (_hp : meromorphicToCp1 X f p = (∞ : OnePoint ℂ)) :
    (vanishingOrder X p (fun q => (f q).getD 0)).untopD 0
      = -(mapAnalyticOrderAt (meromorphicToCp1 X f) p : ℤ) := by
  exact
    vanishingOrder_untopD_eq_neg_mapAnalyticOrderAt_inftyChart
      X f _hf_nonconstant _hholo p _hp

/-- **Sub-leaf #4 of `thm:principal-degree-zero` (plan class: HARD).**

Symmetric to leaf 3: at a point `p` mapped to `∞ ∈ OnePoint ℂ`, the
chart-local Laurent order of the underlying ℂ-valued projection equals
the negative of the ramification index of the lift at `p`.

The chart on `OnePoint ℂ` at `∞` is `1/w`, so the local normal form for
the lift becomes `f(z) = c · z^{-e} + …` with `c ≠ 0`. The
`WithTop.untopD 0` projection lands on the integer `-e`. -/
theorem vanishingOrder_eq_neg_ramificationIndex_at_pole
    (X : Type*) [TopologicalSpace X] [ConnectedSpace X] [CompactSpace X]
    [T2Space X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (f : MeromorphicFunctionType X)
    (hf_nonconstant : ¬ ∃ c : OnePoint ℂ, ∀ x, f x = c)
    (hholo : True)
    (p : X) (_hp : meromorphicToCp1 X f p = (∞ : OnePoint ℂ)) :
    let h := liftToCp1_branchedCoverData X f hf_nonconstant hholo
    (vanishingOrder X p (fun q => (f q).getD 0)).untopD 0
      = -(h.ramificationIndex p : ℤ) := by
  intro h
  simpa [h, liftToCp1_branchedCoverData,
    branchedCoverData_of_nonconstant_holomorphic]
    using
      vanishingOrder_eq_neg_mapAnalyticOrderAt_at_pole
        X f hf_nonconstant hholo p _hp

/-! ## Sub-leaf #5 (MEDIUM) — support of the principal divisor. -/

/-- **Sub-leaf #5a (HARD analytic content of leaf 5).**

At a "regular point" of `f` — neither a zero nor a pole — the Laurent
order of the underlying ℂ-projection of `f` at `p` is the integer `0`.

Discharge route: the projection `(f.toFun q).getD 0` is continuous at
`p` (composing `f.toFun_continuous` with continuity of `(·).getD 0` at
the non-`∞` point `f.toFun p`); pulling this continuity through the
chart `extChartAt 𝓘(ℂ) p` gives `Tendsto (proj ∘ chart.symm)
(𝓝 (chart p)) (𝓝 z)` where `z = (f.toFun p).getD 0 ≠ 0`. Restricting
to the punctured neighbourhood and applying Mathlib's
`tendsto_ne_zero_iff_meromorphicOrderAt_eq_zero` (mp direction) gives
`meromorphicOrderAt = 0`, which equals `orderAt = vanishingOrder` by
the project's chart-pullback definition. -/
theorem vanishingOrder_eq_zero_of_regular_point
    (X : Type*) [TopologicalSpace X] [ConnectedSpace X] [CompactSpace X]
    [T2Space X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (f : MeromorphicFunctionType X) (_hholo : True) (p : X)
    (h0 : meromorphicToCp1 X f p ≠ ((0 : ℂ) : OnePoint ℂ))
    (hinf : meromorphicToCp1 X f p ≠ (∞ : OnePoint ℂ)) :
    vanishingOrder X p (fun q => (f q).getD 0) = 0 := by
  classical
  -- Step 1. Extract z : ℂ from `f.toFun p ≠ ↑0` and `≠ ∞`.
  obtain ⟨z, hz_eq, hz_ne⟩ :
      ∃ z : ℂ, f.toFun p = (↑z : OnePoint ℂ) ∧ z ≠ 0 := by
    rcases hcase : f.toFun p with _ | z
    · exact absurd hcase hinf
    · refine ⟨z, rfl, ?_⟩
      intro hz0
      apply h0
      show f.toFun p = ((0 : ℂ) : OnePoint ℂ)
      rw [hcase, hz0]
      rfl
  -- Step 2. Continuity of `(·).getD 0` at `f.toFun p = ↑z`.
  have hgetD_at :
      ContinuousAt (fun w : OnePoint ℂ => w.getD 0) (f.toFun p) := by
    rw [hz_eq, OnePoint.continuousAt_coe]
    exact continuousAt_id
  -- Step 3. Continuity of the projection at p.
  have hproj_at :
      ContinuousAt (fun q : X => (f.toFun q).getD 0) p :=
    hgetD_at.comp f.toFun_continuous.continuousAt
  -- Step 4. Compose with chart.symm: projection ∘ chart.symm is
  -- continuous at chart p, with limiting value z.
  have hsymm_at :
      ContinuousAt (extChartAt 𝓘(ℂ) p).symm ((extChartAt 𝓘(ℂ) p) p) :=
    continuousAt_extChartAt_symm p
  have hsymm_apply :
      (extChartAt 𝓘(ℂ) p).symm ((extChartAt 𝓘(ℂ) p) p) = p :=
    extChartAt_to_inv p
  have hcomp_at :
      ContinuousAt ((fun q : X => (f.toFun q).getD 0)
          ∘ (extChartAt 𝓘(ℂ) p).symm)
        ((extChartAt 𝓘(ℂ) p) p) := by
    have hproj_at' :
        ContinuousAt (fun q : X => (f.toFun q).getD 0)
          ((extChartAt 𝓘(ℂ) p).symm ((extChartAt 𝓘(ℂ) p) p)) := by
      rw [hsymm_apply]; exact hproj_at
    exact hproj_at'.comp hsymm_at
  -- Step 5. Tendsto in punctured neighbourhood with limit z.
  have hval :
      ((fun q : X => (f.toFun q).getD 0) ∘ (extChartAt 𝓘(ℂ) p).symm)
        ((extChartAt 𝓘(ℂ) p) p) = z := by
    show (f.toFun ((extChartAt 𝓘(ℂ) p).symm ((extChartAt 𝓘(ℂ) p) p))).getD 0 = z
    rw [hsymm_apply, hz_eq]
    rfl
  have htendsto :
      Tendsto ((fun q : X => (f.toFun q).getD 0)
          ∘ (extChartAt 𝓘(ℂ) p).symm)
        (𝓝[≠] ((extChartAt 𝓘(ℂ) p) p)) (𝓝 z) := by
    have h := hcomp_at.tendsto
    rw [hval] at h
    exact h.mono_left nhdsWithin_le_nhds
  -- Step 6. Apply Mathlib's iff (mp direction).
  show JacobianChallenge.HolomorphicForms.VanishingOrder.orderAt p
      (fun q => (f q).getD 0) = 0
  unfold JacobianChallenge.HolomorphicForms.VanishingOrder.orderAt
  exact (tendsto_ne_zero_iff_meromorphicOrderAt_eq_zero
            (f.isMeromorphic p)).mp ⟨z, hz_ne, htendsto⟩

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
    (X : Type*) [TopologicalSpace X] [ConnectedSpace X] [CompactSpace X]
    [T2Space X] [ChartedSpace ℂ X]
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
    (X : Type*) [TopologicalSpace X] [ConnectedSpace X] [CompactSpace X]
    [T2Space X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (f : MeromorphicFunctionType X)
    (hf_nonconstant : ¬ ∃ c : OnePoint ℂ, ∀ x, f x = c)
    (hholo : True)
    (hcond : (∀ q : X, MeromorphicAtX (fun p => (f p).getD 0) q) ∧
              (∃ p : X, vanishingOrder X p (fun p => (f p).getD 0) ≠ ⊤)) :
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
says the order of a nonzero constant is `0`. -/
theorem vanishingOrder_const_nonzero
    (X : Type*) [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (p : X) {z : ℂ} (hz : z ≠ 0) :
    vanishingOrder X p (fun _ => z) = 0 := by
  classical
  show JacobianChallenge.HolomorphicForms.VanishingOrder.orderAt p
      (fun _ : X => z) = 0
  unfold JacobianChallenge.HolomorphicForms.VanishingOrder.orderAt
  show meromorphicOrderAt (fun _ : ℂ => z) ((extChartAt 𝓘(ℂ) p) p) = 0
  rw [meromorphicOrderAt_const]
  exact if_neg hz

/-- **Sub-leaf #7c** — `principalDivisor` of a constant nonzero
projection is the zero divisor.

Mathematical content: when the underlying ℂ-projection of `f` is the
nonzero constant `z`, every coefficient `vanishingOrder p _` is `0`
(by leaf 7b), so the `Finsupp.onFinset` reduces to `0`. -/
theorem principalDivisor_eq_zero_of_constant_nonzero
    (X : Type*) [TopologicalSpace X] [ConnectedSpace X] [CompactSpace X]
    [ChartedSpace ℂ X]
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
    (X : Type*) [TopologicalSpace X] [ConnectedSpace X] [CompactSpace X]
    [T2Space X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (f : MeromorphicFunctionType X)
    (hf : ∃ p : X, vanishingOrder X p (fun q => (f q).getD 0) ≠ ⊤) :
    Divisor.degree (principalDivisor X f) = 0 := by
  classical
  -- Combine `f.isMeromorphic` with `hf` to form the discriminant of
  -- `principalDivisor`'s `by_cases`, used by leaf 6 below.
  have hcond_disc :
      (∀ q : X, MeromorphicAtX (fun p => (f p).getD 0) q) ∧
      (∃ p : X, vanishingOrder X p (fun p => (f p).getD 0) ≠ ⊤) :=
    ⟨f.isMeromorphic, hf⟩
  by_cases hconst : ∃ c : OnePoint ℂ, ∀ x, f x = c
  · -- Constant case. Determine which constant.
    obtain ⟨c, hc⟩ := hconst
    -- The constant cannot be ∞ (would force vanishingOrder = ⊤ everywhere,
    -- contradicting hf). Hence c = ↑z. Furthermore z ≠ 0, otherwise
    -- (f x).getD 0 = 0 always and vanishingOrder = ⊤ everywhere.
    have hf_const_proj : ∀ q, (f q).getD 0 = c.getD 0 := by
      intro q; rw [hc q]
    -- Either c = ∞ or c = ↑z; rule out both bad subcases.
    have hc_finite_proj : ∃ z : ℂ, c = (↑z : OnePoint ℂ) ∧ z ≠ 0 := by
      cases hcase : c with
      | infty =>
        exfalso
        -- (f x).getD 0 = 0 for all x, so vanishingOrder = ⊤ everywhere
        -- (constant zero function), contradicting hf.
        obtain ⟨p, hp⟩ := hf
        apply hp
        have heq : (fun q : X => (f q).getD 0) = (fun _ : X => (0 : ℂ)) := by
          funext q; rw [hf_const_proj q, hcase]; rfl
        rw [heq]
        -- vanishingOrder X p (fun _ => 0) = ⊤
        show JacobianChallenge.HolomorphicForms.VanishingOrder.orderAt p
            (fun _ : X => (0 : ℂ)) = ⊤
        unfold JacobianChallenge.HolomorphicForms.VanishingOrder.orderAt
        show meromorphicOrderAt (fun _ : ℂ => (0 : ℂ))
            ((extChartAt 𝓘(ℂ) p) p) = ⊤
        rw [meromorphicOrderAt_const]; exact if_pos rfl
      | coe z =>
        refine ⟨z, rfl, ?_⟩
        intro hz0
        -- z = 0 ⇒ projection identically 0 ⇒ vanishingOrder = ⊤ everywhere
        obtain ⟨p, hp⟩ := hf
        apply hp
        have heq : (fun q : X => (f q).getD 0) = (fun _ : X => (0 : ℂ)) := by
          funext q; rw [hf_const_proj q, hcase, hz0]; rfl
        rw [heq]
        show JacobianChallenge.HolomorphicForms.VanishingOrder.orderAt p
            (fun _ : X => (0 : ℂ)) = ⊤
        unfold JacobianChallenge.HolomorphicForms.VanishingOrder.orderAt
        show meromorphicOrderAt (fun _ : ℂ => (0 : ℂ))
            ((extChartAt 𝓘(ℂ) p) p) = ⊤
        rw [meromorphicOrderAt_const]; exact if_pos rfl
    obtain ⟨z, rfl, hz_ne⟩ := hc_finite_proj
    -- Each (f x).getD 0 = z.
    have hconst_z : ∀ x, (f x).getD 0 = z := by
      intro x; rw [hc x]; rfl
    rw [principalDivisor_eq_zero_of_constant_nonzero X f hz_ne hconst_z, map_zero]
  · -- Nonconstant case: apply leaf 6, then cancel.
    have h6 := degree_principalDivisor_eq_zeros_minus_poles
      X f hconst trivial hcond_disc
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
    [T2Space X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (f : MeromorphicFunctionType X) :
    Divisor.degree (principalDivisor X f) = 0 := by
  classical
  by_cases hf : ∃ p : X, vanishingOrder X p (fun q => (f q).getD 0) ≠ ⊤
  · exact principal_degree_zero_of_nonzero X f hf
  · -- The discriminant of `principalDivisor` is `(meromorphic) ∧ (∃ finite
    -- order)`. The first conjunct is `f.isMeromorphic`; the second
    -- conjunct is exactly `hf`. So `¬ hf` falsifies the discriminant.
    refine principalDivisor_zero_of_underlying_zero X f ?_
    rintro ⟨_, hf'⟩; exact hf hf'

end JacobianChallenge.Blueprint
