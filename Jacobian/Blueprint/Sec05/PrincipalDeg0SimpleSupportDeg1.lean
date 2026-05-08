import Jacobian.Blueprint.Sec01.PrincipalDivisor
import Jacobian.Blueprint.Sec01.MeromorphicToCp1

/-! # Blueprint stub: `lem:principal-deg0-simple-support-deg1`

Section 5 of `tex/sections/05-abel-jacobi-map.tex`.

If `f ∈ Mer(X)^{×}` has principal divisor `(f) = Q₁ - Q₂` with
`Q₁ ≠ Q₂`, then the associated map `f̂ : X → ℂP¹` is nonconstant of
degree 1.

## Status

**Real type signature.** The conclusion is stated with the genuine
`Nonconstant` / `branchedDegree` predicates; the proof is `sorry`
because the upstream analytic infrastructure (open-mapping theorem,
`BranchedCoverData` constructor for meromorphic maps) is still
frontier-bound.

The Worker AE branch (claude/abel-deeper-k7vp2x) provides supporting
combinatorial infrastructure under a nested
`AbelExistence.PrincipalDeg0SimpleSupportDeg1` namespace: the
two-point-divisor model and the deg-0/two-point-support arithmetic.
That infrastructure is preserved here so the eventual real proof can
plug in immediately.
-/

namespace JacobianChallenge.Blueprint

open scoped Manifold

/-- The point divisor `[P]`: the divisor assigning coefficient `1` to `P`
and `0` elsewhere. Wraps `Finsupp.single P 1`. -/
noncomputable def Divisor.point {X : Type*} (P : X) : Divisor X :=
  Finsupp.single P 1

/-- A function `g : X → Y` is *nonconstant*: there is no single value
`c : Y` assumed everywhere. -/
def Nonconstant {X Y : Type*} (g : X → Y) : Prop :=
  ¬ ∃ c : Y, ∀ x : X, g x = c

/-- **Placeholder.** The branched degree of a continuous map
`g : X → Y` between compact Riemann surfaces, viewed as a function.

The eventual definition builds a `BranchedCoverData` (see
`Jacobian/Blueprint/Sec02/BranchedDegree.lean`) from the
open-mapping / isolated-zeros theorems and reads off
`BranchedCoverData.branchedDegree`; that analytic constructor is
still frontier-bound, so we leave the body as `0` (an obviously
wrong but type-correct stand-in). -/
noncomputable def branchedDegreeOfMap
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (_g : X → Y) : ℕ := 0

/-! ### Helper: meromorphic order -1 implies not continuous -/

open Filter in
/-- If a function has meromorphic order -1 at a point, it cannot be continuous there.
Proof: by `meromorphicOrderAt_eq_int_iff`, `f(z) = (z-x)^(-1) • g(z)` near `x`
with `g` analytic and `g(x) ≠ 0`. Since `g` is continuous with `g(x) ≠ 0`, `g` is
bounded away from 0 near `x`, so `‖f(z)‖ = ‖g(z)‖ / ‖z - x‖ → ∞` as `z → x`.
A continuous function at `x` would be bounded near `x`, contradiction. -/
theorem not_continuousAt_of_meromorphicOrderAt_neg_one
    {f : ℂ → ℂ} {x : ℂ} (hf : MeromorphicAt f x)
    (hord : meromorphicOrderAt f x = ↑(-1 : ℤ)) :
    ¬ ContinuousAt f x := by
  intro h_cont;
  have := hf; rw [ meromorphicOrderAt_eq_int_iff ] at hord; obtain ⟨ g, hg_analytic, hg_ne_zero, hg ⟩ := hord; (
  have h_unbounded : Filter.Tendsto (fun z => ‖(z - x) ^ (-1 : ℤ) • g z‖) (nhdsWithin x {x}ᶜ) Filter.atTop := by
    have h_unbounded : Filter.Tendsto (fun z => ‖(z - x)⁻¹‖ * ‖g z‖) (nhdsWithin x {x}ᶜ) Filter.atTop := by
      apply Filter.Tendsto.atTop_mul_pos;
      exact norm_pos_iff.mpr hg_ne_zero;
      · norm_num +zetaDelta at *;
        exact tendsto_inv_nhdsGT_zero.comp ( tendsto_norm_sub_self_nhdsNE x );
      · exact hg_analytic.continuousAt.norm.continuousWithinAt;
    simpa [ norm_smul ] using h_unbounded;
  exact not_tendsto_atTop_of_tendsto_nhds ( by simpa using h_cont.continuousWithinAt.norm ) ( h_unbounded.congr' <| by filter_upwards [ hg ] with z hz; aesop ));
  exact this

/-! ### Helper: positive meromorphic order implies toFun ≠ ∞ -/

open Filter JacobianChallenge.HolomorphicForms.VanishingOrder in
/-- If the chart-pullback of the ℂ-projection of a `MeromorphicFunctionType`
has positive meromorphic order at `p`, then `f.toFun p ≠ ∞`.

Proof sketch: Suppose `f.toFun p = ∞`. By `meromorphicOrderAt_eq_int_iff`
with `n ≥ 1`, the chart-pullback `g(z) = (z - z₀)^n · h(z)` on a punctured
neighborhood with `h` analytic, `h(z₀) ≠ 0`. Since `n ≥ 1`, `h` is nonzero
near `z₀` by continuity, so `g` is nonzero on a punctured neighborhood.
Thus `(f.toFun q).getD 0 ≠ 0` for `q` near `p`, meaning `f.toFun q ≠ ∞`
near `p`. But `f.toFun p = ∞` and `f.toFun` is continuous, so nearby values
are close to `∞` in the OnePoint topology, meaning their norm is large.
But `g(z) = (z - z₀)^n · h(z) → 0` as `z → z₀`, contradicting large norm. -/
theorem toFun_ne_infty_of_pos_meromorphicOrderAt
    {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (f : MeromorphicFunctionType X) (p : X)
    {n : ℤ} (hn : 0 < n)
    (hord : meromorphicOrderAt
      ((fun q => (f.toFun q).getD 0) ∘ (extChartAt 𝓘(ℂ) p).symm)
      (extChartAt 𝓘(ℂ) p p) = ↑n) :
    f.toFun p ≠ OnePoint.infty := by
  have := f.isMeromorphic p;
  contrapose! this;
  intro ⟨e, he, h_analytic⟩;
  rw [ meromorphicOrderAt_eq_int_iff ] at hord;
  · obtain ⟨ g, hg₁, hg₂, hg₃ ⟩ := hord;
    have h_contra : ∀ᶠ z in nhdsWithin (extChartAt 𝓘(ℂ, ℂ) p p) {extChartAt 𝓘(ℂ, ℂ) p p}ᶜ, f.toFun ((extChartAt 𝓘(ℂ, ℂ) p).symm z) = OnePoint.infty → False := by
      filter_upwards [ hg₃, hg₁.continuousAt.continuousWithinAt.eventually_ne hg₂, self_mem_nhdsWithin ] with z hz₁ hz₂ hz₃;
      cases h : f.toFun ( ( extChartAt 𝓘(ℂ, ℂ) p ).symm z ) <;> simp_all +decide [ sub_eq_iff_eq_add ];
      cases n <;> simp_all +decide [ Option.getD ];
      exact hz₃ ( sub_eq_zero.mp hz₁.1 );
    have h_contra : Filter.Tendsto (fun z => ‖(f.toFun ((extChartAt 𝓘(ℂ, ℂ) p).symm z)).getD 0‖) (nhdsWithin (extChartAt 𝓘(ℂ, ℂ) p p) {extChartAt 𝓘(ℂ, ℂ) p p}ᶜ) Filter.atTop := by
      have h_contra : Filter.Tendsto (fun z => f.toFun ((extChartAt 𝓘(ℂ, ℂ) p).symm z)) (nhdsWithin (extChartAt 𝓘(ℂ, ℂ) p p) {extChartAt 𝓘(ℂ, ℂ) p p}ᶜ) (nhds (f.toFun p)) := by
        have h_contra : ContinuousAt (fun z => f.toFun ((extChartAt 𝓘(ℂ, ℂ) p).symm z)) (extChartAt 𝓘(ℂ, ℂ) p p) := by
          exact f.toFun_continuous.continuousAt.comp ( ContinuousAt.comp ( continuousAt_extChartAt_symm p ) ( continuousAt_id ) );
        convert h_contra.tendsto.mono_left inf_le_left using 1;
        simp +decide [ extChartAt ];
      rw [ this ] at h_contra;
      rw [ OnePoint.nhds_infty_eq ] at h_contra;
      rw [ Filter.tendsto_atTop ];
      intro b; specialize h_contra ( Filter.mem_sup.mpr ⟨ ?_, ?_ ⟩ ) <;> simp_all +decide [ Filter.mem_map, Filter.mem_pure ] ;
      exact { x : OnePoint ℂ | x = OnePoint.infty ∨ ∃ z : ℂ, x = OnePoint.some z ∧ b ≤ ‖z‖ };
      · simp +decide [ Set.preimage ];
        rw [ mem_cocompact ];
        exact ⟨ Metric.closedBall 0 b, ProperSpace.isCompact_closedBall _ _, fun x hx => le_of_not_gt fun h => hx <| mem_closedBall_zero_iff.mpr h.le ⟩;
      · exact Or.inl rfl;
      · filter_upwards [ h_contra, ‹∀ᶠ z in nhdsWithin ( chartAt ℂ p p ) { chartAt ℂ p p } ᶜ, f.toFun ( chartAt ℂ p |>.symm z ) = OnePoint.infty → False› ] with z hz₁ hz₂ ; aesop;
    have h_contra : Filter.Tendsto (fun z => ‖(z - extChartAt 𝓘(ℂ, ℂ) p p) ^ n • g z‖) (nhdsWithin (extChartAt 𝓘(ℂ, ℂ) p p) {extChartAt 𝓘(ℂ, ℂ) p p}ᶜ) Filter.atTop := by
      refine' h_contra.congr' _;
      filter_upwards [ hg₃ ] with z hz using by aesop;
    have h_contra : Filter.Tendsto (fun z => ‖(z - extChartAt 𝓘(ℂ, ℂ) p p) ^ n‖ * ‖g z‖) (nhdsWithin (extChartAt 𝓘(ℂ, ℂ) p p) {extChartAt 𝓘(ℂ, ℂ) p p}ᶜ) Filter.atTop := by
      simpa [ norm_smul ] using h_contra;
    have h_contra : Filter.Tendsto (fun z => ‖(z - extChartAt 𝓘(ℂ, ℂ) p p) ^ n‖) (nhdsWithin (extChartAt 𝓘(ℂ, ℂ) p p) {extChartAt 𝓘(ℂ, ℂ) p p}ᶜ) (nhds 0) := by
      rcases n with ( _ | n ) <;> norm_num at *;
      exact tendsto_nhdsWithin_of_tendsto_nhds ( Continuous.tendsto' ( by continuity ) _ _ ( by simp +decide [ hn.ne' ] ) );
    have h_contra : Filter.Tendsto (fun z => ‖(z - extChartAt 𝓘(ℂ, ℂ) p p) ^ n‖ * ‖g z‖) (nhdsWithin (extChartAt 𝓘(ℂ, ℂ) p p) {extChartAt 𝓘(ℂ, ℂ) p p}ᶜ) (nhds 0) := by
      simpa using h_contra.mul ( hg₁.continuousAt.norm.continuousWithinAt );
    exact not_tendsto_atTop_of_tendsto_nhds h_contra ‹_›;
  · exact ⟨ e, he, h_analytic ⟩

open Filter JacobianChallenge.HolomorphicForms.VanishingOrder in
/-- If `f.toFun p = (w : ℂ)` (a finite value) and the chart-pullback of
the ℂ-projection has positive meromorphic order at `p`, then `w = 0`.

Proof: Since `f.toFun p = (w : ℂ)`, the ℂ-projection `(fun q => (f.toFun q).getD 0)`
is continuous at `p` (same argument as in sorry 1: f.toFun is continuous, near `p`
the OnePoint values are close to `(w : OnePoint ℂ)` hence finite, so getD 0 extracts
the ℂ value continuously). The chart-pullback is then continuous at `z₀ := extChartAt p p`
with value `w`. On a punctured neighborhood, the chart-pullback equals `(z - z₀)^n · h(z)`
with `h` analytic. Since `n ≥ 1`, this tends to `0` as `z → z₀`. By uniqueness of limits
(ℂ is T2), `w = 0`. -/
theorem toFun_val_eq_zero_of_pos_meromorphicOrderAt
    {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (f : MeromorphicFunctionType X) (p : X) (w : ℂ)
    (hw : f.toFun p = (w : OnePoint ℂ))
    {n : ℤ} (hn : 0 < n)
    (hmer : MeromorphicAt
      ((fun q => (f.toFun q).getD 0) ∘ (extChartAt 𝓘(ℂ) p).symm)
      (extChartAt 𝓘(ℂ) p p))
    (hord : meromorphicOrderAt
      ((fun q => (f.toFun q).getD 0) ∘ (extChartAt 𝓘(ℂ) p).symm)
      (extChartAt 𝓘(ℂ) p p) = ↑n) :
    w = 0 := by
  have := hmer; simp_all +decide [ meromorphicOrderAt_eq_int_iff ];
  obtain ⟨ g, hg₁, hg₂, hg₃ ⟩ := hord;
  have h_lim : Filter.Tendsto (fun z => (z - (chartAt ℂ p) p) ^ n * g z) (nhdsWithin ((chartAt ℂ p) p) {((chartAt ℂ p) p)}ᶜ) (nhds 0) := by
    rcases n with ( _ | n ) <;> simp_all +decide [ zpow_add₀, zpow_sub₀ ];
    exact tendsto_nhdsWithin_of_tendsto_nhds ( ContinuousAt.tendsto ( by exact ContinuousAt.mul ( ContinuousAt.pow ( continuousAt_id.sub continuousAt_const ) _ ) hg₁.continuousAt ) |> fun h => h.trans ( by simp +decide [ hn.ne' ] ) );
  have h_cont : ContinuousAt (fun z => (f.toFun (chartAt ℂ p |>.symm z)).getD 0) (chartAt ℂ p p) := by
    have h_cont : ContinuousAt (fun z => (f.toFun z).getD 0) (chartAt ℂ p |>.symm (chartAt ℂ p p)) := by
      have h_cont : ContinuousAt (fun z => (f.toFun z).getD 0) p := by
        have h_cont : ContinuousAt (fun z => f.toFun z) p := by
          exact f.toFun_continuous.continuousAt
        rw [ ContinuousAt ] at *;
        rw [ tendsto_nhds ] at *;
        intro s hs hs'; specialize h_cont ( OnePoint.some '' s ) ; simp_all +decide [ Set.preimage ] ;
        filter_upwards [ h_cont ( by simpa [ Option.getD ] using hs' ) ] with x hx using by cases h : f.toFun x <;> aesop;
      aesop;
    convert h_cont.comp ( show ContinuousAt ( fun z => ( chartAt ℂ p ).symm z ) ( chartAt ℂ p p ) from ?_ ) using 1;
    exact ContinuousAt.comp ( show ContinuousAt ( fun z => ( chartAt ℂ p ).symm z ) ( chartAt ℂ p p ) from by exact ( chartAt ℂ p ).continuousAt_symm ( by simp +decide ) ) continuousAt_id;
  have := tendsto_nhds_unique ( h_cont.mono_left nhdsWithin_le_nhds ) ( h_lim.congr' <| by filter_upwards [ hg₃ ] with z hz; rw [ hz ] ) ; aesop;

/-! ### TOPDOWN decomposition (round 1)

The headline theorem is split into 4 named sub-obligations + a sorry-free
assembly. Each sub-obligation is individually attackable; the deepest
(`branchedDegree_eq_one_of_singleton_pole_set`) bottoms out in the
frontier `BranchedCoverData` constructor, which is the genuine analytic
gap. The other three are mostly classical bookkeeping. -/

/-
**Sub-leaf 1.** If `(f) = [Q₁] - [Q₂]` with `Q₁ ≠ Q₂`, then `f`
takes the pole value `∞` at `Q₂`: i.e. `meromorphicToCp1 X f Q₂ = ∞`.

Bottom-up content: the principal-divisor description records the
Laurent order at every point. Coefficient `-1` at `Q₂` means a simple
pole, hence `f.toFun Q₂ = ∞`. Should follow from the
`principalDivisor`-`vanishingOrder` adjunction in
`Sec01/PrincipalDivisor.lean` plus the fact that
`MeromorphicFunctionType` records poles by sending them to `∞`.
-/
theorem meromorphicToCp1_at_pole_of_simple_two_point_principal
    (X : Type*) [TopologicalSpace X] [ConnectedSpace X] [CompactSpace X]
    [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (f : MeromorphicFunctionType X) (Q₁ Q₂ : X) (hne : Q₁ ≠ Q₂)
    (hpd : principalDivisor X f = Divisor.point Q₁ - Divisor.point Q₂) :
    meromorphicToCp1 X f Q₂ = OnePoint.infty := by
  by_contra h;
  obtain ⟨w, hw⟩ : ∃ w : ℂ, f.toFun Q₂ = w := by
    exact?;
  have h_cont : ContinuousAt (fun q => (f.toFun q).getD 0) Q₂ := by
    have h_cont : ContinuousAt (fun q => f.toFun q) Q₂ := by
      exact f.toFun_continuous.continuousAt;
    rw [ ContinuousAt ] at *;
    rw [ tendsto_nhds ] at *;
    intro s hs hs';
    specialize h_cont ( OnePoint.some '' s ) ?_ ?_ <;> simp_all +decide [ Set.preimage ];
    · exact?;
    · filter_upwards [ h_cont ] with x hx using by obtain ⟨ y, hy, hy' ⟩ := hx; cases h : f.toFun x <;> aesop;
  have h_order : (vanishingOrder X Q₂ (fun q => (f.toFun q).getD 0)).untopD 0 = -1 := by
    unfold principalDivisor at hpd;
    split_ifs at hpd <;> simp_all +decide [ Finsupp.ext_iff, Divisor.point ];
    · simpa [ hne ] using hpd Q₂;
    · specialize hpd Q₁ ; simp_all +decide [ Finsupp.single_apply ];
  have h_order : (meromorphicOrderAt ((fun q => (f.toFun q).getD 0) ∘ (extChartAt 𝓘(ℂ) Q₂).symm) (extChartAt 𝓘(ℂ) Q₂ Q₂)) = -1 := by
    unfold vanishingOrder at h_order;
    unfold HolomorphicForms.VanishingOrder.orderAt at h_order;
    cases h : meromorphicOrderAt ( ( fun q => Option.getD ( f.toFun q ) 0 ) ∘ ( extChartAt 𝓘(ℂ, ℂ) Q₂ ).symm ) ( extChartAt 𝓘(ℂ, ℂ) Q₂ Q₂ ) <;> simp_all +decide;
  have h_not_cont : ¬ ContinuousAt ((fun q => (f.toFun q).getD 0) ∘ (extChartAt 𝓘(ℂ) Q₂).symm) (extChartAt 𝓘(ℂ) Q₂ Q₂) := by
    apply_rules [ not_continuousAt_of_meromorphicOrderAt_neg_one ];
    exact f.isMeromorphic Q₂;
  apply h_not_cont;
  apply ContinuousAt.comp;
  · aesop;
  · exact?

/-
**Sub-leaf 2.** Symmetric to sub-leaf 1: the simple zero at `Q₁`
gives `meromorphicToCp1 X f Q₁ = 0`.
-/
theorem meromorphicToCp1_at_zero_of_simple_two_point_principal
    (X : Type*) [TopologicalSpace X] [ConnectedSpace X] [CompactSpace X]
    [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (f : MeromorphicFunctionType X) (Q₁ Q₂ : X) (hne : Q₁ ≠ Q₂)
    (hpd : principalDivisor X f = Divisor.point Q₁ - Divisor.point Q₂) :
    meromorphicToCp1 X f Q₁ = ((0 : ℂ) : OnePoint ℂ) := by
  have h_meromorphic_order : meromorphicOrderAt ((fun q => (f.toFun q).getD 0) ∘ (extChartAt 𝓘(ℂ) Q₁).symm) (extChartAt 𝓘(ℂ) Q₁ Q₁) = 1 := by
    unfold principalDivisor at hpd;
    unfold Divisor.point at hpd;
    split_ifs at hpd <;> replace hpd := congr_arg ( fun g => g Q₁ ) hpd <;> simp_all +decide [ Finsupp.single_apply ];
    unfold vanishingOrder at hpd;
    unfold HolomorphicForms.VanishingOrder.orderAt at hpd;
    cases h : meromorphicOrderAt ( ( fun q => Option.getD ( f.toFun q ) 0 ) ∘ ( chartAt ℂ Q₁ ).symm ) ( chartAt ℂ Q₁ Q₁ ) <;> simp_all +decide;
    · exact absurd hpd ( by erw [ h ] ; simp +decide );
    · erw [ h ] at hpd ; aesop;
  obtain ⟨w, hw⟩ : ∃ w : ℂ, f.toFun Q₁ = (w : OnePoint ℂ) := by
    have h_finite : f.toFun Q₁ ≠ OnePoint.infty := by
      apply toFun_ne_infty_of_pos_meromorphicOrderAt f Q₁ (by norm_num) h_meromorphic_order;
    exact?;
  have := toFun_val_eq_zero_of_pos_meromorphicOrderAt f Q₁ w hw ( by norm_num ) ( f.isMeromorphic Q₁ ) h_meromorphic_order; aesop;

/-- **Sub-leaf 3 (general, sorry-free).** Universal-logic helper: a
function attaining two distinct values is nonconstant. -/
theorem nonconstant_of_two_distinct_values
    {X Y : Type*} (g : X → Y) {a b : X} {c d : Y}
    (hne_val : c ≠ d) (ha : g a = c) (hb : g b = d) :
    Nonconstant g := by
  intro ⟨e, he⟩
  exact hne_val (by rw [← ha, he a, ← he b, hb])

/-- **Sub-leaf 4.** From `(meromorphicToCp1 X f)⁻¹(∞) = {Q₂}` (a simple
pole) we get `branchedDegreeOfMap = 1`. This is the deep frontier sub-
obligation: it requires the `BranchedCoverData` constructor for
nonconstant holomorphic maps to ℂP¹, plus the constancy-of-weighted-
fibre-count theorem (Sec02 leaf 8). -/
theorem branchedDegreeOfMap_eq_one_of_simple_two_point_principal
    (X : Type*) [TopologicalSpace X] [ConnectedSpace X] [CompactSpace X]
    [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (f : MeromorphicFunctionType X) (Q₁ Q₂ : X) (hne : Q₁ ≠ Q₂)
    (hpd : principalDivisor X f = Divisor.point Q₁ - Divisor.point Q₂) :
    branchedDegreeOfMap (meromorphicToCp1 X f) = 1 := by
  sorry

/-- **Headline theorem (sorry-free assembly).** If `f ∈ Mer(X)^{×}` has
principal divisor `(f) = Q₁ - Q₂` with `Q₁ ≠ Q₂`, then the associated
map `f̂ : X → ℂP¹` is nonconstant of branched degree 1.

Assembled from the four sub-leaves above:
- nonconstancy: sub-leaves 1+2 give distinct values at `Q₁` and `Q₂`,
  then sub-leaf 3 gives nonconstancy.
- branched-degree-1: sub-leaf 4 directly. -/
theorem principal_deg0_simple_support_deg1
    (X : Type*) [TopologicalSpace X] [ConnectedSpace X] [CompactSpace X]
    [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (f : MeromorphicFunctionType X) (Q₁ Q₂ : X) (hne : Q₁ ≠ Q₂)
    (hpd : principalDivisor X f = Divisor.point Q₁ - Divisor.point Q₂) :
    Nonconstant (meromorphicToCp1 X f) ∧
    branchedDegreeOfMap (meromorphicToCp1 X f) = 1 := by
  refine ⟨?_, branchedDegreeOfMap_eq_one_of_simple_two_point_principal X f Q₁ Q₂ hne hpd⟩
  exact nonconstant_of_two_distinct_values
    (meromorphicToCp1 X f)
    (a := Q₁) (b := Q₂)
    (c := ((0 : ℂ) : OnePoint ℂ))
    (d := OnePoint.infty)
    (by exact OnePoint.coe_ne_infty 0)
    (meromorphicToCp1_at_zero_of_simple_two_point_principal X f Q₁ Q₂ hne hpd)
    (meromorphicToCp1_at_pole_of_simple_two_point_principal X f Q₁ Q₂ hne hpd)

namespace AbelExistence
namespace PrincipalDeg0SimpleSupportDeg1

/-- A divisor with support of size at most two: a pair of integer
coefficients at two distinguished points. -/
structure TwoPointDivisor where
  /-- Coefficient at the first support point. -/
  m : Int
  /-- Coefficient at the second support point. -/
  n : Int

/-- Degree of a two-point divisor. -/
def TwoPointDivisor.degree (D : TwoPointDivisor) : Int := D.m + D.n

/-- Both coefficients are nonzero (the "support has exactly two
points" condition; coefficients are allowed to be zero only if the
support has size strictly less than two). -/
def TwoPointDivisor.bothNonzero (D : TwoPointDivisor) : Prop :=
  D.m ≠ 0 ∧ D.n ≠ 0

/-- **General SHORT lemma.** A two-point degree-zero divisor with
both coefficients nonzero has `n = -m`.

Proof: `m + n = 0` forces `n = -m` by integer arithmetic.
Discharged by `omega` from core Lean. -/
theorem coefficients_opposite (D : TwoPointDivisor)
    (hdeg : D.degree = 0) (_hnt : D.bothNonzero) :
    D.n = -D.m := by
  unfold TwoPointDivisor.degree at hdeg
  omega

/-- **Specialisation: deg-1 case.** Hypothesis `|m| = 1` plus
two-point support and degree zero forces `D = ±([p] - [q])`,
i.e. `(m, n) ∈ {(1, -1), (-1, 1)}`.

In `Int`, `m * m = 1` is the unit-normalisation of `|m| = 1`. The
unit step `m * m = 1 → m = 1 ∨ m = -1` is nonlinear, but a
case analysis combined with `Int.mul_le_mul_of_nonneg_left` and
`Int.neg_mul_neg` bounds `|m| * |m| ≥ 4` whenever `|m| ≥ 2`,
contradicting `m * m = 1`. -/
theorem principal_deg0_simple_support_deg1
    (D : TwoPointDivisor)
    (hdeg : D.degree = 0) (hnt : D.bothNonzero)
    (hunit : D.m * D.m = 1) :
    (D.m = 1 ∧ D.n = -1) ∨ (D.m = -1 ∧ D.n = 1) := by
  have hopp : D.n = -D.m := coefficients_opposite D hdeg hnt
  have hm_unit : D.m = 1 ∨ D.m = -1 := by
    by_cases hpos : 0 < D.m
    · by_cases h1 : D.m = 1
      · exact Or.inl h1
      · exfalso
        have h3 : 2 ≤ D.m := by omega
        have h3' : (0 : Int) ≤ D.m := by omega
        have h4 : D.m * 2 ≤ D.m * D.m :=
          Int.mul_le_mul_of_nonneg_left h3 h3'
        rw [hunit] at h4
        omega
    · by_cases hzero : D.m = 0
      · exfalso
        rw [hzero, Int.zero_mul] at hunit
        omega
      · by_cases hn1 : D.m = -1
        · exact Or.inr hn1
        · exfalso
          have h3 : 2 ≤ -D.m := by omega
          have h3' : (0 : Int) ≤ -D.m := by omega
          have h4 : (-D.m) * 2 ≤ (-D.m) * (-D.m) :=
            Int.mul_le_mul_of_nonneg_left h3 h3'
          have h5 : (-D.m) * (-D.m) = D.m * D.m := Int.neg_mul_neg D.m D.m
          rw [h5, hunit] at h4
          omega
  rcases hm_unit with hpm | hpm
  · refine Or.inl ⟨hpm, ?_⟩
    rw [hopp, hpm]
  · refine Or.inr ⟨hpm, ?_⟩
    rw [hopp, hpm]
    decide

end PrincipalDeg0SimpleSupportDeg1
end AbelExistence

end JacobianChallenge.Blueprint