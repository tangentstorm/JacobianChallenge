import Jacobian.HolomorphicForms.RiemannRoch
import Jacobian.HolomorphicForms.RRKMinusPointVanishing

/-!
# Path B leaf: a nonconstant `L([P])` element has pole divisor exactly `[P]`

Supporting leaf for GitHub issue #232 (genus-zero uniformization), **Path B**
(Riemann–Roch route). Tracking node `lem:rr-nonconstant-L-point-has-exact-pole`.

This file gives an **independent** derivation of the "headline obligation 3"
fact: on a compact connected genus-zero Riemann surface, a *nonconstant*
element `f ∈ L([P])` has pole divisor exactly `Divisor.point P`.

## Statement (this leaf)

`genusZero_poleDivisor_eq_point_of_nonconstant_mem_L_point'` takes the two
honest hypotheses

* `f.Nonconstant`, and
* `f.MemRiemannRochSpace (Divisor.point P)`  (i.e. `(f) + [P] ≥ 0`),

and concludes `f.poles = Divisor.point P`. No appeal to #232/#233, to the
biholomorphism, or to any goal-field accessor — the proof is purely
divisor-theoretic plus the compact-Riemann-surface Liouville fact.

## Proof outline

1. `MemRiemannRochSpace` unfolds to `Effective ((f) + [P])`, and
   `(f) = zeros − poles`. Combined with the disjoint-support property
   `zero_or_pole_eq_zero` this forces `poles ≤ [P]` pointwise.
2. `poles` is effective (`poleDivisor_nonneg`).
3. `poles ≠ 0`: otherwise `f` would be a pole-free meromorphic map to the
   sphere on a compact connected RS, hence **constant** by the maximum-modulus
   / compact-Liouville lemma
   `holomorphic_meromorphicMapToSphere_constant_on_compact`
   (proved upstream via Mathlib's
   `MDifferentiable.exists_eq_const_of_compactSpace`). This contradicts
   `f.Nonconstant`.
4. An effective divisor `≤ [P]` and `≠ 0` equals `[P]`
   (`effective_le_point_iff_grounded`).

The genuine analytic kernel — "a global holomorphic function on a compact
connected Riemann surface is constant" — is **not** open here: it is supplied
by `holomorphic_compact_connected_constant` (in `HolomorphicCompactConstant`)
through its meromorphic-map wrapper. This leaf is therefore sorry-free.
-/

namespace JacobianChallenge.HolomorphicForms

open scoped Manifold OnePoint Topology

/--
**Path B leaf (#232).** A nonconstant element of the Riemann–Roch space
`L([P])` on a compact connected genus-zero Riemann surface has pole divisor
exactly `Divisor.point P`.

This is the bare form taking `f.Nonconstant` and `f.MemRiemannRochSpace
(Divisor.point P)` as hypotheses, independent of the
`GenusZeroPointRiemannRochElement` packaging. The genus hypothesis is not
needed for *this* implication: nonconstancy plus membership in `L([P])` already
pin the pole divisor.
-/
theorem genusZero_poleDivisor_eq_point_of_nonconstant_mem_L_point'
    (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [JacobianChallenge.Periods.StableChartAt ℂ X]
    (P : X) (f : MeromorphicMapToSphere X)
    (hnc : f.Nonconstant)
    (hmem : f.MemRiemannRochSpace (Divisor.point P)) :
    f.poles = Divisor.point P := by
  classical
  -- 1. `MemRiemannRochSpace` says `(f) + [P] ≥ 0`, with `(f) = zeros − poles`.
  unfold MeromorphicMapToSphere.MemRiemannRochSpace at hmem
  rw [MeromorphicMapToSphere.principal_eq_zeroDivisor_sub_poleDivisor] at hmem
  -- 2. Disjoint support of zeros/poles ⇒ `poles ≤ [P]` pointwise.
  have hle : f.poles ≤ Divisor.point P := by
    intro Q
    have h_disjoint := f.zero_or_pole_eq_zero Q
    have h_eff := hmem Q
    simp at h_eff
    cases h_disjoint with
    | inl hz =>
      rw [hz] at h_eff
      simp at h_eff
      exact h_eff
    | inr hp =>
      have h_pt_Q : f.poles Q = 0 := by
        rw [MeromorphicMapToSphere.poles]
        exact hp
      rw [h_pt_Q]
      exact Divisor.effective_point P Q
  -- 3. `poles` is effective.
  have heff : Divisor.Effective f.poles := f.poleDivisor_nonneg
  -- 4. `poles ≠ 0`, else `f` would be pole-free hence constant (compact
  --    Liouville) — contradicting nonconstancy.
  have hne : f.poles ≠ 0 := by
    intro hzero
    have hconst :=
      holomorphic_meromorphicMapToSphere_constant_on_compact X f hzero
    exact hconst hnc
  -- 5. Effective, `≤ [P]`, and nonzero ⇒ equals `[P]`.
  exact effective_le_point_iff_grounded f.poles P heff hle hne

/--
**Path B leaf (#232), packaged form.** The same conclusion stated for a
`GenusZeroPointRiemannRochElement`, matching the shape downstream Path-B
consumers expect. Delegates to the bare form above.
-/
theorem genusZero_poleDivisor_eq_point_of_GenusZeroPointRiemannRochElement
    (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [JacobianChallenge.Periods.StableChartAt ℂ X]
    [FiniteDimensionalHolomorphicOneForms ℂ X]
    (P : X) (h : analyticGenus ℂ X = 0)
    (f : GenusZeroPointRiemannRochElement X P h) :
    f.meromorphicMap.poles = Divisor.point P :=
  genusZero_poleDivisor_eq_point_of_nonconstant_mem_L_point'
    X P f.meromorphicMap f.nonconstant f.mem_L_point

/--
**Path B leaf (#232), analytic-order corollary.** A nonconstant `f ∈ L([P])`
that carries honest analytic data has chart-local analytic order exactly `1`
at `P`.

This is the precise fact the branched-cover / degree chain consumes
(`mapAnalyticOrderAt f.toMap P = 1`), derived here from the *weaker* hypotheses
`f.Nonconstant + f.MemRiemannRochSpace [P] + f.AnalyticData` rather than from a
pre-supplied `f.poles = Divisor.point P`. The proof composes
`genusZero_poleDivisor_eq_point_of_nonconstant_mem_L_point'` (this file, which
pins the pole divisor) with the analytic-order projection
`MeromorphicMapToSphere.mapAnalyticOrderAt_toMap_eq_one_of_analyticData`
(in `MeromorphicToBranchedCover`; cited, not edited).
-/
theorem genusZero_mapAnalyticOrderAt_eq_one_of_nonconstant_mem_L_point
    (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [JacobianChallenge.Periods.StableChartAt ℂ X]
    (P : X) (f : MeromorphicMapToSphere X)
    (han : f.AnalyticData)
    (hnc : f.Nonconstant)
    (hmem : f.MemRiemannRochSpace (Divisor.point P)) :
    JacobianChallenge.HolomorphicForms.mapAnalyticOrderAt f.toMap P = 1 := by
  have hpole : f.poles = Divisor.point P :=
    genusZero_poleDivisor_eq_point_of_nonconstant_mem_L_point' X P f hnc hmem
  exact f.mapAnalyticOrderAt_toMap_eq_one_of_analyticData han P hpole

/--
**Path B leaf (#232), analytic-order corollary, packaged form.** The same
`mapAnalyticOrderAt = 1` conclusion for a `GenusZeroPointRiemannRochElement`
together with its analytic data. Delegates to the bare form above.
-/
theorem genusZero_mapAnalyticOrderAt_eq_one_of_GenusZeroPointRiemannRochElement
    (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [JacobianChallenge.Periods.StableChartAt ℂ X]
    [FiniteDimensionalHolomorphicOneForms ℂ X]
    (P : X) (h : analyticGenus ℂ X = 0)
    (f : GenusZeroPointRiemannRochElement X P h)
    (han : f.meromorphicMap.AnalyticData) :
    JacobianChallenge.HolomorphicForms.mapAnalyticOrderAt f.meromorphicMap.toMap P = 1 :=
  genusZero_mapAnalyticOrderAt_eq_one_of_nonconstant_mem_L_point
    X P f.meromorphicMap han f.nonconstant f.mem_L_point

/--
**Path B leaf (#232), branched-cover degree corollary.** A nonconstant
`f ∈ L([P])` carrying honest analytic data packages as a branched cover of the
sphere whose branched degree over `∞` is `f.poleDivisor.degree.toNat = 1`.

This is the gateway datum for the biholomorphism / injectivity step: it is
derived here from the *weaker* hypotheses
`f.Nonconstant + f.MemRiemannRochSpace [P] + f.AnalyticData` rather than from a
pre-supplied `f.poles = Divisor.point P`. The proof composes
`genusZero_poleDivisor_eq_point_of_nonconstant_mem_L_point'` (this file, which
pins the pole divisor) with the simple-pole branched-cover constructor
`MeromorphicMapToSphere.branchedCoverDataOfPoleDegree_of_simple_pole`
(in `MeromorphicToBranchedCover`; cited, not edited).
-/
theorem genusZero_branchedCoverDataOfPoleDegree_of_nonconstant_mem_L_point
    (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [JacobianChallenge.Periods.StableChartAt ℂ X]
    (P : X) (f : MeromorphicMapToSphere X)
    (han : f.AnalyticData)
    (hnc : f.Nonconstant)
    (hmem : f.MemRiemannRochSpace (Divisor.point P)) :
    f.BranchedCoverDataOfPoleDegree := by
  have hpole : f.poles = Divisor.point P :=
    genusZero_poleDivisor_eq_point_of_nonconstant_mem_L_point' X P f hnc hmem
  exact f.branchedCoverDataOfPoleDegree_of_simple_pole P hnc hpole han

/--
**Path B leaf (#232), branched-cover degree corollary, packaged form.** The same
`BranchedCoverDataOfPoleDegree` conclusion for a
`GenusZeroPointRiemannRochElement` together with its analytic data. Delegates to
the bare form above.
-/
theorem genusZero_branchedCoverDataOfPoleDegree_of_GenusZeroPointRiemannRochElement
    (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [JacobianChallenge.Periods.StableChartAt ℂ X]
    [FiniteDimensionalHolomorphicOneForms ℂ X]
    (P : X) (h : analyticGenus ℂ X = 0)
    (f : GenusZeroPointRiemannRochElement X P h)
    (han : f.meromorphicMap.AnalyticData) :
    f.meromorphicMap.BranchedCoverDataOfPoleDegree :=
  genusZero_branchedCoverDataOfPoleDegree_of_nonconstant_mem_L_point
    X P f.meromorphicMap han f.nonconstant f.mem_L_point

/--
**Path B leaf (#232), degree-one bijectivity package.** A nonconstant
`f ∈ L([P])` carrying honest analytic data yields the full
`MeromorphicDegreeOneData` record: `f.toMap` is continuous, **bijective**, and
its pole divisor has degree one. This is the exact record downstream consumers
(`GenusZeroClassification`, `AnalyticOfCurveBasis`) read via `bijective_toMap`.

Compared with `meromorphicDegreeOneData_of_poleDivisor_point`
(in `MeromorphicDegree`; cited, not edited), the hypotheses here are *weaker*
on two counts: the pole divisor is pinned by Riemann–Roch membership rather
than pre-supplied, and continuity comes directly from
`AnalyticData.continuous_toMap`, so no separate `PoleModulusData` is needed.
The proof composes this file's pole-divisor and branched-cover leaves with the
degree bookkeeping and bijectivity bridges of `MeromorphicDegree`.
-/
theorem genusZero_meromorphicDegreeOneData_of_nonconstant_mem_L_point
    (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [JacobianChallenge.Periods.StableChartAt ℂ X]
    (P : X) (f : MeromorphicMapToSphere X)
    (han : f.AnalyticData)
    (hnc : f.Nonconstant)
    (hmem : f.MemRiemannRochSpace (Divisor.point P)) :
    Nonempty (MeromorphicDegreeOneData X f) := by
  have hpole : f.poles = Divisor.point P :=
    genusZero_poleDivisor_eq_point_of_nonconstant_mem_L_point' X P f hnc hmem
  have hcont : Continuous f.toMap := han.continuous_toMap
  have hdegree : Divisor.degree f.poles = 1 :=
    meromorphicMapToSphere_poleDivisor_degree_eq_one_of_point f P hpole
  have hbranch : f.BranchedCoverDataOfPoleDegree :=
    genusZero_branchedCoverDataOfPoleDegree_of_nonconstant_mem_L_point
      X P f han hnc hmem
  exact ⟨{ continuous_toMap := hcont
           bijective_toMap :=
             meromorphicMapToSphere_bijective_of_poleDivisor_degree_one
               X f hcont hdegree hbranch
           degree_eq_pole_degree := hdegree }⟩

/--
**Path B leaf (#232), degree-one bijectivity package, packaged form.** The same
`MeromorphicDegreeOneData` conclusion for a `GenusZeroPointRiemannRochElement`
together with its analytic data. Delegates to the bare form above.
-/
theorem genusZero_meromorphicDegreeOneData_of_GenusZeroPointRiemannRochElement
    (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [JacobianChallenge.Periods.StableChartAt ℂ X]
    [FiniteDimensionalHolomorphicOneForms ℂ X]
    (P : X) (h : analyticGenus ℂ X = 0)
    (f : GenusZeroPointRiemannRochElement X P h)
    (han : f.meromorphicMap.AnalyticData) :
    Nonempty (MeromorphicDegreeOneData X f.meromorphicMap) :=
  genusZero_meromorphicDegreeOneData_of_nonconstant_mem_L_point
    X P f.meromorphicMap han f.nonconstant f.mem_L_point

/--
**Path B leaf (#232), topological uniformization payoff.** A nonconstant
`f ∈ L([P])` carrying honest analytic data realizes a homeomorphism
`X ≃ₜ OnePoint ℂ` whose underlying map **is** `f.toMap`.

The carried identification `⇑e = f.toMap` is the point of the statement: a
downstream consumer can transport forward smoothness
(`MeromorphicMapToSphere.contMDiff_toMap_of_analyticData`, cited not edited)
along `e` toward the #232 biholomorphism, and the bare homeomorphism feeds the
`*_of_homeomorph_onePoint` providers and the `X ≃ₜ OnePoint ℂ` input of #233.

The proof is pure composition: the accepted degree-one bijectivity package of
this file supplies a continuous bijection, and Mathlib's
`Continuous.homeoOfEquivCompactToT2` promotes a continuous bijection from a
compact space to a T2 space to a homeomorphism.
-/
theorem genusZero_homeomorph_onePoint_of_nonconstant_mem_L_point
    (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [JacobianChallenge.Periods.StableChartAt ℂ X]
    (P : X) (f : MeromorphicMapToSphere X)
    (han : f.AnalyticData)
    (hnc : f.Nonconstant)
    (hmem : f.MemRiemannRochSpace (Divisor.point P)) :
    ∃ e : X ≃ₜ OnePoint ℂ, ⇑e = f.toMap := by
  obtain ⟨data⟩ :=
    genusZero_meromorphicDegreeOneData_of_nonconstant_mem_L_point
      X P f han hnc hmem
  let equiv : X ≃ OnePoint ℂ := Equiv.ofBijective f.toMap data.bijective_toMap
  have hcont : Continuous equiv := by
    simpa [equiv] using data.continuous_toMap
  exact ⟨hcont.homeoOfEquivCompactToT2, rfl⟩

/--
**Path B leaf (#232), topological uniformization payoff, packaged form.** The
same homeomorphism conclusion for a `GenusZeroPointRiemannRochElement` together
with its analytic data. Delegates to the bare form above.
-/
theorem genusZero_homeomorph_onePoint_of_GenusZeroPointRiemannRochElement
    (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [JacobianChallenge.Periods.StableChartAt ℂ X]
    [FiniteDimensionalHolomorphicOneForms ℂ X]
    (P : X) (h : analyticGenus ℂ X = 0)
    (f : GenusZeroPointRiemannRochElement X P h)
    (han : f.meromorphicMap.AnalyticData) :
    ∃ e : X ≃ₜ OnePoint ℂ, ⇑e = f.meromorphicMap.toMap :=
  genusZero_homeomorph_onePoint_of_nonconstant_mem_L_point
    X P f.meromorphicMap han f.nonconstant f.mem_L_point

/-! ### Bridge into the sound germ-space Riemann-Roch carrier

The carrier `RiemannRochBoundedSection X D` (and through it the module-facing
span `RiemannRochGermSpace X D`) is built on `MeromorphicFunctionWithDivisors`,
whose `order`-compatibility fields force the zero divisor to be effective.
`MeromorphicMapToSphere` carries no such effectivity, but for a nonconstant
element of `L([P])` it is derivable: the pole-divisor leaf of this file pins
`poles = [P]`, so at `P` disjointness forces `zeros P = 0`, and away from `P`
Riemann-Roch membership gives `zeros Q ≥ 0` directly.
-/

/--
**Path B leaf (#232), zero-divisor effectivity.** A nonconstant `f ∈ L([P])`
has effective zero divisor. This is one of the four demanded fields of the
open effective granular provider, derived here from the honest hypotheses
alone (no `AnalyticData` needed).
-/
theorem genusZero_zeroDivisor_effective_of_nonconstant_mem_L_point
    (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [JacobianChallenge.Periods.StableChartAt ℂ X]
    (P : X) (f : MeromorphicMapToSphere X)
    (hnc : f.Nonconstant)
    (hmem : f.MemRiemannRochSpace (Divisor.point P)) :
    Divisor.Effective f.zeroDivisor := by
  classical
  have hpole : f.poles = Divisor.point P :=
    genusZero_poleDivisor_eq_point_of_nonconstant_mem_L_point' X P f hnc hmem
  intro Q
  by_cases hQP : Q = P
  · -- At `P` the pole divisor is `1 ≠ 0`, so disjointness pins `zeros P = 0`.
    subst hQP
    have hpQ : f.poleDivisor Q = 1 := by
      have h := congrArg (fun D : Divisor X => D Q) hpole
      simpa [MeromorphicMapToSphere.poles, Divisor.point_apply_self] using h
    rcases f.zero_or_pole_eq_zero Q with hz | hp
    · rw [hz]
    · rw [hp] at hpQ
      omega
  · -- Away from `P` the membership inequality reduces to `zeros Q ≥ 0`.
    have hpQ : f.poleDivisor Q = 0 := by
      have h := congrArg (fun D : Divisor X => D Q) hpole
      simpa [MeromorphicMapToSphere.poles, Divisor.point_apply_ne hQP] using h
    unfold MeromorphicMapToSphere.MemRiemannRochSpace at hmem
    rw [MeromorphicMapToSphere.principal_eq_zeroDivisor_sub_poleDivisor] at hmem
    have h_eff := hmem Q
    simp [Finsupp.add_apply, Finsupp.sub_apply, Divisor.point_apply_ne hQP, hpQ]
      at h_eff
    omega

/--
**General bridge into the divisor-compatible carrier.** A
`MeromorphicMapToSphere` with honest analytic data and an effective zero
divisor packages as a `MeromorphicFunctionWithDivisors`: the underlying
function and germs come from the analytic-data lift
`toMeromorphicFunctionType` (cited from `MeromorphicToBranchedCover`, not
edited), the divisor fields are copied, and the recorded order function is the
principal-divisor coefficient, whose compatibility with the zero/pole fields
is exactly disjointness plus the two effectivity facts.
-/
noncomputable def MeromorphicMapToSphere.toMeromorphicFunctionWithDivisors
    {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [JacobianChallenge.Periods.StableChartAt ℂ X]
    (f : MeromorphicMapToSphere X) (han : f.AnalyticData)
    (heff : Divisor.Effective f.zeroDivisor) :
    MeromorphicFunctionWithDivisors X where
  toFunction := f.toMeromorphicFunctionType han
  germs := (f.toMeromorphicFunctionType han).germFamily
  germs_eq_toFunction := rfl
  zeroDivisor := f.zeroDivisor
  poleDivisor := f.poleDivisor
  principalDivisor := f.principalDivisor
  order := fun Q => (f.principalDivisor Q : WithTop ℤ)
  zeroDivisor_apply := by
    intro Q
    have hpe : f.principalDivisor Q = f.zeroDivisor Q - f.poleDivisor Q := by
      rw [f.principalDivisor_eq, Finsupp.sub_apply]
    have hnn := f.poleDivisor_nonneg Q
    have heffQ := heff Q
    rw [zeroCoeffOfOrder, WithTop.untopD_coe, hpe]
    rcases f.zero_or_pole_eq_zero Q with hz | hp
    · rw [hz]
      exact (max_eq_right (by omega)).symm
    · rw [hp, sub_zero]
      exact (max_eq_left heffQ).symm
  poleDivisor_apply := by
    intro Q
    have hpe : f.principalDivisor Q = f.zeroDivisor Q - f.poleDivisor Q := by
      rw [f.principalDivisor_eq, Finsupp.sub_apply]
    have hnn := f.poleDivisor_nonneg Q
    have heffQ := heff Q
    rw [poleCoeffOfOrder, WithTop.untopD_coe, hpe]
    rcases f.zero_or_pole_eq_zero Q with hz | hp
    · rw [hz, zero_sub, neg_neg]
      exact (max_eq_left hnn).symm
    · rw [hp]
      exact (max_eq_right (by omega)).symm
  principalDivisor_apply := by
    intro Q
    rw [principalCoeffOfOrder, WithTop.untopD_coe]
  principalDivisor_eq := f.principalDivisor_eq
  poleDivisor_nonneg := f.poleDivisor_nonneg
  zero_or_pole_eq_zero := f.zero_or_pole_eq_zero
  toFun_ne_infty_of_poleDivisor_zero := by
    intro Q hQ
    simpa using f.toMap_ne_infty_of_poleDivisor_zero Q hQ

/--
Riemann-Roch membership transfers along the bridge: both sides are
`Divisor.Effective (principal + D)` and the principal divisors are copied.
-/
theorem MeromorphicMapToSphere.memRiemannRochSpace_toMeromorphicFunctionWithDivisors
    {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [JacobianChallenge.Periods.StableChartAt ℂ X]
    (f : MeromorphicMapToSphere X) (han : f.AnalyticData)
    (heff : Divisor.Effective f.zeroDivisor)
    (D : Divisor X) (hmem : f.MemRiemannRochSpace D) :
    (f.toMeromorphicFunctionWithDivisors han heff).MemRiemannRochSpace D :=
  hmem

/--
A `MeromorphicMapToSphere` in `L(D)` with analytic data and effective zero
divisor is a divisor-compatible Riemann-Roch bounded section.
-/
noncomputable def MeromorphicMapToSphere.toRiemannRochBoundedSection
    {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [JacobianChallenge.Periods.StableChartAt ℂ X]
    (f : MeromorphicMapToSphere X) (han : f.AnalyticData)
    (heff : Divisor.Effective f.zeroDivisor)
    (D : Divisor X) (hmem : f.MemRiemannRochSpace D) :
    RiemannRochBoundedSection X D :=
  ⟨f.toMeromorphicFunctionWithDivisors han heff,
   f.memRiemannRochSpace_toMeromorphicFunctionWithDivisors han heff D hmem⟩

@[simp] theorem MeromorphicMapToSphere.toRiemannRochBoundedSection_coe
    {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [JacobianChallenge.Periods.StableChartAt ℂ X]
    (f : MeromorphicMapToSphere X) (han : f.AnalyticData)
    (heff : Divisor.Effective f.zeroDivisor)
    (D : Divisor X) (hmem : f.MemRiemannRochSpace D) :
    ⇑(f.toRiemannRochBoundedSection han heff D hmem) = f.toMap :=
  rfl

/--
**Path B lane meet (#232).** A nonconstant `f ∈ L([P])` with honest analytic
data lands in the sound germ-space Riemann-Roch carrier: it packages as a
`RiemannRochBoundedSection X [P]` whose underlying function **is** `f.toMap`,
and hence (via `toRiemannRochGermSpace`, cited from `RiemannRoch`, not edited)
its germs are a member of `RiemannRochGermSpace X [P]` — the span whose
`finrank = 2` computation is the Path-B dimension core. This is the point
where the jc3 consumer chain and the germ-space carrier lane meet on one
object.
-/
theorem genusZero_riemannRochBoundedSection_of_nonconstant_mem_L_point
    (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [JacobianChallenge.Periods.StableChartAt ℂ X]
    (P : X) (f : MeromorphicMapToSphere X)
    (han : f.AnalyticData)
    (hnc : f.Nonconstant)
    (hmem : f.MemRiemannRochSpace (Divisor.point P)) :
    ∃ s : RiemannRochBoundedSection X (Divisor.point P), ⇑s = f.toMap := by
  have heff : Divisor.Effective f.zeroDivisor :=
    genusZero_zeroDivisor_effective_of_nonconstant_mem_L_point X P f hnc hmem
  exact ⟨f.toRiemannRochBoundedSection han heff (Divisor.point P) hmem, rfl⟩

/--
**Path B lane meet (#232), packaged form.** The same bounded-section
conclusion for a `GenusZeroPointRiemannRochElement` together with its analytic
data. Delegates to the bare form above.
-/
theorem genusZero_riemannRochBoundedSection_of_GenusZeroPointRiemannRochElement
    (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [JacobianChallenge.Periods.StableChartAt ℂ X]
    [FiniteDimensionalHolomorphicOneForms ℂ X]
    (P : X) (h : analyticGenus ℂ X = 0)
    (f : GenusZeroPointRiemannRochElement X P h)
    (han : f.meromorphicMap.AnalyticData) :
    ∃ s : RiemannRochBoundedSection X (Divisor.point P),
      ⇑s = f.meromorphicMap.toMap :=
  genusZero_riemannRochBoundedSection_of_nonconstant_mem_L_point
    X P f.meromorphicMap han f.nonconstant f.mem_L_point

/-! ### The granular-provider field matrix

The open Path-B frontier `genusZero_fixedPole_rr_effectiveGranular_provider`
(in `MeromorphicToBranchedCover`; cited, never edited) demands a
`MeromorphicMapToSphere` with four granular fields. The leaves of this file
plus one `AnalyticData` field prove all four for ANY nonconstant element of
`L([P])` with analytic data, so the provider's remaining content is exactly
"produce a `GenusZeroPointRiemannRochElement` together with its
`AnalyticData`" — the extraction frontier. The statements below copy the
provider's conjunction shape verbatim so the reduction is definitional.
-/

/--
**Path B leaf (#232), granular field matrix.** A nonconstant `f ∈ L([P])`
with honest analytic data satisfies the exact four-field matrix of the open
effective granular provider: effective zero divisor, pole divisor exactly
`[P]`, pointwise meromorphic canonical finite lift, and order-one extension
at the pole.
-/
theorem genusZero_effectiveGranular_fields_of_nonconstant_mem_L_point
    (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [JacobianChallenge.Periods.StableChartAt ℂ X]
    (P : X) (f : MeromorphicMapToSphere X)
    (han : f.AnalyticData)
    (hnc : f.Nonconstant)
    (hmem : f.MemRiemannRochSpace (Divisor.point P)) :
    Divisor.Effective f.zeroDivisor ∧
    f.poles = Divisor.point P ∧
    (∀ p : X,
      JacobianChallenge.HolomorphicForms.VanishingOrder.MeromorphicAtX
        (fun q => (f.toMap q).getD 0) p) ∧
    JacobianChallenge.HolomorphicForms.mapAnalyticOrderAt f.toMap P = 1 :=
  ⟨genusZero_zeroDivisor_effective_of_nonconstant_mem_L_point X P f hnc hmem,
   genusZero_poleDivisor_eq_point_of_nonconstant_mem_L_point' X P f hnc hmem,
   han.meromorphic_getD,
   genusZero_mapAnalyticOrderAt_eq_one_of_nonconstant_mem_L_point
     X P f han hnc hmem⟩

/--
**Path B leaf (#232), granular field matrix, packaged form.** The same
four-field matrix for a `GenusZeroPointRiemannRochElement` together with its
analytic data. Delegates to the bare form above.
-/
theorem genusZero_effectiveGranular_fields_of_GenusZeroPointRiemannRochElement
    (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [JacobianChallenge.Periods.StableChartAt ℂ X]
    [FiniteDimensionalHolomorphicOneForms ℂ X]
    (P : X) (h : analyticGenus ℂ X = 0)
    (f : GenusZeroPointRiemannRochElement X P h)
    (han : f.meromorphicMap.AnalyticData) :
    Divisor.Effective f.meromorphicMap.zeroDivisor ∧
    f.meromorphicMap.poles = Divisor.point P ∧
    (∀ p : X,
      JacobianChallenge.HolomorphicForms.VanishingOrder.MeromorphicAtX
        (fun q => (f.meromorphicMap.toMap q).getD 0) p) ∧
    JacobianChallenge.HolomorphicForms.mapAnalyticOrderAt
      f.meromorphicMap.toMap P = 1 :=
  genusZero_effectiveGranular_fields_of_nonconstant_mem_L_point
    X P f.meromorphicMap han f.nonconstant f.mem_L_point

/--
**Path B reduction (#232).** The literal existential goal of the open
effective granular provider follows from a `GenusZeroPointRiemannRochElement`
together with its analytic data. Once the extraction frontier produces such
an element, the open provider closes by `exact` on this theorem — the
remaining Path-B gap is therefore precisely "element + `AnalyticData`".

This theorem does NOT claim the unconditioned provider: the element and its
analytic data are honest hypotheses, with no routing through the circular
fixed-pole providers.
-/
theorem genusZero_fixedPole_rr_effectiveGranular_of_element
    (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [JacobianChallenge.Periods.StableChartAt ℂ X]
    [FiniteDimensionalHolomorphicOneForms ℂ X]
    (P : X) (h : analyticGenus ℂ X = 0)
    (f : GenusZeroPointRiemannRochElement X P h)
    (han : f.meromorphicMap.AnalyticData) :
    ∃ f' : MeromorphicMapToSphere X,
      Divisor.Effective f'.zeroDivisor ∧
      f'.poles = Divisor.point P ∧
      (∀ p : X,
        JacobianChallenge.HolomorphicForms.VanishingOrder.MeromorphicAtX
          (fun q => (f'.toMap q).getD 0) p) ∧
      JacobianChallenge.HolomorphicForms.mapAnalyticOrderAt f'.toMap P = 1 :=
  ⟨f.meromorphicMap,
   genusZero_effectiveGranular_fields_of_GenusZeroPointRiemannRochElement
     X P h f han⟩

/-! ### Nonconstancy transfer at the germ seam

Interface lemmas for the open germ-to-map bridge
(`genusZero_pointRiemannRochElement_of_germSpace_outside_constants`, in
`RiemannRoch`; cited, never edited): the bridge receives a germ family
outside the constant line and must construct a map-level `Nonconstant`
witness. The connective is proved here on the carrier types.

The degenerate `toFun ≡ ∞` case needs no infiniteness argument: germ families
are built from the finite lift `getD 0`, so an everywhere-`∞` function has
the constant-`0` germ family, which lies in the constant line like every
other pointwise-constant case. The contrapositive is the transfer.
-/

/--
**Germ computation.** A pointwise-constant meromorphic function (constant as
a map to `OnePoint ℂ`, including the everywhere-`∞` case) has the constant
germ at every point, with value the finite projection `c.getD 0`.
-/
theorem MeromorphicFunctionType.germAt_eq_constant_of_forall_toFun_eq
    {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [JacobianChallenge.Periods.StableChartAt ℂ X]
    (f : MeromorphicFunctionType X) (c : OnePoint ℂ)
    (hc : ∀ x, f.toFun x = c) (p : X) :
    f.germAt p = MeromorphicGermAt.constant (X := X) (p := p) (c.getD 0) := by
  have hfin : f.toFiniteFun = fun _ => c.getD 0 := by
    funext q
    simp [MeromorphicFunctionType.toFiniteFun, hc q]
  ext
  rw [MeromorphicFunctionType.germAt_germ, hfin]
  rfl

/--
**Constant-line membership.** A divisor-compatible meromorphic function that
is pointwise constant as a map to `OnePoint ℂ` has germ family inside the
constant germ-family line, witnessed by the finite projection of the constant
value.
-/
theorem MeromorphicFunctionWithDivisors.germs_mem_constantGermFamilyLine_of_forall_toFun_eq
    {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [JacobianChallenge.Periods.StableChartAt ℂ X]
    (g : MeromorphicFunctionWithDivisors X) (c : OnePoint ℂ)
    (hc : ∀ x, g.toFunction.toFun x = c) :
    g.germs ∈ constantGermFamilyLine X := by
  refine ⟨c.getD 0, ?_⟩
  rw [g.germs_eq_toFunction]
  funext P
  rw [constantGermFamilyLinearMap_apply_at]
  exact (g.toFunction.germAt_eq_constant_of_forall_toFun_eq c hc P).symm

/--
**Nonconstancy transfer (the seam interface).** A divisor-compatible
meromorphic function whose germ family lies outside the constant line is
nonconstant as a function to `OnePoint ℂ`. The conclusion is literally the
`MeromorphicMapToSphere.Nonconstant` shape for any map whose `toMap` is
`g.toFunction.toFun`, so the germ-to-map bridge can construct its
`nonconstant` field by `exact` from the extraction hypothesis
`F ∉ constantGermFamilyLine X` once `F` is represented by `g`.
-/
theorem MeromorphicFunctionWithDivisors.nonconstant_of_germs_notMem_constantGermFamilyLine
    {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [JacobianChallenge.Periods.StableChartAt ℂ X]
    (g : MeromorphicFunctionWithDivisors X)
    (hg : g.germs ∉ constantGermFamilyLine X) :
    ¬ ∃ c : OnePoint ℂ, ∀ x : X, g.toFunction.toFun x = c := by
  rintro ⟨c, hc⟩
  exact hg (g.germs_mem_constantGermFamilyLine_of_forall_toFun_eq c hc)

/-! ### Carrier representative ⟹ element + AnalyticData (statement-level)

Pipeline from a divisor-compatible carrier representative to the inputs of
this file's packaged corollaries. Per manager triage (duplicate-declaration
clash between `RiemannRoch` and `RRKMinusPointVanishing`, queued upstream),
the carrier-to-sphere wrapper is NOT imported: each lemma instead takes the
wrapper's outputs as statement-level hypotheses — a sphere map `f` linked to
the carrier element `g` by `f.toMap = g.toFunction.toFun` and the divisor-copy
facts. The future instantiation site (the wrapper, once the duplicate-decl
reconciliation lands) discharges these hypotheses definitionally; any
`sorryAx` taint stays there, so the declarations below are axiom-clean.

The `simple_pole_order_one` input is provably NOT derivable from the current
carrier fields (a counter-model with recorded order `0` against a genuine
order-`3` root satisfies all fields), so it is taken as the named
order-soundness side condition, never a `sorry`.
-/

/--
**Membership transfer (carrier → sphere, statement-level).** Riemann-Roch
membership for the divisor-compatible carrier transfers to any sphere map
whose principal divisor copies the carrier's: both sides are
`Divisor.Effective (principal + D)`. Mirror of the accepted sphere→carrier
transfer.
-/
theorem MeromorphicFunctionWithDivisors.memRiemannRochSpace_mapToSphere_of_principal_eq
    {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [JacobianChallenge.Periods.StableChartAt ℂ X]
    (g : MeromorphicFunctionWithDivisors X) (f : MeromorphicMapToSphere X)
    (hprin : f.principalDivisor = g.principalDivisor)
    (D : Divisor X) (hmem : g.MemRiemannRochSpace D) :
    f.MemRiemannRochSpace D := by
  unfold MeromorphicMapToSphere.MemRiemannRochSpace
  unfold MeromorphicFunctionWithDivisors.MemRiemannRochSpace at hmem
  have hp : f.principal = g.principal := hprin
  rw [hp]
  exact hmem

/--
**AnalyticData production from carrier facts (statement-level).** A sphere
map whose underlying function is a carrier element's function has honest
analytic data, given the order-soundness side condition (stated carrier-side)
as a hypothesis: global continuity and pointwise meromorphicity of the finite
lift are carried by the underlying `MeromorphicFunctionType`
(`toFun_continuous`, `isMeromorphic`) and transported along the function
identification; the simple-pole order-one field is the hypothesis transported
along the pole-divisor copy.
-/
noncomputable def MeromorphicFunctionWithDivisors.analyticData_mapToSphere_of_simple_pole_order_one
    {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [JacobianChallenge.Periods.StableChartAt ℂ X]
    (g : MeromorphicFunctionWithDivisors X) (f : MeromorphicMapToSphere X)
    (hmap : f.toMap = g.toFunction.toFun)
    (hpoles : f.poleDivisor = g.poleDivisor)
    (hord : ∀ Q : X, g.poles = Divisor.point Q →
      JacobianChallenge.HolomorphicForms.mapAnalyticOrderAt
        g.toFunction.toFun Q = 1) :
    f.AnalyticData where
  continuous_toMap := by
    rw [hmap]
    exact g.toFunction.toFun_continuous
  meromorphic_getD := by
    intro p
    simp only [hmap]
    exact g.toFunction.isMeromorphic p
  simple_pole_order_one := by
    intro Q hQ
    have hgpoles : g.poles = Divisor.point Q := by
      show g.poleDivisor = Divisor.point Q
      rw [← hpoles]
      exact hQ
    simp only [hmap]
    exact hord Q hgpoles

/--
**Element production from a carrier representative (statement-level).** A
divisor-compatible carrier representative in `L([P])` whose germ family lies
outside the constant line yields a `GenusZeroPointRiemannRochElement`, for
any sphere map linked to it by the function identification and the
principal-divisor copy: membership transfers, and nonconstancy is the
accepted germ-seam transfer transported along the identification.
-/
theorem genusZeroPointRiemannRochElement_of_carrier_representative
    (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [JacobianChallenge.Periods.StableChartAt ℂ X]
    [FiniteDimensionalHolomorphicOneForms ℂ X]
    (P : X) (h : analyticGenus ℂ X = 0)
    (g : MeromorphicFunctionWithDivisors X) (f : MeromorphicMapToSphere X)
    (hmap : f.toMap = g.toFunction.toFun)
    (hprin : f.principalDivisor = g.principalDivisor)
    (hmem : g.MemRiemannRochSpace (Divisor.point P))
    (hg : g.germs ∉ constantGermFamilyLine X) :
    Nonempty (GenusZeroPointRiemannRochElement X P h) :=
  ⟨{ meromorphicMap := f
     nonconstant := by
       have hnc := g.nonconstant_of_germs_notMem_constantGermFamilyLine hg
       show ¬ ∃ c : OnePoint ℂ, ∀ x : X, f.toMap x = c
       simp only [hmap]
       exact hnc
     mem_L_point :=
       g.memRiemannRochSpace_mapToSphere_of_principal_eq f hprin
         (Divisor.point P) hmem }⟩

/--
**Pipeline payoff (statement-level).** A carrier representative in `L([P])`
outside the constant line, together with a linked sphere map and the
order-soundness side condition, yields a `GenusZeroPointRiemannRochElement`
WITH its `AnalyticData` — the exact input shape of this file's packaged
corollaries (granular field matrix, degree-one bijectivity, sphere
homeomorphism, bounded-section lane meet). The open germ-to-map bridge
therefore reduces to producing the representative and its linked map; the
hypotheses here are discharged definitionally by the carrier wrapper once the
upstream duplicate-declaration reconciliation lands.
-/
theorem genusZeroPointRiemannRochElement_with_analyticData_of_carrier_representative
    (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [JacobianChallenge.Periods.StableChartAt ℂ X]
    [FiniteDimensionalHolomorphicOneForms ℂ X]
    (P : X) (h : analyticGenus ℂ X = 0)
    (g : MeromorphicFunctionWithDivisors X) (f : MeromorphicMapToSphere X)
    (hmap : f.toMap = g.toFunction.toFun)
    (hprin : f.principalDivisor = g.principalDivisor)
    (hpoles : f.poleDivisor = g.poleDivisor)
    (hmem : g.MemRiemannRochSpace (Divisor.point P))
    (hg : g.germs ∉ constantGermFamilyLine X)
    (hord : ∀ Q : X, g.poles = Divisor.point Q →
      JacobianChallenge.HolomorphicForms.mapAnalyticOrderAt
        g.toFunction.toFun Q = 1) :
    ∃ fe : GenusZeroPointRiemannRochElement X P h,
      Nonempty fe.meromorphicMap.AnalyticData :=
  ⟨{ meromorphicMap := f
     nonconstant := by
       have hnc := g.nonconstant_of_germs_notMem_constantGermFamilyLine hg
       show ¬ ∃ c : OnePoint ℂ, ∀ x : X, f.toMap x = c
       simp only [hmap]
       exact hnc
     mem_L_point :=
       g.memRiemannRochSpace_mapToSphere_of_principal_eq f hprin
         (Divisor.point P) hmem },
   ⟨g.analyticData_mapToSphere_of_simple_pole_order_one f hmap hpoles hord⟩⟩

/-! ### Span-expression extraction package (germ-to-map bridge Steps 1–2)

The two "routine packaging needed" items of the bridge plan: expose an
arbitrary element of the germ-space span as a finite `ℂ`-linear combination
of bounded-section generators (with a nonzero-coefficient refinement), and
the rewrite identifying a generator's germ family after nonzero scalar
multiplication. Pure linear algebra over sorry-free definitions; the
analytic `AddData` step of the bridge is deliberately NOT touched here.
-/

/--
**Bridge Step 1 packaging.** Every element of the Riemann-Roch germ space is
a finite `ℂ`-linear combination of germ families of bounded-section
generators. Direct unfolding of `Submodule.mem_span_set'` plus a choice of
generator for each range member.
-/
theorem RiemannRochGermSpace.exists_finset_sum_generators
    {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [JacobianChallenge.Periods.StableChartAt ℂ X]
    (D : Divisor X) (F : RiemannRochGermSpace X D) :
    ∃ (n : ℕ) (c : Fin n → ℂ) (gen : Fin n → RiemannRochBoundedSection X D),
      (F : MeromorphicGermFamily X) =
        ∑ i, c i • (gen i).toMeromorphicFunctionWithDivisors.germs := by
  classical
  have hF : (F : MeromorphicGermFamily X) ∈
      Submodule.span ℂ
        (Set.range fun s : RiemannRochBoundedSection X D =>
          s.toMeromorphicFunctionWithDivisors.germs) := F.2
  obtain ⟨n, c, g, hsum⟩ := Submodule.mem_span_set'.mp hF
  refine ⟨n, c, fun i => (g i).2.choose, ?_⟩
  rw [← hsum]
  exact Finset.sum_congr rfl fun i _ =>
    congrArg (fun t => c i • t) ((g i).2.choose_spec).symm

/--
**Bridge Step 1–2 packaging, normalized form.** The same finite span
expression with all coefficients nonzero: zero summands are pruned from the
expression (they vanish from the sum), then the surviving index set is
re-enumerated.
-/
theorem RiemannRochGermSpace.exists_finset_sum_generators'
    {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [JacobianChallenge.Periods.StableChartAt ℂ X]
    (D : Divisor X) (F : RiemannRochGermSpace X D) :
    ∃ (n : ℕ) (c : Fin n → ℂ) (gen : Fin n → RiemannRochBoundedSection X D),
      (∀ i, c i ≠ 0) ∧
      (F : MeromorphicGermFamily X) =
        ∑ i, c i • (gen i).toMeromorphicFunctionWithDivisors.germs := by
  classical
  obtain ⟨n, c, gen, hsum⟩ :=
    RiemannRochGermSpace.exists_finset_sum_generators D F
  let s : Finset (Fin n) := Finset.univ.filter (fun i => c i ≠ 0)
  have hfilter :
      ∑ i ∈ s, c i • (gen i).toMeromorphicFunctionWithDivisors.germs =
        ∑ i, c i • (gen i).toMeromorphicFunctionWithDivisors.germs := by
    refine Finset.sum_filter_of_ne fun i _ hne hc0 => hne ?_
    rw [hc0, zero_smul]
  have hattach :
      ∑ i ∈ s, c i • (gen i).toMeromorphicFunctionWithDivisors.germs =
        ∑ x : {i // i ∈ s},
          c x • (gen x).toMeromorphicFunctionWithDivisors.germs :=
    (Finset.sum_coe_sort s
      (fun i => c i • (gen i).toMeromorphicFunctionWithDivisors.germs)).symm
  have hequiv :
      ∑ x : {i // i ∈ s},
          c x • (gen x).toMeromorphicFunctionWithDivisors.germs =
        ∑ j : Fin s.card,
          c (s.equivFin.symm j) •
            (gen (s.equivFin.symm j)).toMeromorphicFunctionWithDivisors.germs := by
    refine Fintype.sum_equiv s.equivFin _ _ fun x => ?_
    rw [Equiv.symm_apply_apply]
  refine ⟨s.card, fun j => c (s.equivFin.symm j),
          fun j => gen (s.equivFin.symm j), fun j => ?_, ?_⟩
  · have hmem : ((s.equivFin.symm j : {i // i ∈ s}) : Fin n) ∈
        Finset.univ.filter (fun i => c i ≠ 0) := (s.equivFin.symm j).2
    exact (Finset.mem_filter.mp hmem).2
  · rw [hsum, ← hfilter, hattach, hequiv]

/--
**Bridge Step 2 packaging.** Nonzero scalar multiplication of a bounded
section multiplies its germ family by the scalar. Definitional: the carrier
constructor sets `germs := c • f.germs`.
-/
@[simp] theorem RiemannRochBoundedSection.smulNonzero_germs
    {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [JacobianChallenge.Periods.StableChartAt ℂ X]
    {D : Divisor X}
    (c : ℂ) (hc : c ≠ 0) (s : RiemannRochBoundedSection X D) :
    (RiemannRochBoundedSection.smulNonzero c hc
        s).toMeromorphicFunctionWithDivisors.germs =
      c • s.toMeromorphicFunctionWithDivisors.germs :=
  rfl

/--
**Bridge Step 2 packaging, subtype-valued form.** The same identity read
through the canonical inclusion into the germ-space module carrier.
-/
@[simp] theorem RiemannRochBoundedSection.smulNonzero_toRiemannRochGermSpace_val
    {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [JacobianChallenge.Periods.StableChartAt ℂ X]
    {D : Divisor X}
    (c : ℂ) (hc : c ≠ 0) (s : RiemannRochBoundedSection X D) :
    ((RiemannRochBoundedSection.smulNonzero c hc s).toRiemannRochGermSpace :
        MeromorphicGermFamily X) =
      c • (s.toRiemannRochGermSpace : MeromorphicGermFamily X) :=
  rfl

/-! ### Bridge Step 5: bounded sections package as sphere maps

The reverse packaging direction of the germ-to-map bridge plan (§5–§7):
consume a bounded section, produce the `MeromorphicMapToSphere` with divisor
data and `L([P])` membership transferred, and instantiate this file's
statement-level carrier pipeline with the wrapper — every linking hypothesis
(`hmap`, `hprin`, `hpoles`) discharges by `rfl` because the wrapper copies
the carrier's function and divisor fields.

**Taint disclosure (deliberate, established policy):** the wrapper
`meromorphicFunctionWithDivisors_to_mapToSphere` (in `RRKMinusPointVanishing`;
imported and cited per brokered terms, never edited) discharges its
`toMap_eq_infty_of_poleDivisor_pos` field through the carrier-gated
germ-order bridge, which is sorried. Every declaration below therefore
inherits `sorryAx` through exactly that one documented chain and nothing
else. When the carrier is made order-sound upstream, this section greens
automatically with zero edits.
-/

/--
**Bridge Step 5 constructor.** A divisor-compatible Riemann-Roch bounded
section packages as a meromorphic map to the sphere via the carrier wrapper.
-/
noncomputable def RiemannRochBoundedSection.toMeromorphicMapToSphere
    {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [JacobianChallenge.Periods.StableChartAt ℂ X]
    {D : Divisor X} (s : RiemannRochBoundedSection X D) :
    MeromorphicMapToSphere X :=
  meromorphicFunctionWithDivisors_to_mapToSphere s.toMeromorphicFunctionWithDivisors

/--
**Bridge Step 5 membership.** The packaged sphere map keeps the bounded
section's Riemann-Roch membership: the wrapper copies the principal divisor,
so the accepted statement-level transfer applies with a definitional link.
-/
theorem RiemannRochBoundedSection.toMeromorphicMapToSphere_memRiemannRochSpace
    {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [JacobianChallenge.Periods.StableChartAt ℂ X]
    {D : Divisor X} (s : RiemannRochBoundedSection X D) :
    s.toMeromorphicMapToSphere.MemRiemannRochSpace D :=
  s.toMeromorphicFunctionWithDivisors.memRiemannRochSpace_mapToSphere_of_principal_eq
    s.toMeromorphicMapToSphere rfl D s.memRiemannRochSpace

/--
**Bridge §5–§7 element production.** A bounded section of `L([P])` whose germ
family lies outside the constant line yields a
`GenusZeroPointRiemannRochElement`: the statement-level carrier pipeline
instantiated with the wrapper, all linking hypotheses by `rfl`.
-/
theorem genusZeroPointRiemannRochElement_of_boundedSection
    (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [JacobianChallenge.Periods.StableChartAt ℂ X]
    [FiniteDimensionalHolomorphicOneForms ℂ X]
    (P : X) (h : analyticGenus ℂ X = 0)
    (s : RiemannRochBoundedSection X (Divisor.point P))
    (hg : s.toMeromorphicFunctionWithDivisors.germs ∉ constantGermFamilyLine X) :
    Nonempty (GenusZeroPointRiemannRochElement X P h) :=
  genusZeroPointRiemannRochElement_of_carrier_representative X P h
    s.toMeromorphicFunctionWithDivisors s.toMeromorphicMapToSphere
    rfl rfl s.memRiemannRochSpace hg

/--
**Bridge §5–§7 element production with analytic data.** Same hypotheses plus
the order-soundness side condition (carrier-side; provably underivable from
current carrier fields, hence a named hypothesis) yield the element WITH its
`AnalyticData` — the exact input of this file's packaged corollaries. With
this, the germ-to-map bridge's remaining content is precisely its Steps 1–4:
the span expression (delivered by this file) and the `AddData` analytic fold.
-/
theorem genusZeroPointRiemannRochElement_with_analyticData_of_boundedSection
    (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [JacobianChallenge.Periods.StableChartAt ℂ X]
    [FiniteDimensionalHolomorphicOneForms ℂ X]
    (P : X) (h : analyticGenus ℂ X = 0)
    (s : RiemannRochBoundedSection X (Divisor.point P))
    (hg : s.toMeromorphicFunctionWithDivisors.germs ∉ constantGermFamilyLine X)
    (hord : ∀ Q : X,
      s.toMeromorphicFunctionWithDivisors.poles = Divisor.point Q →
      JacobianChallenge.HolomorphicForms.mapAnalyticOrderAt
        s.toMeromorphicFunctionWithDivisors.toFunction.toFun Q = 1) :
    ∃ fe : GenusZeroPointRiemannRochElement X P h,
      Nonempty fe.meromorphicMap.AnalyticData :=
  genusZeroPointRiemannRochElement_with_analyticData_of_carrier_representative
    X P h s.toMeromorphicFunctionWithDivisors s.toMeromorphicMapToSphere
    rfl rfl rfl s.memRiemannRochSpace hg hord

end JacobianChallenge.HolomorphicForms
