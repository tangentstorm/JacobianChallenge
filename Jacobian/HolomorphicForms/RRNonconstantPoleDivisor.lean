import Jacobian.HolomorphicForms.RiemannRoch

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

end JacobianChallenge.HolomorphicForms
