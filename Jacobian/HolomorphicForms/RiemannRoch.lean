import Jacobian.HolomorphicForms.AnalyticGenus
import Jacobian.HolomorphicForms.Meromorphic

/-!
# Riemann-Roch interface for the genus-zero route

This module exposes the first production theorem leaf needed by
`GenusZeroClassification.lean`: genus zero gives a meromorphic map with one
prescribed simple pole.  The eventual proof belongs here, built from divisor
theory and Riemann-Roch for compact Riemann surfaces.
-/

namespace JacobianChallenge.HolomorphicForms

open scoped Manifold

/-- A nonconstant element of the Riemann-Roch space `L([P])`. -/
structure GenusZeroPointRiemannRochElement
    (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [FiniteDimensionalHolomorphicOneForms ℂ X]
    (P : X)
    (_h : analyticGenus ℂ X = 0) where
  meromorphicMap : MeromorphicMapToSphere X
  nonconstant : meromorphicMap.Nonconstant
  mem_L_point : meromorphicMap.MemRiemannRochSpace (Divisor.point P)

/-- Fixed-pole Riemann-Roch output in genus zero. -/
structure GenusZeroFixedPoleMeromorphicData
    (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [FiniteDimensionalHolomorphicOneForms ℂ X]
    (P : X)
    (_h : analyticGenus ℂ X = 0) where
  meromorphicMap : MeromorphicMapToSphere X
  poleDivisor_eq_point : meromorphicMap.poles = Divisor.point P

/-- **Riemann-Roch dimension leaf.** On a compact connected genus-zero
Riemann surface, `L([P])` contains a nonconstant meromorphic function.

Bottom-up content: prove the Riemann-Roch calculation `ℓ(P) = 2`, choose a
nonconstant element of `L(P)`, and package the divisor-boundedness condition
`(f) + [P] ≥ 0`. -/
theorem genusZero_exists_nonconstant_mem_L_point
    (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [FiniteDimensionalHolomorphicOneForms ℂ X]
    (P : X)
    (h : analyticGenus ℂ X = 0) :
    Nonempty (GenusZeroPointRiemannRochElement X P h) := by
  sorry

/-- **Pole-identification leaf.** A nonconstant element of `L([P])` on a
genus-zero compact Riemann surface has pole divisor exactly `[P]`.

Bottom-up content: `mem_L_point` gives pole divisor bounded by `[P]`; if the
pole divisor were `0`, the map would be holomorphic `X → ℂ` and hence
constant by compactness, contradicting `nonconstant`. -/
theorem genusZero_poleDivisor_eq_point_of_nonconstant_mem_L_point
    (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [FiniteDimensionalHolomorphicOneForms ℂ X]
    {P : X}
    {h : analyticGenus ℂ X = 0}
    (f : GenusZeroPointRiemannRochElement X P h) :
    f.meromorphicMap.poles = Divisor.point P := by
  -- BLOCKER: The theorem is unprovable from the current definitions.
  -- `MeromorphicMapToSphere` carries `poleDivisor` as a free data field with
  -- no axiom linking it to the actual behavior of `toMap`.  A counterexample
  -- exists: take `poleDivisor = 0`, `zeroDivisor = 0`, any nonconstant
  -- `toMap`, and `mem_L_point` holds because `Effective (point P)` is true,
  -- yet `poleDivisor ≠ point P`.  To make this provable, two pieces are
  -- needed:
  --   1. An axiom on `MeromorphicMapToSphere` connecting `poleDivisor = 0`
  --      to the map being holomorphic (pole-free), e.g.
  --      `poles_zero_iff_holomorphic : poleDivisor = 0 ↔ ∀ x, toMap x ≠ ∞`.
  --   2. A Liouville-type theorem for compact connected Riemann surfaces:
  --      holomorphic `X → ℂ` implies constant (missing from Mathlib;
  --      requires maximum modulus principle or open mapping theorem for
  --      ℂ-valued holomorphic functions on compact connected complex
  --      manifolds).
  sorry

/-- **Riemann-Roch assembly.** On a compact connected genus-zero Riemann
surface, for every point `P` there is a meromorphic function with exactly one
simple pole at `P`. -/
theorem genusZero_fixedPole_meromorphicData_nonempty
    (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [FiniteDimensionalHolomorphicOneForms ℂ X]
    (P : X)
    (h : analyticGenus ℂ X = 0) :
    Nonempty (GenusZeroFixedPoleMeromorphicData X P h) := by
  rcases genusZero_exists_nonconstant_mem_L_point X P h with ⟨f⟩
  exact ⟨
    { meromorphicMap := f.meromorphicMap
      poleDivisor_eq_point :=
        genusZero_poleDivisor_eq_point_of_nonconstant_mem_L_point X f }⟩

end JacobianChallenge.HolomorphicForms
