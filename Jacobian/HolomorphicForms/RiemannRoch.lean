import Jacobian.HolomorphicForms.AnalyticGenus
import Jacobian.HolomorphicForms.Meromorphic
import Mathlib.Geometry.Manifold.Complex

/-!
# Riemann-Roch interface for the genus-zero route

This module exposes the first production theorem leaf needed by
`GenusZeroClassification.lean`: genus zero gives a meromorphic map with one
prescribed simple pole.

The three headline obligations are now sorry-free assemblies of
smaller named obligations (each captured as a separate `theorem`),
mirroring the TeX decomposition in `tex/sections/03-riemann-roch.tex`
(see the `genus-zero-rr-route` subsection added in this round).

Every decomposed leaf has a precise mathematical content with a
docstring proof sketch; some bottom out at sorry-bearing structural
companions exposed near the top of the file. These structural
companions encode the *missing API* on `MeromorphicMapToSphere` and
`Divisor` that the project needs but which Mathlib v4.28.0 does not
yet provide.
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

/-! ### Structural companions on `MeromorphicMapToSphere`

The abstract `MeromorphicMapToSphere` structure carries a `toMap`
plus opaque divisor data, with no axioms tying the divisor data to
the map. Real proofs need *axiomatic bridges* that capture the
expected geometric content. We expose them as named sorries and use
them as black-box hypotheses below. Each captures a single,
reusable structural fact about real meromorphic maps.

These are documented in `tex/sections/03-riemann-roch.tex` under
`§Riemann–Roch genus-zero route` (see the `genus-zero-rr-route`
sub-section).
-/

/-- **Structural axiom (S1).** A meromorphic map to the Riemann sphere
whose pole divisor is `0` factors through the affine chart `ℂ`: there
is a smooth (in fact `ContMDiff` of class `⊤`) function `g : X → ℂ`
such that the original `f.toMap` agrees with `(↑) ∘ g`.

Bottom-up: this is the analytic content of "no poles" — outside the
pole locus, the map lifts through the embedding `ℂ ↪ OnePoint ℂ`. The
project's `MeromorphicMapToSphere` structure does not yet expose this
factorisation; supplying it is a Mathlib-internal task (or a project
refactor of the structure).

Cross-ref: `tex/sections/03-riemann-roch.tex`, `lem:meromorphic-no-poles-factors`. -/
theorem MeromorphicMapToSphere.toFiniteFun_of_no_poles
    {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (f : MeromorphicMapToSphere X) (_hpole : f.poles = 0) :
    ∃ g : X → ℂ, MDifferentiable (modelWithCornersSelf ℂ ℂ) 𝓘(ℂ, ℂ) g ∧
      f.toMap = fun x => ((g x : ℂ) : OnePoint ℂ) := by
  sorry

/-- **Structural axiom (S2).** Membership in `L([P])` implies the pole
divisor is bounded above by `[P]` pointwise; combined with effectivity
of `f.poles` this means `f.poles ∈ {0, point P}`.

Bottom-up: from `Divisor.Effective (f.principal + point P)` and
disjoint zero/pole supports for an actual meromorphic function,
the bound on `f.poles` follows. Currently captured as a sorry on
the abstract structure, since support-disjointness is not in the
fields of `MeromorphicMapToSphere`.

Cross-ref: `tex/sections/03-riemann-roch.tex`, `lem:mem-L-point-pole-bound`. -/
theorem MeromorphicMapToSphere.poles_eq_zero_or_point_of_mem_L_point
    {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (f : MeromorphicMapToSphere X) (P : X)
    (_hmem : f.MemRiemannRochSpace (Divisor.point P)) :
    f.poles = 0 ∨ f.poles = Divisor.point P := by
  sorry

/-- **Structural axiom (S3).** From the genus-zero Riemann-Roch
identity `ℓ([P]) − ℓ(K − [P]) = 2` plus the negative-degree vanishing
`ℓ(K − [P]) = 0`, one obtains a *concrete witness* of a nonconstant
function in `L([P])`. This packages the existential conclusion of the
RR formula into a constructed `GenusZeroPointRiemannRochElement`.

Bottom-up: the RR umbrella in
`Jacobian/Blueprint/Sec02/InputRiemannRoch.lean` provides the
*abstract* `riemann_roch` identity over a `LineBundleType`; this
companion bridges from there to the concrete
`MeromorphicMapToSphere` API used in the genus-zero classification.
The bridge is not yet built (line bundles have no `Module ℂ`-linked
RR-space construction); this is the named structural sorry.

Cross-ref: `tex/sections/03-riemann-roch.tex`, `lem:genus-zero-RR-witness`. -/
theorem genusZero_pointRiemannRochSpace_witness_exists
    (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [FiniteDimensionalHolomorphicOneForms ℂ X]
    (P : X) (h : analyticGenus ℂ X = 0) :
    ∃ f : MeromorphicMapToSphere X,
      f.Nonconstant ∧ f.MemRiemannRochSpace (Divisor.point P) := by
  sorry

/-! ### Headline obligations (sorry-free assemblies) -/

/-- **Headline obligation 1.** On a compact connected genus-zero
Riemann surface, `L([P])` contains a nonconstant meromorphic function.

Sorry-free assembly: extract a witness from
`genusZero_pointRiemannRochSpace_witness_exists` and package it. -/
theorem genusZero_exists_nonconstant_mem_L_point
    (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [FiniteDimensionalHolomorphicOneForms ℂ X]
    (P : X)
    (h : analyticGenus ℂ X = 0) :
    Nonempty (GenusZeroPointRiemannRochElement X P h) := by
  obtain ⟨f, hnc, hmem⟩ := genusZero_pointRiemannRochSpace_witness_exists X P h
  exact ⟨{ meromorphicMap := f, nonconstant := hnc, mem_L_point := hmem }⟩

/-- **Headline obligation 2.** A meromorphic map to the Riemann
sphere on a compact connected complex 1-manifold whose pole divisor
is `0` (i.e. is holomorphic everywhere) is constant.

Sorry-free assembly: factor the map through `ℂ` via
`MeromorphicMapToSphere.toFiniteFun_of_no_poles` (S1), then apply
`MDifferentiable.exists_eq_const_of_compactSpace` (Mathlib's compact
Liouville). -/
theorem holomorphic_meromorphicMapToSphere_constant_on_compact
    (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (f : MeromorphicMapToSphere X)
    (hpole : f.poles = 0) :
    ¬ f.Nonconstant := by
  -- Step 1: factor through ℂ.
  obtain ⟨g, hg_mdiff, hg_eq⟩ := f.toFiniteFun_of_no_poles hpole
  -- Step 2: g is constant by compact Liouville.
  obtain ⟨v, hv⟩ := hg_mdiff.exists_eq_const_of_compactSpace
  -- Step 3: f.toMap is constant equal to (↑v).
  intro hnonconst
  apply hnonconst
  refine ⟨((v : ℂ) : OnePoint ℂ), fun x => ?_⟩
  have h1 : f.toMap x = ((g x : ℂ) : OnePoint ℂ) := by
    rw [hg_eq]
  rw [h1, congr_fun hv x]
  rfl

/-- **Headline obligation 3.** A nonconstant element of `L([P])` on a
genus-zero compact Riemann surface has pole divisor exactly `[P]`.

Sorry-free assembly: by S2 the pole divisor is `0` or `point P`;
the `0` case contradicts nonconstancy via the compact-Liouville
companion `holomorphic_meromorphicMapToSphere_constant_on_compact`.
-/
theorem genusZero_poleDivisor_eq_point_of_nonconstant_mem_L_point
    (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [FiniteDimensionalHolomorphicOneForms ℂ X]
    {P : X}
    {h : analyticGenus ℂ X = 0}
    (f : GenusZeroPointRiemannRochElement X P h) :
    f.meromorphicMap.poles = Divisor.point P := by
  rcases f.meromorphicMap.poles_eq_zero_or_point_of_mem_L_point P f.mem_L_point with
    hzero | hpt
  · -- Pole divisor 0 contradicts nonconstancy via Liouville.
    exfalso
    exact holomorphic_meromorphicMapToSphere_constant_on_compact X f.meromorphicMap hzero
      f.nonconstant
  · exact hpt

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
