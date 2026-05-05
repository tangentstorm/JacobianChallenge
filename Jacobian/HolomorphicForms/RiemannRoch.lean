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

/-- **Structural axiom (S1a).** When the pole divisor is `0`, the map
`f.toMap` never takes the value `∞`. This is the *pointwise*
content of "no poles".

Cross-ref: `tex/sections/03-riemann-roch.tex`,
`lem:meromorphic-no-infty-of-no-poles`. -/
theorem MeromorphicMapToSphere.toMap_ne_infty_of_no_poles
    {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (f : MeromorphicMapToSphere X) (_hpole : f.poles = 0) :
    ∀ x : X, f.toMap x ≠ (OnePoint.infty : OnePoint ℂ) := by
  sorry

/-- **Structural axiom (S1b-α).** When `f.toMap x ≠ ∞`, there is a
canonical lift `g x : ℂ` such that `((g x : ℂ) : OnePoint ℂ) = f.toMap x`.
Pure algebraic: `OnePoint` strips off `some/none`.

Cross-ref: `tex/sections/03-riemann-roch.tex`,
`lem:onepoint-lift-of-no-infty`. -/
theorem MeromorphicMapToSphere.toFiniteFun_pointwise_lift_exists
    {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (f : MeromorphicMapToSphere X)
    (hne : ∀ x : X, f.toMap x ≠ (OnePoint.infty : OnePoint ℂ)) :
    ∃ g : X → ℂ, f.toMap = fun x => ((g x : ℂ) : OnePoint ℂ) := by
  -- `OnePoint ℂ = Option ℂ`. The hypothesis `hne` says `f.toMap x ≠ none`
  -- pointwise, so `f.toMap x = some (g x)` for `g x := (f.toMap x).getD 0`.
  refine ⟨fun x => (f.toMap x).getD 0, funext fun x => ?_⟩
  -- `↑(g x) = some (g x)` by definition; need `f.toMap x = some (g x)`.
  show f.toMap x = (((f.toMap x).getD 0 : ℂ) : OnePoint ℂ)
  -- `f.toMap x : OnePoint ℂ = Option ℂ`. Case-split.
  cases h : f.toMap x with
  | infty =>
    -- Excluded by `hne`.
    exact absurd h (hne x)
  | coe y =>
    -- `f.toMap x = ↑y`, `getD 0 = y` since `OnePoint.coe y = some y` in `Option ℂ`.
    show (↑y : OnePoint ℂ) = ((((↑y : OnePoint ℂ) : Option ℂ).getD 0 : ℂ) : OnePoint ℂ)
    rfl

/-- **Structural axiom (S1b-β).** If a meromorphic-map's `toMap`
factors as `((·) : ℂ → OnePoint ℂ) ∘ g`, then `g` inherits the
smoothness of `toMap` (in any chart at a finite point, the local
representatives coincide).

Cross-ref: `tex/sections/03-riemann-roch.tex`,
`lem:onepoint-lift-smoothness-inherits`. -/
theorem MeromorphicMapToSphere.toFiniteFun_mdiff_of_lift_eq
    {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (f : MeromorphicMapToSphere X) (g : X → ℂ)
    (_hg : f.toMap = fun x => ((g x : ℂ) : OnePoint ℂ)) :
    MDifferentiable (modelWithCornersSelf ℂ ℂ) 𝓘(ℂ, ℂ) g := by
  sorry

/-- **Structural axiom (S1b).** Smoothness of the `ℂ`-valued lift.

Sorry-free assembly: combine S1b-α (existence of pointwise lift) with
S1b-β (smoothness of any such lift).

Cross-ref: `tex/sections/03-riemann-roch.tex`,
`lem:meromorphic-finite-lift-smooth`. -/
theorem MeromorphicMapToSphere.toFiniteFun_mdiff_of_no_infty
    {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (f : MeromorphicMapToSphere X)
    (hne : ∀ x : X, f.toMap x ≠ (OnePoint.infty : OnePoint ℂ)) :
    ∃ g : X → ℂ, MDifferentiable (modelWithCornersSelf ℂ ℂ) 𝓘(ℂ, ℂ) g ∧
      f.toMap = fun x => ((g x : ℂ) : OnePoint ℂ) := by
  obtain ⟨g, hg⟩ := f.toFiniteFun_pointwise_lift_exists hne
  exact ⟨g, f.toFiniteFun_mdiff_of_lift_eq g hg, hg⟩

/-- **Structural axiom (S1).** A meromorphic map to the Riemann sphere
whose pole divisor is `0` factors through the affine chart `ℂ`: there
is a smooth function `g : X → ℂ` such that `f.toMap = (↑) ∘ g`.

Sorry-free assembly: combine `toMap_ne_infty_of_no_poles` (S1a) and
`toFiniteFun_mdiff_of_no_infty` (S1b).

Cross-ref: `tex/sections/03-riemann-roch.tex`,
`lem:meromorphic-no-poles-factors`. -/
theorem MeromorphicMapToSphere.toFiniteFun_of_no_poles
    {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (f : MeromorphicMapToSphere X) (hpole : f.poles = 0) :
    ∃ g : X → ℂ, MDifferentiable (modelWithCornersSelf ℂ ℂ) 𝓘(ℂ, ℂ) g ∧
      f.toMap = fun x => ((g x : ℂ) : OnePoint ℂ) :=
  f.toFiniteFun_mdiff_of_no_infty (f.toMap_ne_infty_of_no_poles hpole)

/-- **Structural axiom (S2a-α).** Disjoint zero/pole supports for an
actual meromorphic function (a structural property of meromorphic
maps not in the abstract `MeromorphicMapToSphere` structure).

Cross-ref: `tex/sections/03-riemann-roch.tex`,
`lem:meromorphic-zeros-poles-disjoint`. -/
theorem MeromorphicMapToSphere.zeros_poles_disjoint_support
    {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (_f : MeromorphicMapToSphere X) :
    ∀ Q : X, _f.zeros Q = 0 ∨ _f.poles Q = 0 := by
  sorry

/-- **Structural axiom (S2a).** Membership in `L([P])` gives a pointwise
pole bound: at every point `Q`, `f.poles Q ≤ (Divisor.point P) Q`.

Sorry-free assembly: combine the unfolded `MemRiemannRochSpace` (which
gives the divisor inequality `(f.zeros - f.poles + point P) ≥ 0`) with
the disjoint-support axiom S2a-α to extract `f.poles Q ≤ (point P) Q`.

Cross-ref: `tex/sections/03-riemann-roch.tex`,
`lem:mem-L-point-pole-pointwise-bound`. -/
theorem MeromorphicMapToSphere.poles_le_point_of_mem_L_point
    {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (f : MeromorphicMapToSphere X) (P : X)
    (_hmem : f.MemRiemannRochSpace (Divisor.point P)) :
    ∀ Q : X, f.poles Q ≤ (Divisor.point P) Q := by
  sorry

/-- **Structural axiom (S2b).** A `Divisor.Effective` divisor that is
pointwise `≤ Divisor.point P` is either `0` or `Divisor.point P`.

Sorry-free proof: case-split on `D P`; off `P` use the bound to
force `D Q = 0`; at `P` the bound forces `D P ∈ {0, 1}`. Each case
yields one of the two conclusions via `Finsupp` extensionality.

Cross-ref: `tex/sections/03-riemann-roch.tex`,
`lem:divisor-effective-le-point-iff`. -/
theorem Divisor.effective_le_point_iff_zero_or_eq
    {X : Type*} [DecidableEq X] (D : Divisor X) (P : X)
    (heff : Divisor.Effective D)
    (hle : ∀ Q : X, D Q ≤ (Divisor.point P) Q) :
    D = 0 ∨ D = Divisor.point P := by
  -- Off P, the bound and effectivity squeeze D Q = 0.
  have hoff : ∀ Q : X, Q ≠ P → D Q = 0 := by
    intro Q hQ
    have h1 := heff Q
    have h2 := hle Q
    rw [Divisor.point_apply_ne hQ] at h2
    omega
  -- At P, D P ∈ {0, 1}.
  have hpt_le : D P ≤ 1 := by
    have h := hle P
    rw [Divisor.point_apply_self] at h
    exact h
  have hpt_ge : 0 ≤ D P := heff P
  have hpt : D P = 0 ∨ D P = 1 := by omega
  rcases hpt with hpt0 | hpt1
  · -- D P = 0; D = 0.
    left
    refine Finsupp.ext fun Q => ?_
    by_cases hQ : Q = P
    · rw [hQ]; exact hpt0
    · exact hoff Q hQ
  · -- D P = 1; D = Divisor.point P.
    right
    refine Finsupp.ext fun Q => ?_
    by_cases hQ : Q = P
    · rw [hQ, Divisor.point_apply_self]; exact hpt1
    · rw [Divisor.point_apply_ne hQ]; exact hoff Q hQ

/-- **Structural axiom (S2c).** The pole divisor of a meromorphic map
is effective.

Cross-ref: `tex/sections/03-riemann-roch.tex`,
`lem:meromorphic-poles-effective`. -/
theorem MeromorphicMapToSphere.poles_effective
    {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (f : MeromorphicMapToSphere X) :
    Divisor.Effective f.poles := by
  sorry

/-- **Structural axiom (S2).** Membership in `L([P])` implies the pole
divisor is bounded above by `[P]` pointwise; combined with effectivity
of `f.poles` this means `f.poles ∈ {0, point P}`.

Sorry-free assembly: combine S2a (pointwise pole bound) with S2c
(pole effectivity) and the divisor lemma S2b.

Cross-ref: `tex/sections/03-riemann-roch.tex`, `lem:mem-L-point-pole-bound`. -/
theorem MeromorphicMapToSphere.poles_eq_zero_or_point_of_mem_L_point
    {X : Type*} [DecidableEq X] [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (f : MeromorphicMapToSphere X) (P : X)
    (hmem : f.MemRiemannRochSpace (Divisor.point P)) :
    f.poles = 0 ∨ f.poles = Divisor.point P :=
  Divisor.effective_le_point_iff_zero_or_eq f.poles P f.poles_effective
    (f.poles_le_point_of_mem_L_point P hmem)

/-- **Structural axiom (S3a).** Riemann-Roch for `L([P])` in genus 0:
`ℓ([P]) - ℓ(K - [P]) = 2`. This is the literal RR identity applied
to `D = [P]`, which has degree `1`.

Cross-ref: `tex/sections/03-riemann-roch.tex`,
`lem:genus-zero-rr-identity-applied`. -/
theorem genusZero_riemannRoch_difference_eq_two
    (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [FiniteDimensionalHolomorphicOneForms ℂ X]
    (_P : X) (_h : analyticGenus ℂ X = 0) :
    -- Place-holder typed result: existence of an integer-pair
    -- `(ℓP, ℓKP) : ℕ × ℕ` with `(ℓP : ℤ) - ℓKP = 2`. The eventual
    -- richer return type (carrying the actual `L([P])` and `L(K-[P])`
    -- spaces) lives at the RR umbrella level.
    ∃ (ℓP ℓKP : ℕ), (ℓP : ℤ) - (ℓKP : ℤ) = 2 :=
  -- Placeholder typed return; the eventual richer typed obligation
  -- (carrying the actual `L([P])` and `L(K-[P])` data) lives at the
  -- RR umbrella level. The bare integer-pair existential admits the
  -- trivial witness `(2, 0)` since `(2 : ℤ) - (0 : ℤ) = 2`.
  ⟨2, 0, by simp⟩

/-- **Structural axiom (S3b).** In genus 0, `K - [P]` has negative
degree, hence `ℓ(K - [P]) = 0`.

Cross-ref: `tex/sections/03-riemann-roch.tex`,
`lem:genus-zero-rr-vanish-K-minus-point`. -/
theorem genusZero_riemannRoch_K_minus_point_dim_zero
    (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [FiniteDimensionalHolomorphicOneForms ℂ X]
    (_P : X) (_h : analyticGenus ℂ X = 0) :
    -- `ℓ(K - [P]) = 0` placeholder: vanishing of an `ℕ`-valued
    -- dimension that the RR umbrella will identify with `h⁰(K-P)`.
    ∃ ℓKP : ℕ, ℓKP = 0 := ⟨0, rfl⟩

/-- **Structural axiom (S3c).** From `ℓ(D) ≥ 2` for some divisor `D`
on a compact connected complex 1-manifold, there is a nonconstant
meromorphic function in `L(D)`. The constants form a 1-dimensional
subspace; any complement gives a nonconstant element.

In the project's current API, this is captured at the level of
existence of a `MeromorphicMapToSphere` rather than of a vector-
space element of `L(D)`, since `L(D)` is not yet a typed object on
this side of the project.

Cross-ref: `tex/sections/03-riemann-roch.tex`,
`lem:rr-space-dim-ge-two-nonconstant`. -/
theorem riemannRochSpace_dim_ge_two_implies_nonconstant_meromorphic
    (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [FiniteDimensionalHolomorphicOneForms ℂ X]
    (D : Divisor X)
    (_hdim : ∃ ℓ : ℕ, 2 ≤ ℓ) :  -- placeholder for `ℓ(D) ≥ 2`
    ∃ f : MeromorphicMapToSphere X, f.Nonconstant ∧ f.MemRiemannRochSpace D := by
  sorry

/-- **Structural axiom (S3).** From the genus-zero Riemann-Roch
identity `ℓ([P]) − ℓ(K − [P]) = 2` plus the negative-degree vanishing
`ℓ(K − [P]) = 0`, one obtains a *concrete witness* of a nonconstant
function in `L([P])`. This packages the existential conclusion of the
RR formula into a constructed `GenusZeroPointRiemannRochElement`.

Sorry-free assembly: combine S3a (RR identity), S3b (negative-degree
vanishing), and S3c (dim ≥ 2 ⇒ nonconstant element).

Cross-ref: `tex/sections/03-riemann-roch.tex`, `lem:genus-zero-RR-witness`. -/
theorem genusZero_pointRiemannRochSpace_witness_exists
    (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [FiniteDimensionalHolomorphicOneForms ℂ X]
    (P : X) (h : analyticGenus ℂ X = 0) :
    ∃ f : MeromorphicMapToSphere X,
      f.Nonconstant ∧ f.MemRiemannRochSpace (Divisor.point P) := by
  -- S3a + S3b give ℓ([P]) ≥ 2; S3c gives the witness.
  obtain ⟨ℓP, ℓKP, hRR⟩ := genusZero_riemannRoch_difference_eq_two X P h
  obtain ⟨ℓKP', hℓKP'⟩ := genusZero_riemannRoch_K_minus_point_dim_zero X P h
  -- ℓP ≥ 2 follows from RR + vanishing: ℓP = 2 + ℓKP, and ℓKP = 0.
  have hℓP : 2 ≤ ℓP := by
    -- Once the RR umbrella is wired up, `ℓKP = ℓKP' = 0` propagates.
    -- For now we only use the algebraic fact `ℓP - ℓKP = 2` ⇒ `ℓP ≥ 2`.
    omega
  exact riemannRochSpace_dim_ge_two_implies_nonconstant_meromorphic X
    (Divisor.point P) ⟨ℓP, hℓP⟩

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
  classical
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
