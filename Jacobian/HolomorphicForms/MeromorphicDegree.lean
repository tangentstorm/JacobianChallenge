import Jacobian.HolomorphicForms.RiemannRoch

/-!
# Degree of meromorphic maps to the Riemann sphere

This module names the second production interface needed by the genus-zero
classification proof: a meromorphic map with pole divisor `[P]` promotes to a
continuous bijection `X → OnePoint ℂ`.

The two headline obligations now decompose into smaller named
structural companions, mirroring the TeX decomposition in
`tex/sections/03-riemann-roch.tex` and
`tex/sections/04-branched-covers-genus-zero.tex` (`§Degree-one
classification`).
-/

namespace JacobianChallenge.HolomorphicForms

open scoped Manifold

/-- Degree data for a meromorphic map to the Riemann sphere.

The current downstream consumer only needs continuity and bijectivity.  The
`degree_eq_pole_degree` field records the future divisor-degree theorem that
explains why these consequences hold. -/
structure MeromorphicDegreeOneData
    (X : Type*) [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (f : MeromorphicMapToSphere X) where
  continuous_toMap : Continuous f.toMap
  bijective_toMap : Function.Bijective f.toMap
  degree_eq_pole_degree : Divisor.degree f.poles = 1

/-! ### Structural companions for the continuity step

The continuity of a meromorphic-map-to-sphere across a single pole is
the classical *removable-singularity / one-point extension* statement:
the pole-locus complement carries a smooth `ℂ`-valued function, and
the limit at the pole equals `∞ : OnePoint ℂ`.
-/

/-- **Structural axiom (M1a).** Off the single pole `P`, the map
takes finite values: `∀ x ≠ P, f.toMap x ≠ ∞`.

Cross-ref: `tex/sections/04-branched-covers-genus-zero.tex`,
`lem:meromorphic-no-infty-off-pole`. -/
theorem MeromorphicMapToSphere.toMap_ne_infty_off_pole
    {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (f : MeromorphicMapToSphere X) (P : X)
    (_hpole : f.poles = Divisor.point P) :
    ∀ x : X, x ≠ P → f.toMap x ≠ (OnePoint.infty : OnePoint ℂ) := by
  sorry

/-- **Structural axiom (M1b).** Off any locus where `f.toMap` is
finite, the map is continuous: in any chart at a finite point,
`f.toMap` agrees (via `OnePoint.some`) with a smooth `ℂ`-valued
function, which is continuous.

Cross-ref: `tex/sections/04-branched-covers-genus-zero.tex`,
`lem:meromorphic-continuous-on-finite-set`. -/
theorem MeromorphicMapToSphere.continuousOn_of_no_infty_on
    {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (f : MeromorphicMapToSphere X) (S : Set X)
    (_hne : ∀ x ∈ S, f.toMap x ≠ (OnePoint.infty : OnePoint ℂ)) :
    ContinuousOn f.toMap S := by
  sorry

/-- **Structural axiom (M1).** Restricted to the complement of the
single-pole locus `{P}`, the meromorphic map is continuous.

Sorry-free assembly: combine M1a (no-∞ off pole) with M1b
(continuity from no-∞).

Cross-ref: `tex/sections/04-branched-covers-genus-zero.tex`,
`lem:meromorphic-continuous-off-pole`. -/
theorem MeromorphicMapToSphere.continuousOn_compl_pole_of_poleDivisor_point
    {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (f : MeromorphicMapToSphere X) (P : X)
    (hpole : f.poles = Divisor.point P) :
    ContinuousOn f.toMap {P}ᶜ :=
  f.continuousOn_of_no_infty_on {P}ᶜ
    (fun x hx => f.toMap_ne_infty_off_pole P hpole x hx)

/-- **Structural axiom (M3).** A meromorphic map whose only pole is at
`P` actually evaluates to `∞ : OnePoint ℂ` at `P`.

Cross-ref: `tex/sections/04-branched-covers-genus-zero.tex`,
`lem:meromorphic-value-at-pole`. -/
theorem MeromorphicMapToSphere.toMap_pole_eq_infty_of_poleDivisor_point
    {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (f : MeromorphicMapToSphere X) (P : X)
    (_hpole : f.poles = Divisor.point P) :
    f.toMap P = (OnePoint.infty : OnePoint ℂ) := by
  sorry

/-- **Structural axiom (M2a).** A meromorphic map with a simple pole
at `P` has a *finite-pre-image lift* `g : X \ {P} → ℂ` such that
`f.toMap = OnePoint.some ∘ g` on `{P}ᶜ`, and `‖g x‖ → ∞` as
`x → P`.

This is the local-Laurent diverging-modulus content.

Cross-ref: `tex/sections/04-branched-covers-genus-zero.tex`,
`lem:simple-pole-modulus-diverges`. -/
theorem MeromorphicMapToSphere.modulus_diverges_at_simple_pole
    {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (f : MeromorphicMapToSphere X) (P : X)
    (_hpole : f.poles = Divisor.point P) :
    ∃ g : X → ℂ,
      (∀ x : X, x ≠ P → f.toMap x = ((g x : ℂ) : OnePoint ℂ)) ∧
      Filter.Tendsto (fun x => ‖g x‖) (nhdsWithin P {P}ᶜ) Filter.atTop := by
  sorry

/-- **Structural axiom (M2b).** A `ℂ`-valued function whose modulus
diverges at a punctured nhd of `P`, lifted to `OnePoint ℂ` via
`some`, tends to `∞` at `P`.

Cross-ref: `tex/sections/04-branched-covers-genus-zero.tex`,
`lem:onepoint-tendsto-infty-of-modulus-diverges`. -/
theorem OnePoint.tendsto_infty_of_modulus_diverges
    {X : Type*} [TopologicalSpace X] (P : X)
    (g : X → ℂ)
    (_hdiv : Filter.Tendsto (fun x => ‖g x‖) (nhdsWithin P {P}ᶜ) Filter.atTop) :
    Filter.Tendsto (fun x => ((g x : ℂ) : OnePoint ℂ))
      (nhdsWithin P {P}ᶜ) (nhds (OnePoint.infty : OnePoint ℂ)) := by
  sorry

/-- **Structural axiom (M2).** Near a simple pole `P`, the meromorphic
map tends to `∞ : OnePoint ℂ`. Sorry-free assembly: combine M2a
(modulus divergence on the punctured nhd) with M2b (modulus → `∞`
in `OnePoint`), plus M3 (value at the pole) via the
`nhds = nhdsWithin {P} ⊔ nhdsWithin {P}ᶜ` decomposition.

Cross-ref: `tex/sections/04-branched-covers-genus-zero.tex`,
`lem:meromorphic-tends-to-infty-at-simple-pole`. -/
theorem MeromorphicMapToSphere.tendsto_infty_at_pole_of_poleDivisor_point
    {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (f : MeromorphicMapToSphere X) (P : X)
    (hpole : f.poles = Divisor.point P) :
    Filter.Tendsto f.toMap (nhds P) (nhds (OnePoint.infty : OnePoint ℂ)) := by
  -- Step 1: punctured-nhd version via M2a + M2b.
  obtain ⟨g, hgeq, hdiv⟩ := f.modulus_diverges_at_simple_pole P hpole
  have hp_lim : Filter.Tendsto f.toMap (nhdsWithin P {P}ᶜ)
      (nhds (OnePoint.infty : OnePoint ℂ)) := by
    refine (OnePoint.tendsto_infty_of_modulus_diverges P g hdiv).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact (hgeq x hx).symm
  -- Step 2: at P, f.toMap P = ∞ (M3).
  have h_at : f.toMap P = (OnePoint.infty : OnePoint ℂ) :=
    f.toMap_pole_eq_infty_of_poleDivisor_point P hpole
  -- Step 3: combine via `nhds = pure ⊔ punctured`.
  have h_decomp : nhds P = nhdsWithin P {P} ⊔ nhdsWithin P {P}ᶜ :=
    nhds_eq_nhdsWithin_sup_nhdsWithin P (by simp)
  rw [h_decomp, Filter.tendsto_sup]
  refine ⟨?_, hp_lim⟩
  -- On `nhdsWithin P {P} = pure P`, tendsto follows from f P = ∞.
  rw [nhdsWithin_singleton]
  -- `Tendsto f (pure P) (nhds ∞)` reduces to `f P ∈ nhds ∞`, which holds since f P = ∞.
  -- `f P = ∞` gives `Tendsto f (pure P) (nhds ∞)` after substituting f P.
  have := tendsto_pure_nhds f.toMap P
  rw [h_at] at this
  exact this

/-- **Extension-continuity leaf.** A meromorphic map to the Riemann sphere
with pole divisor `[P]` extends continuously over the pole.

Sorry-free assembly: continuity is local; the pole-complement gives
M1, the pole-locus is a single point and M2 supplies the limit at
`P`. Use `continuousOn_iff_continuous_compl` (or the open-cover
gluing of `Continuous`). -/
theorem meromorphicMapToSphere_continuous_of_poleDivisor_point
    (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (f : MeromorphicMapToSphere X) (P : X)
    (hpole : f.poles = Divisor.point P) :
    Continuous f.toMap := by
  -- Strategy: continuity at P follows from M2; continuity off P follows from M1.
  rw [continuous_iff_continuousAt]
  intro x
  by_cases hx : x = P
  · -- At the pole P, use M3 (toMap = ∞ at pole) and M2 (tendsto to ∞).
    rw [hx]
    have h_at_pole : f.toMap P = (OnePoint.infty : OnePoint ℂ) :=
      f.toMap_pole_eq_infty_of_poleDivisor_point P hpole
    rw [ContinuousAt, h_at_pole]
    exact f.tendsto_infty_at_pole_of_poleDivisor_point P hpole
  · -- Off the pole, use M1.
    have hcont_on : ContinuousOn f.toMap {P}ᶜ :=
      f.continuousOn_compl_pole_of_poleDivisor_point P hpole
    have hopen : IsOpen ({P}ᶜ : Set X) := isOpen_compl_singleton
    exact (hcont_on.continuousAt (hopen.mem_nhds hx))

/-- **Degree bookkeeping leaf.** If the pole divisor is `[P]`, then its
degree is one. -/
theorem meromorphicMapToSphere_poleDivisor_degree_eq_one_of_point
    {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (f : MeromorphicMapToSphere X) (P : X)
    (hpole : f.poles = Divisor.point P) :
    Divisor.degree f.poles = 1 := by
  rw [hpole]
  exact Divisor.degree_point P

/-! ### Structural companions for the bijectivity step -/

/-- **Structural axiom (M4a).** The image of a continuous map from a
compact space is compact (purely topological; routes through Mathlib's
`IsCompact.image`). -/
theorem MeromorphicMapToSphere.image_isCompact
    {X : Type*} [TopologicalSpace X] [CompactSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (f : MeromorphicMapToSphere X)
    (hcont : Continuous f.toMap) :
    IsCompact (Set.range f.toMap) :=
  isCompact_range hcont

/-- **Structural axiom (M4b).** A meromorphic map of degree 1 is open
(no ramification at degree 1).

Cross-ref: `tex/sections/04-branched-covers-genus-zero.tex`,
`lem:degree-one-open-map`. -/
theorem MeromorphicMapToSphere.isOpenMap_of_pole_degree_one
    {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (f : MeromorphicMapToSphere X)
    (_hcont : Continuous f.toMap)
    (_hdegree : Divisor.degree f.poles = 1) :
    IsOpenMap f.toMap := by
  sorry

/-- **Structural axiom (M4).** A continuous meromorphic map of degree 1
between compact connected complex 1-manifolds is **surjective**.

Sorry-free assembly: the image is compact (M4a) and open (M4b);
since `OnePoint ℂ` is connected, a nonempty clopen set is the whole
space.

Cross-ref: `tex/sections/04-branched-covers-genus-zero.tex`,
`lem:degree-one-surjective`. -/
theorem MeromorphicMapToSphere.surjective_of_continuous_and_pole_degree_one
    {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X] [Nonempty X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (f : MeromorphicMapToSphere X)
    (hcont : Continuous f.toMap)
    (hdegree : Divisor.degree f.poles = 1) :
    Function.Surjective f.toMap := by
  -- range f is nonempty, compact (M4a), open (M4b's image of univ).
  have hopenmap : IsOpenMap f.toMap :=
    f.isOpenMap_of_pole_degree_one hcont hdegree
  have hrange_open : IsOpen (Set.range f.toMap) := by
    rw [← Set.image_univ]
    exact hopenmap _ isOpen_univ
  have hrange_compact : IsCompact (Set.range f.toMap) := f.image_isCompact hcont
  have hrange_closed : IsClosed (Set.range f.toMap) := hrange_compact.isClosed
  have hrange_nonempty : (Set.range f.toMap).Nonempty := Set.range_nonempty _
  -- In a connected space, any nonempty clopen is univ.
  have hclopen : IsClopen (Set.range f.toMap) := ⟨hrange_closed, hrange_open⟩
  have hrange_univ : Set.range f.toMap = Set.univ := by
    rcases isClopen_iff.mp hclopen with hempty | huniv
    · exact (hrange_nonempty.ne_empty hempty).elim
    · exact huniv
  exact Set.range_eq_univ.mp hrange_univ

/-- **Structural axiom (M5a).** A pole-degree-1 meromorphic map has
all preimage fibers of cardinality at most 1.

Cross-ref: `tex/sections/04-branched-covers-genus-zero.tex`,
`lem:degree-one-fiber-card-le-one`. -/
theorem MeromorphicMapToSphere.fiber_card_le_one_of_pole_degree_one
    {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (f : MeromorphicMapToSphere X)
    (_hcont : Continuous f.toMap)
    (_hdegree : Divisor.degree f.poles = 1) :
    ∀ y : OnePoint ℂ, ∀ x₁ x₂ : X,
      f.toMap x₁ = y → f.toMap x₂ = y → x₁ = x₂ := by
  sorry

/-- **Structural axiom (M5).** A continuous meromorphic map of degree 1
between compact connected complex 1-manifolds is **injective**.

Sorry-free assembly: directly from M5a. -/
theorem MeromorphicMapToSphere.injective_of_continuous_and_pole_degree_one
    {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (f : MeromorphicMapToSphere X)
    (hcont : Continuous f.toMap)
    (hdegree : Divisor.degree f.poles = 1) :
    Function.Injective f.toMap := by
  intro x₁ x₂ hxx
  exact f.fiber_card_le_one_of_pole_degree_one hcont hdegree
    (f.toMap x₁) x₁ x₂ rfl hxx.symm

/-- **Degree-one bijectivity leaf.** A continuous meromorphic map to
`OnePoint ℂ` whose pole divisor has degree one is bijective.

Sorry-free assembly: combine surjectivity (M4) and injectivity (M5).
-/
theorem meromorphicMapToSphere_bijective_of_poleDivisor_degree_one
    (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (f : MeromorphicMapToSphere X)
    (hcont : Continuous f.toMap)
    (hdegree : Divisor.degree f.poles = 1) :
    Function.Bijective f.toMap :=
  ⟨f.injective_of_continuous_and_pole_degree_one hcont hdegree,
   f.surjective_of_continuous_and_pole_degree_one hcont hdegree⟩

/-- **Degree-one assembly.** A meromorphic map whose pole divisor is `[P]`
has degree one and therefore is continuous and bijective as a map to
`OnePoint ℂ`. -/
theorem meromorphicDegreeOneData_of_poleDivisor_point
    (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (f : MeromorphicMapToSphere X) (P : X)
    (hpole : f.poles = Divisor.point P) :
    Nonempty (MeromorphicDegreeOneData X f) := by
  have hcont : Continuous f.toMap :=
    meromorphicMapToSphere_continuous_of_poleDivisor_point X f P hpole
  have hdegree : Divisor.degree f.poles = 1 :=
    meromorphicMapToSphere_poleDivisor_degree_eq_one_of_point f P hpole
  exact ⟨
    { continuous_toMap := hcont
      bijective_toMap :=
        meromorphicMapToSphere_bijective_of_poleDivisor_degree_one X f hcont hdegree
      degree_eq_pole_degree := hdegree }⟩

end JacobianChallenge.HolomorphicForms
