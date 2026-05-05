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

/-- **Structural axiom (M1).** Restricted to the complement of the
single-pole locus `{P}`, the meromorphic map agrees with a smooth
`X \ {P} → ℂ` that is continuous (in fact `ContMDiff`) and lifts
through `OnePoint.some`.

Bottom-up: `f.toMap x ≠ ∞` for `x ≠ P`; this lift is then the
chart expression of `f` away from the pole.

Cross-ref: `tex/sections/03-riemann-roch.tex`,
`lem:meromorphic-continuous-off-pole`. -/
theorem MeromorphicMapToSphere.continuousOn_compl_pole_of_poleDivisor_point
    {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (f : MeromorphicMapToSphere X) (P : X)
    (_hpole : f.poles = Divisor.point P) :
    ContinuousOn f.toMap {P}ᶜ := by
  sorry

/-- **Structural axiom (M2).** Near a simple pole `P`, the meromorphic
map tends to `∞ : OnePoint ℂ`. This is the local-Laurent / one-point
extension statement: in any chart at `P`, the map locally looks like
`z ↦ a/z + (holomorphic)` with `a ≠ 0`, hence diverges; the
`OnePoint` topology converts divergence to `∞`-convergence.

Cross-ref: `tex/sections/03-riemann-roch.tex`,
`lem:meromorphic-tends-to-infty-at-simple-pole`. -/
theorem MeromorphicMapToSphere.tendsto_infty_at_pole_of_poleDivisor_point
    {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (f : MeromorphicMapToSphere X) (P : X)
    (_hpole : f.poles = Divisor.point P) :
    Filter.Tendsto f.toMap (nhds P) (nhds (OnePoint.infty : OnePoint ℂ)) := by
  sorry

/-- **Structural axiom (M3).** A meromorphic map whose only pole is at
`P` actually evaluates to `∞ : OnePoint ℂ` at `P`. This is the
"value-at-pole" axiom — the structural data linking the abstract
`poleDivisor` to the concrete `toMap` at the pole.

Cross-ref: `tex/sections/03-riemann-roch.tex`,
`lem:meromorphic-value-at-pole`. -/
theorem MeromorphicMapToSphere.toMap_pole_eq_infty_of_poleDivisor_point
    {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (f : MeromorphicMapToSphere X) (P : X)
    (_hpole : f.poles = Divisor.point P) :
    f.toMap P = (OnePoint.infty : OnePoint ℂ) := by
  sorry

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

/-- **Structural axiom (M4).** A continuous meromorphic map of degree 1
between compact connected complex 1-manifolds is **surjective**.

Bottom-up: the image is compact (continuous image of compact), and
has nonempty interior (since the map is open on the complement of
the ramification locus, which has measure zero in degree 1 — in
fact, no ramification at all in degree 1). A nonempty compact set
with nonempty interior is everything.

Cross-ref: `tex/sections/04-branched-covers-genus-zero.tex`,
`lem:degree-one-surjective`. -/
theorem MeromorphicMapToSphere.surjective_of_continuous_and_pole_degree_one
    {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (f : MeromorphicMapToSphere X)
    (_hcont : Continuous f.toMap)
    (_hdegree : Divisor.degree f.poles = 1) :
    Function.Surjective f.toMap := by
  sorry

/-- **Structural axiom (M5).** A continuous meromorphic map of degree 1
between compact connected complex 1-manifolds is **injective**.

Bottom-up: degree 1 means the generic fiber has cardinality 1; with
no ramification (degree 1 cannot have ramification), this extends
to global injectivity.

Cross-ref: `tex/sections/04-branched-covers-genus-zero.tex`,
`lem:degree-one-injective`. -/
theorem MeromorphicMapToSphere.injective_of_continuous_and_pole_degree_one
    {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (f : MeromorphicMapToSphere X)
    (_hcont : Continuous f.toMap)
    (_hdegree : Divisor.degree f.poles = 1) :
    Function.Injective f.toMap := by
  sorry

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
