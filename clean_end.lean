      degree_one_data := ⟨_f.meromorphicMap, rfl, ⟨data⟩⟩ }⟩

/-- **Properness/degree data assembly.** Extracts the degree-one promotion
from the named existence leaf. -/
noncomputable def properDegreeOneMapOfSimplePole
    (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [FiniteDimensionalHolomorphicOneForms ℂ X]
    (f : GenusZeroSimplePoleMeromorphicMap X) :
    GenusZeroProperDegreeOneMap X :=
  Classical.choice (properDegreeOneMapOfSimplePole_nonempty X f)

/-- **Sub-obligation 2 wrapper (sorry-free).** Existence form of
`properDegreeOneMapOfSimplePole`. -/
theorem simplePole_meromorphicMap_proper_degreeOne
    (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [FiniteDimensionalHolomorphicOneForms ℂ X]
    (f : GenusZeroSimplePoleMeromorphicMap X) :
    Nonempty (GenusZeroProperDegreeOneMap X) := by
  exact ⟨properDegreeOneMapOfSimplePole X f⟩

/-- **Sub-obligation 3 (degree one implies parametrization).** A proper
degree-one meromorphic map from a compact connected Riemann surface to
`OnePoint ℂ` is a biholomorphic parametrization.

Bottom-up content: a holomorphic map of degree one is bijective with
nonvanishing local degree, hence a biholomorphism; forgetting the analytic
structure gives the recorded homeomorphism. -/
theorem proper_degreeOne_meromorphicMap_biholomorphic
    (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [FiniteDimensionalHolomorphicOneForms ℂ X]
    (f : GenusZeroProperDegreeOneMap X) :
    Nonempty (GenusZeroBiholomorphicParametrization X) := by
  let e : X ≃ OnePoint ℂ := Equiv.ofBijective f.toMap f.bijective_toMap
  have he : Continuous e := by
    simpa [e] using f.continuous_toMap
  exact ⟨⟨he.homeoOfEquivCompactToT2⟩⟩

/-- **Uniformization (genus zero):** a compact connected Riemann surface
with `analyticGenus = 0` is homeomorphic to the one-point
compactification of `ℂ`.

Pure assembly of the three Riemann-Roch route leaves above:
simple-pole meromorphic function, proper degree-one map, and degree-one
biholomorphic parametrization. -/
theorem genus_zero_homeomorph_onePointCx
    (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [FiniteDimensionalHolomorphicOneForms ℂ X]
    (h : analyticGenus ℂ X = 0) :
    Nonempty (X ≃ₜ OnePoint ℂ) := by
  let ⟨f⟩ := genus_zero_exists_simplePole_meromorphicMap X h
  let ⟨g⟩ := simplePole_meromorphicMap_proper_degreeOne X f
  let ⟨b⟩ := proper_degreeOne_meromorphicMap_biholomorphic X g
  exact ⟨b.toHomeomorph⟩

/-- The "hard" direction: if `analyticGenus ℂ X = 0` then `X` is
homeomorphic to the standard 2-sphere.

Decomposes into two obligations:
1. `genus_zero_homeomorph_onePointCx` — Riemann-Roch route assembly through
   simple-pole existence, proper degree-one map, and biholomorphic
   parametrization.
2. `onePointCx_homeomorph_sphere` — the standard homeomorphism
   `OnePoint ℂ ≃ₜ S²` via inverse stereographic projection (proved
   sorry-free using `onePointEquivSphereOfFinrankEq`). -/
theorem homeomorphic_sphere_of_analyticGenus_eq_zero
    (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [FiniteDimensionalHolomorphicOneForms ℂ X]
    (_h : analyticGenus ℂ X = 0) :
    Nonempty (X ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :=
  let ⟨e⟩ := genus_zero_homeomorph_onePointCx X _h
  ⟨e.trans onePointCx_homeomorph_sphere⟩

/-- A compact connected Riemann surface has analytic genus zero iff it is
homeomorphic to the standard 2-sphere.

Pure assembly of the two directions
`analyticGenus_eq_zero_of_homeomorphic_sphere` and
`homeomorphic_sphere_of_analyticGenus_eq_zero`; this declaration adds
no new sorry. -/
theorem analyticGenus_eq_zero_iff_homeomorphic_sphere
    (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [FiniteDimensionalHolomorphicOneForms ℂ X] :
    analyticGenus ℂ X = 0 ↔
      Nonempty (X ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :=
  ⟨homeomorphic_sphere_of_analyticGenus_eq_zero X,
   analyticGenus_eq_zero_of_homeomorphic_sphere X⟩

end JacobianChallenge.HolomorphicForms
