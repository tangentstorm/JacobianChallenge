import Jacobian.HolomorphicForms.RiemannRoch

/-!
# Degree of meromorphic maps to the Riemann sphere

This module names the second production interface needed by the genus-zero
classification proof: a meromorphic map with pole divisor `[P]` promotes to a
continuous bijection `X → OnePoint ℂ`.
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

/-- **Extension-continuity leaf.** A meromorphic map to the Riemann sphere
with pole divisor `[P]` extends continuously over the pole.

Bottom-up content: prove the local removable-singularity/one-point extension
statement in charts and glue over the compact surface. -/
theorem meromorphicMapToSphere_continuous_of_poleDivisor_point
    (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (f : MeromorphicMapToSphere X) (P : X)
    (_hpole : f.poles = Divisor.point P) :
    Continuous f.toMap := by
  -- BLOCKER: `MeromorphicMapToSphere.toMap` is an unconstrained function `X → OnePoint ℂ`;
  -- `locally_meromorphic` is a bare `Prop` placeholder carrying no analytic content, and
  -- `poleDivisor` is an arbitrary `Divisor X` with no proven link to the map.  Consequently,
  -- one can construct a counterexample (discontinuous `toMap` with `poleDivisor = point P`),
  -- making this theorem unprovable from the current definitions.
  -- Missing piece: `MeromorphicMapToSphere` needs either a `Continuous toMap` field or
  -- genuine meromorphic data (e.g. via Mathlib's `MeromorphicAt` API) connecting `toMap`
  -- to its divisors, so that continuity can be derived from the local removable-singularity
  -- theorem.
  sorry

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

/-- **Degree-one bijectivity leaf.** A continuous meromorphic map to
`OnePoint ℂ` whose pole divisor has degree one is bijective.

Bottom-up content: prove map degree equals pole-divisor degree, then use
degree-one fiber counting and ramification theory to obtain bijectivity. -/
theorem meromorphicMapToSphere_bijective_of_poleDivisor_degree_one
    (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (f : MeromorphicMapToSphere X)
    (_hcont : Continuous f.toMap)
    (_hdegree : Divisor.degree f.poles = 1) :
    Function.Bijective f.toMap := by
  -- BLOCKER: This theorem is *false* under the current definitions.
  --
  -- `MeromorphicMapToSphere` (defined in Meromorphic.lean) has `toMap` and
  -- `poleDivisor` as independent, unconstrained fields.  One can construct a
  -- constant continuous map with `poleDivisor = Divisor.point P` (degree 1),
  -- giving `Continuous f.toMap` and `Divisor.degree f.poles = 1` while
  -- `f.toMap` is trivially non-bijective.
  --
  -- Missing declarations needed in `MeromorphicMapToSphere`:
  --   1. `MeromorphicMapToSphere.toMap_meromorphicAt` — a field/axiom
  --      ensuring `toMap` is genuinely meromorphic (via Mathlib's
  --      `MeromorphicAt` or an equivalent local chart condition), replacing
  --      the bare `locally_meromorphic : Prop`.
  --   2. `MeromorphicMapToSphere.poleDivisor_eq_preimage_infty` — a
  --      field/axiom ensuring `poleDivisor` faithfully records the preimage
  --      of `∞` with multiplicities (e.g.,
  --      `∀ x, poleDivisor x = orderAt f x ∞`).
  --   3. Degree theory for proper holomorphic maps (fiber cardinality =
  --      degree counted with multiplicity) — likely as a standalone theorem
  --      once (1) and (2) are in place.
  sorry

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
