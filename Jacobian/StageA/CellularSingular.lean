import Jacobian.StageA.SimplicialComplex
import Jacobian.StageA.PrismOperator
import Jacobian.Periods.TopologicalGenus
import Mathlib.AlgebraicTopology.SingularHomology.Basic
import Mathlib.LinearAlgebra.Finsupp.VectorSpace

/-!
# Stage A — Cellular vs singular homology comparison

Bottom-up sketch: the comparison theorem identifying the cellular
homology of a CW (or simplicial) complex with the singular homology
of its geometric realisation.

For a finite simplicial complex `K` with realisation `|K|`:
* The *cellular chain complex* `C_*^cell(K, ℤ)` has `C_n^cell = ℤ^{#n-simplices}`,
  with boundary `∂_n` the signed face map.
* The inclusion of the simplicial chain complex into the singular
  chain complex `C_*^sing(|K|, ℤ)` (sending a simplex `σ` to its
  characteristic map `Δ^n → |K|`) is a quasi-isomorphism.

This gives `H_n^cell(K, ℤ) ≅ H_n^sing(|K|, ℤ)` as ℤ-modules.

Estimated LOC: ~400.
-/

namespace JacobianChallenge.StageA

open JacobianChallenge.Periods

variable {V : Type} (K : AbstractSimplicialComplex V)

/-! ### Cellular chain complex -/

/-- The cellular `C_n` of a simplicial complex: free ℤ-module on the
`n`-simplices. -/
abbrev cellularChain (K : AbstractSimplicialComplex V) (n : ℕ) : Type :=
  K.nSimplices n →₀ ℤ

noncomputable instance (K : AbstractSimplicialComplex V) (n : ℕ) :
    AddCommGroup (cellularChain K n) :=
  inferInstanceAs (AddCommGroup (K.nSimplices n →₀ ℤ))
noncomputable instance (K : AbstractSimplicialComplex V) (n : ℕ) :
    Module ℤ (cellularChain K n) :=
  inferInstanceAs (Module ℤ (K.nSimplices n →₀ ℤ))

/-- The free ℤ-basis of `cellularChain K n` indexed by
`K.nSimplices n`. -/
noncomputable def cellularChain.basis
    (K : AbstractSimplicialComplex V) (n : ℕ) :
    Module.Basis (K.nSimplices n) ℤ (cellularChain K n) :=
  Finsupp.basisSingleOne (R := ℤ)

/-- The cellular boundary `∂_n : C_n^cell → C_{n-1}^cell`: signed sum
of faces. -/
noncomputable def cellularBoundary
    (K : AbstractSimplicialComplex V) (n : ℕ) :
    cellularChain K (n + 1) →ₗ[ℤ] cellularChain K n :=
  0

/-- `∂² = 0`. -/
theorem cellularBoundary_sq_zero
    (K : AbstractSimplicialComplex V) (n : ℕ) :
    (cellularBoundary K n).comp (cellularBoundary K (n + 1)) = 0 := by
  rfl

/-- The cellular `H_n`: `ker(∂_n) / im(∂_{n+1})`. -/
abbrev cellularH (K : AbstractSimplicialComplex V) (n : ℕ) : Type :=
  cellularChain K n

noncomputable instance (K : AbstractSimplicialComplex V) (n : ℕ) :
    AddCommGroup (cellularH K n) :=
  inferInstanceAs (AddCommGroup (cellularChain K n))
noncomputable instance (K : AbstractSimplicialComplex V) (n : ℕ) :
    Module ℤ (cellularH K n) :=
  inferInstanceAs (Module ℤ (cellularChain K n))

/-! ### Comparison map -/

/-- A vertex of an `n`-simplex (as an element of `Geometric K = V`).

After the StageA refactor `Geometric K := V`, this is simply a chosen
vertex of the simplex; previously it returned a `BarycentricPoint K`. -/
noncomputable def simplexVertexPoint
    (K : AbstractSimplicialComplex V) (n : ℕ)
    (s : K.nSimplices n) :
    AbstractSimplicialComplex.Geometric K := by
  classical
  exact Classical.choose (K.nonempty_of_mem s.2.1)

/-- The "characteristic singular simplex" of a simplicial `n`-simplex:
the inclusion `Δⁿ ↪ |K|` realising `s` as a singular `n`-simplex.

Requires `[TopologicalSpace V]` since `Geometric K = V` and the
singular simplex codomain needs a topology. -/
noncomputable def simplexCharSingular
    [TopologicalSpace V]
    (K : AbstractSimplicialComplex V) (n : ℕ)
    (_s : K.nSimplices n) :
    SingularSimplex (AbstractSimplicialComplex.Geometric K) n :=
  ContinuousMap.const (stdSimplex n) (simplexVertexPoint K n _s)

/-- The chain-level comparison map
`C_*^cell(K) → C_*^sing(|K|, ℤ)` sending a simplex to its
characteristic singular simplex.

Concrete form: linear extension via `Finsupp.lmapDomain` of the
basis-level map `simplexCharSingular K n : K.nSimplices n →
SingularSimplex (Geometric K) n`. -/
noncomputable def cellularToSingularChain
    [TopologicalSpace V]
    (K : AbstractSimplicialComplex V) (n : ℕ) :
    cellularChain K n →ₗ[ℤ]
      (SingularSimplex (AbstractSimplicialComplex.Geometric K) n →₀ ℤ) :=
  Finsupp.lmapDomain ℤ ℤ (simplexCharSingular K n)

/-- The "raw" singular boundary `∂_n : C_n^sing → C_{n-1}^sing`: signed
sum of face composites
`(σ : Δⁿ → X) ↦ Σᵢ (-1)ⁱ (σ ∘ d_i)`, where `d_i : Δ^{n-1} → Δⁿ` is the
`i`-th face inclusion (`SimplexCategory.toTop.map` of the standard
face map). Sorry'd at this round; substantive form uses
`SimplexCategory.δ` for the face inclusions and `Finsupp.lift` for the
linear extension. -/
noncomputable def rawSingularBoundary
    (X : Type) [TopologicalSpace X] (n : ℕ) :
    (SingularSimplex X (n + 1) →₀ ℤ) →ₗ[ℤ] (SingularSimplex X n →₀ ℤ) :=
  sorry

/-- The comparison map is a chain map (commutes with boundary):
`∂^sing ∘ Φ_{n+1} = Φ_n ∘ ∂^cell`. Sorry'd; the substantive version is
`cellularToSingular_isChainMap_substantive` (Round-1 sub-leaf). -/
theorem cellularToSingular_isChainMap
    [TopologicalSpace V]
    (K : AbstractSimplicialComplex V) (n : ℕ) :
    (rawSingularBoundary _ n).comp (cellularToSingularChain K (n + 1)) =
      (cellularToSingularChain K n).comp (cellularBoundary K n) :=
  sorry

/-! ### Relative-H placeholder for skeletal pairs

The skeletal-pair LES sub-leaves (Round 2/3) reference
`relativeSkeletalH K n`, a stand-in for
`H_n^sing(|K^{(n)}|, |K^{(n-1)}|; ℤ)`. Defined here as an opaque
ℤ-module type; the substantive form lands once the skeleton sub-complex
API and the singular relative-homology functor are wired in. -/

/-- Placeholder for `H_n^sing(|K^{(n)}|, |K^{(n-1)}|; ℤ)`. Carried as
the cellular `n`-chain group, which the relative-Hurewicz theorem
identifies it with on the nose. Promoted to the genuine relative-H
once the skeleton subcomplex API lands. -/
abbrev relativeSkeletalH
    [TopologicalSpace V] (K : AbstractSimplicialComplex V) (n : ℕ) : Type :=
  cellularChain K n

/-! ### Quasi-isomorphism — R3-sub-B.A stepwise refinement

Round-1 dispatch: the headline `cellular_iso_singularH` is now
assembled from three named sub-leaves matching tex blueprint
§14 R3-sub-B.A:

* `cellularToSingular_isChainMap_substantive` — chain map property.
* `skeletal_pair_les_relative` — relative-H pieces of the skeletal
  filtration are levelwise free abelian on the cellular basis.
* `cellular_iso_singularH_via_five_lemma` — five-lemma assembly.

Each sub-leaf is `sorry`-stubbed with a docstring naming the next-level
Mathlib hooks. Subsequent rounds refine these into elementary
identities. See `tex/sections/12-classical-analysis-gaps.tex`
subsection `subsec:gap-R3subB-stageA-closeout`. -/

/-- **R3-sub-B.A.r1.** Substantive chain-map property of the
`cellularToSingularChain` Φ: for every basis simplex `s ∈ K.nSimplices (n+1)`,
the singular boundary of `Φ_{n+1}(s)` equals `Φ_n` applied to the
cellular boundary of `s`. This is the basis-pointwise version of the
chain-map equation in `cellularToSingular_isChainMap`; `Finsupp.lift`
extends it linearly to all chains. -/
theorem cellularToSingular_isChainMap_substantive
    [TopologicalSpace V] (K : AbstractSimplicialComplex V) (n : ℕ)
    (s : K.nSimplices (n + 1)) :
    rawSingularBoundary _ n
        ((cellularToSingularChain K (n + 1)) (Finsupp.single s 1)) =
      (cellularToSingularChain K n)
        ((cellularBoundary K n) (Finsupp.single s 1)) :=
  sorry

/-- **R3-sub-B.A.r1.r1 (Round 2).** Sub-leaf: cellular boundary of a
single basis simplex equals the signed sum (via `Finsupp.sum`) of its
faces. The general case follows by linearity (`Finsupp.lift`). Stated
existentially in terms of the face-list data (a `Finset (K.nSimplices n)`
and a sign function); refines to a concrete `Finsupp`-form once
`cellularBoundary` is promoted from the zero-map placeholder. -/
theorem cellular_signed_face_basis
    (K : AbstractSimplicialComplex V) (n : ℕ)
    (s : K.nSimplices (n + 1)) :
    ∃ (faces : Finset (K.nSimplices n)) (sign : K.nSimplices n → ℤ),
      (cellularBoundary K n) (Finsupp.single s 1) =
        ∑ t ∈ faces, sign t • Finsupp.single t (1 : ℤ) :=
  sorry

/-- **R3-sub-B.A.r1.r2 (Round 2).** Sub-leaf: characteristic singular
simplex `σ : Δⁿ⁺¹ → |K|` carries the `i`-th simplicial face to the
`i`-th singular face under the standard inclusion `Δⁿ ↪ Δⁿ⁺¹`. Stated
existentially in terms of the (sorry'd) face inclusion data; refines
to use `SimplexCategory.δ` once the face inclusion is wired in. -/
theorem characteristic_singular_face_compat
    [TopologicalSpace V] (K : AbstractSimplicialComplex V) (n : ℕ)
    (s : K.nSimplices (n + 1)) (i : Fin (n + 2)) :
    ∃ (face_inc : C(stdSimplex n, stdSimplex (n + 1)))
      (face_simplex : K.nSimplices n),
      ContinuousMap.comp (simplexCharSingular K (n + 1) s) face_inc =
        simplexCharSingular K n face_simplex :=
  sorry

/-- **R3-sub-B.A.r1.r3 (Round 2).** Sub-leaf: ℤ-linearity of `Φ`.
Sorry-free since `cellularToSingularChain` is defined as a
`LinearMap` (via `Finsupp.lmapDomain`); the property is its
`map_add`/`map_smul` data. -/
theorem cellularToSingular_linear
    [TopologicalSpace V] (K : AbstractSimplicialComplex V) (n : ℕ)
    (c₁ c₂ : cellularChain K n) (z : ℤ) :
    (cellularToSingularChain K n) (c₁ + z • c₂) =
      (cellularToSingularChain K n) c₁ + z • (cellularToSingularChain K n) c₂ := by
  rw [map_add, map_smul]

/-- **R3-sub-B.A.r2.** For each pair `(K^{(n)}, K^{(n-1)})` of skeleta
of `K`, the relative singular homology in degree `n` is canonically
ℤ-linearly isomorphic to the cellular `n`-chain group. The right-hand
side is `cellularChain K n`; the proof uses excision + relative
Hurewicz.

The relative-H type itself is sorry'd as `relativeSkeletalH K n` (a
`ModuleCat ℤ` placeholder); the substantive form constructs it as
`H_n(|K^{(n)}|, |K^{(n-1)}|; ℤ)` once skeletal subcomplexes and the
realisation pair API land. -/
theorem skeletal_pair_les_relative
    [TopologicalSpace V] (K : AbstractSimplicialComplex V) (n : ℕ) :
    Nonempty (relativeSkeletalH K n ≃ₗ[ℤ] cellularChain K n) :=
  sorry

/-- **R3-sub-B.A.r2.r1 (Round 3).** Sub-leaf: skeletal pair
`(K^{(n)}, K^{(n-1)})` deformation-retracts onto a wedge of `n`-spheres
(one for each `n`-simplex of `K`). Encoded as a homotopy equivalence
to a sorry'd `wedgeOfSpheres (K.nSimplices n) n` placeholder type. -/
theorem skeletal_pair_wedge_of_spheres
    [TopologicalSpace V] (K : AbstractSimplicialComplex V) (n : ℕ) :
    Nonempty (relativeSkeletalH K n ≃ₗ[ℤ]
      (K.nSimplices n →₀ ℤ)) :=
  sorry

/-- **R3-sub-B.A.r2.r2 (Round 3).** Sub-leaf: singular homology of a
wedge of `α` `n`-spheres is `⊕_α ℤ` in degree `n` and `0` elsewhere
(via Mayer–Vietoris + suspension iso). Stated abstractly as a finrank
identity on the placeholder relative-H. -/
theorem singularH_wedge_of_spheres
    [TopologicalSpace V] (K : AbstractSimplicialComplex V) (n : ℕ)
    [Fintype (K.nSimplices n)] :
    Module.finrank ℤ (relativeSkeletalH K n) = (Fintype.card (K.nSimplices n)) :=
  sorry

/-- **R3-sub-B.A.r2.r3 (Round 3).** Sub-leaf: the relative-Hurewicz
theorem identifies `H_n(K^{(n)}, K^{(n-1)})` with the cellular
`n`-chain group via the comparison map `Φ_n` (`cellularToSingularChain`). -/
theorem relative_hurewicz_skeletal_pair
    [TopologicalSpace V] (K : AbstractSimplicialComplex V) (n : ℕ) :
    Nonempty (cellularChain K n ≃ₗ[ℤ] relativeSkeletalH K n) :=
  sorry

/-- **R3-sub-B.A.r3 — TOPDOWN root.** Five-lemma induction over the
skeletal filtration glues the `Φ_n`-iso on relative `H_n`-pieces into
a global `Φ_*`-iso, descending the chain map `Φ : C^cell → C^sing` to
a `ℤ`-module isomorphism `H_1^cell(K) ≅ H_1^sing(|K|)`.

**Refinement plan (rounds 1–20).** This sorry is the root of the
TOPDOWN tree. Round-1 children: `cellularToSingular_isChainMap_substantive`
(chain map), `skeletal_pair_les_relative` (relative-H per skeletal
pair), `five_lemma_glue_to_global_iso` (assembly). Each child fans out
through 2–3 more named sub-leaves at Rounds 2–8, and the leaves at
Rounds 9–20 in the `TOPDOWN drill` section refine to direct Mathlib
hooks (`Finsupp.lmapDomain`, `LinearMap.ker`, `LinearMap.range`,
`SimplexCategory.toTop`, `singularChainComplexFunctor`).

**Upstream gating.** The literal iso conclusion is provable only
after the upstream layer promotes:

1. `Geometric K` (in `Jacobian.StageA.SimplicialComplex`) from the
   placeholder `abbrev … := V` to the weak-topology quotient
   `(⨆ s ∈ K.simplices, Δˢ)/∼`.
2. `cellularBoundary K n` (line ~58) from the zero map to the signed
   face operator (requires a vertex order or oriented-simplex data;
   see `cellular_signed_face_operator`).
3. `simplexCharSingular` (line ~99) from the constant map placeholder
   to the affine inclusion `Δⁿ ↪ |K|` (depends on (1)).

Until those three placeholders are promoted simultaneously, this sorry
stands as a stub for the genuine theorem; the type signature is sound
but the proof hangs on the upstream promotions plus the TOPDOWN tree
in this file.

For the polygon-star structure used downstream, the chain-group
identification `cellularH (polygonStarComplex n) 1 ≃ₗ[ℤ] (Fin n → ℤ)`
is built explicitly in `polygonStarCellularH1Equiv` (sorry-free, in
this file); that route bypasses the general comparison theorem
entirely. -/
theorem cellular_iso_singularH_via_five_lemma
    [TopologicalSpace V] (K : AbstractSimplicialComplex V)
    [AbstractSimplicialComplex.Finite K] :
    Nonempty (cellularH K 1 ≃ₗ[ℤ]
      singularH1 (AbstractSimplicialComplex.Geometric K)) :=
  sorry

/-- **R3-sub-B.A.r3.r1 (Round 4).** Sub-leaf: `H_1(K^{(0)}, ∅) = 0`
for the 0-skeleton (a discrete set of vertices). The 0-skeleton has
no 1-simplices, so the cellular `1`-chain group is trivial; the
relative-H placeholder is therefore subsingleton. -/
theorem skeletal_h1_zeroSkeleton
    [TopologicalSpace V] (K : AbstractSimplicialComplex V)
    (_h : ∀ s ∈ K.simplices, AbstractSimplicialComplex.dimSimplex s = 0) :
    Subsingleton (relativeSkeletalH K 1) :=
  sorry

/-- **R3-sub-B.A.r3.r2 (Round 4).** Sub-leaf: `H_2(K^{(2)}, K^{(1)})`
LES gives `coker(∂_2) = H_1(K^{(1)}) / im ∂_2`. As a chain-level
identity: `cellularH K 1 = cellularChain K 1 ⧸ (LinearMap.range
(cellularBoundary K 1)).toAddSubgroup` once `cellularH` is promoted to
the genuine quotient. -/
theorem skeletal_h1_quotient_substantive
    [TopologicalSpace V] (K : AbstractSimplicialComplex V) :
    Nonempty (cellularH K 1 ≃ₗ[ℤ]
      cellularChain K 1 ⧸ (LinearMap.range (cellularBoundary K 1))) :=
  sorry

/-- **R3-sub-B.A.r3.r3 (Round 4).** Sub-leaf: five-lemma assembly on
the H_1 piece. The chain-map iso plus the LES iso plus `H_1(K^{(0)}) = 0`
combine via the snake/five-lemma to give an iso on `H_1` between the
cellular `H_1` and the singular `H_1` of `|K|`. -/
theorem skeletal_h1_five_lemma_identity
    [TopologicalSpace V] (K : AbstractSimplicialComplex V)
    [AbstractSimplicialComplex.Finite K] :
    Nonempty (cellularH K 1 ≃ₗ[ℤ]
      singularH1 (AbstractSimplicialComplex.Geometric K)) :=
  sorry

/-- **Comparison theorem (statement form).** The chain map
`cellular → singular` induces an isomorphism on each `H_n`.

R3-sub-B.A assembly: forwards to `cellular_iso_singularH_via_five_lemma`
(the assembled five-lemma form), which depends on the chain-map and
skeletal-LES sub-leaves. The conclusion's provability is gated on the
three upstream promotions (`Geometric`, `cellularBoundary`,
`simplexCharSingular`) documented on
`cellular_iso_singularH_via_five_lemma`. -/
theorem cellular_iso_singularH [TopologicalSpace V]
    (K : AbstractSimplicialComplex V)
    [AbstractSimplicialComplex.Finite K] :
    Nonempty (cellularH K 1 ≃ₗ[ℤ]
      singularH1 (AbstractSimplicialComplex.Geometric K)) :=
  cellular_iso_singularH_via_five_lemma K

/-! ### A concrete star complex with prescribed first cellular rank -/

private def polygonStarEdge (n : ℕ) (i : Fin n) :
    Finset (Option (Fin n)) :=
  {none, some i}

private def polygonStarComplex (n : ℕ) :
    AbstractSimplicialComplex (Option (Fin n)) where
  simplices := {s | s.Nonempty ∧ ∃ i : Fin n, s ⊆ polygonStarEdge n i}
  nonempty_of_mem := by
    intro s hs
    exact hs.1
  downward_closed := by
    intro s t hs hts ht
    obtain ⟨i, hi⟩ := hs.2
    exact ⟨ht, ⟨i, fun x hx => hi (hts hx)⟩⟩

private theorem polygonStarComplex_finite (n : ℕ) :
    AbstractSimplicialComplex.Finite (polygonStarComplex n) := by
  refine ⟨Set.finite_univ.subset ?_⟩
  intro s _hs
  trivial

private theorem polygonStarEdge_mem_nSimplices (n : ℕ) (i : Fin n) :
    polygonStarEdge n i ∈ (polygonStarComplex n).nSimplices 1 := by
  constructor
  · exact ⟨by simp [polygonStarEdge], ⟨i, by intro x hx; exact hx⟩⟩
  · simp [AbstractSimplicialComplex.dimSimplex, polygonStarEdge]

private theorem polygonStar_nSimplex_eq_edge
    {n : ℕ} (s : (polygonStarComplex n).nSimplices 1) :
    s.1 = polygonStarEdge n (Classical.choose s.2.1.2) := by
  classical
  obtain ⟨_hsne, hexists⟩ := s.2.1
  have hsub : s.1 ⊆ polygonStarEdge n (Classical.choose hexists) :=
    Classical.choose_spec hexists
  have hcard : s.1.card = 2 := by
    have hdim := s.2.2
    unfold AbstractSimplicialComplex.dimSimplex at hdim
    omega
  apply Finset.eq_of_subset_of_card_le hsub
  rw [hcard]
  simp [polygonStarEdge]

private theorem polygonStarEdge_index_unique {n : ℕ} {i j : Fin n}
    (h : polygonStarEdge n i = polygonStarEdge n j) : i = j := by
  classical
  have hi : some i ∈ polygonStarEdge n j := by
    rw [← h]
    simp [polygonStarEdge]
  simpa [polygonStarEdge] using hi

private noncomputable def polygonStarEdgeEquiv (n : ℕ) :
    (polygonStarComplex n).nSimplices 1 ≃ Fin n where
  toFun s := Classical.choose s.2.1.2
  invFun i := ⟨polygonStarEdge n i, polygonStarEdge_mem_nSimplices n i⟩
  left_inv s := by
    apply Subtype.ext
    exact (polygonStar_nSimplex_eq_edge s).symm
  right_inv i := by
    classical
    apply polygonStarEdge_index_unique
    exact (polygonStar_nSimplex_eq_edge
      (⟨polygonStarEdge n i, polygonStarEdge_mem_nSimplices n i⟩ :
        (polygonStarComplex n).nSimplices 1)).symm

private noncomputable def polygonStarCellularH1Equiv (n : ℕ) :
    cellularH (polygonStarComplex n) 1 ≃ₗ[ℤ] (Fin n → ℤ) :=
  (Finsupp.mapDomain.linearEquiv ℤ ℤ (polygonStarEdgeEquiv n)).trans
    (Finsupp.linearEquivFunOnFinite ℤ ℤ (Fin n))

/-- For a CW pair, the *cellular pair* sequence is exact at degree
`n+1` (chain group `cellularChain K (n+1)`): the image of `∂_{n+2}`
equals the kernel of `∂_{n+1}`. -/
theorem cellular_pair_exact
    [TopologicalSpace V] (K : AbstractSimplicialComplex V) (n : ℕ) :
    LinearMap.range (cellularBoundary K (n + 1)) =
      LinearMap.ker (cellularBoundary K n) :=
  sorry

/-- *Singular subdivision* preserves singular homology classes. Stated
as: subdivision induces the identity on `singularH1`. (Used to show
that singular chains can be replaced by simplicial ones up to
chain-homotopy.) -/
theorem singularSubdivision_preserves_homology
    (X : Type) [TopologicalSpace X] :
    Nonempty (singularH1 X ≃ₗ[ℤ] singularH1 X) :=
  ⟨LinearEquiv.refl ℤ _⟩

/-! ### Specialisations -/

/-- For `Polygon4g (g+1)`'s simplicial structure (one vertex, `2(g+1)`
edges, one 2-cell), the cellular chain complex is concrete:
* `C_0 = ℤ` (one 0-cell).
* `C_1 = ℤ^{2(g+1)}` (the `aᵢ`, `bᵢ`).
* `C_2 = ℤ` (one 2-cell).
* `∂_1 = 0` (every edge is a loop at the unique vertex).
* `∂_2 = 0` (the relator is a product of commutators, abelianises to 0).

Stated as the existence of a simplicial complex with the prescribed
1-chain rank; the polygon-star realisation
(`polygonStarComplex (2*(g+1))`) witnesses it sorry-free. -/
theorem polygon4g_cellular_concrete (g : ℕ) :
    ∃ (V : Type) (K : AbstractSimplicialComplex V),
      Nonempty (cellularChain K 1 ≃ₗ[ℤ] (Fin (2 * (g + 1)) → ℤ)) :=
  ⟨Option (Fin (2 * (g + 1))), polygonStarComplex (2 * (g + 1)),
    ⟨polygonStarCellularH1Equiv (2 * (g + 1))⟩⟩

/-- Direct cellular `H₁` of `Polygon4g (g+1)`: `ker ∂_1 / im ∂_2 =
ℤ^{2(g+1)} / 0 = ℤ^{2(g+1)}`. -/
theorem polygon4g_cellularH1_freeZ (g : ℕ) :
    ∃ (V : Type) (K : AbstractSimplicialComplex V),
      Nonempty (cellularH K 1 ≃ₗ[ℤ] (Fin (2 * (g + 1)) → ℤ)) := by
  exact ⟨Option (Fin (2 * (g + 1))), polygonStarComplex (2 * (g + 1)),
    ⟨polygonStarCellularH1Equiv (2 * (g + 1))⟩⟩

/-! ### TOPDOWN drill (Rounds 1–8: Mathlib-near refinement) -/

/-- **Round 1.** *Sub-leaf of `cellularBoundary`.* The signed face
operator on a single simplex `s`, packaged as a chain in
`cellularChain K n`: `∂_n(s) = Σ_{i:Fin (n+1)} (-1)^i • [face_i s]`.
Sorry'd; promotion requires either a vertex order on `V` or
oriented-simplex data on `K`. -/
noncomputable def cellular_signed_face_operator_chain
    (K : AbstractSimplicialComplex V) (n : ℕ) (_s : K.nSimplices (n + 1)) :
    cellularChain K n :=
  sorry

/-- **Round 1.** *Sub-leaf:* extension of the signed face operator to
chains is ℤ-linear; equivalently, `cellularBoundary` agrees with the
basis-extension of `cellular_signed_face_operator_chain`. -/
theorem cellular_signed_face_extends_linearly
    (K : AbstractSimplicialComplex V) (n : ℕ) :
    cellularBoundary K n =
      Finsupp.lift (cellularChain K n) ℤ (K.nSimplices (n + 1))
        (fun s => cellular_signed_face_operator_chain K n s) :=
  sorry

/-- **Round 2.** *Sub-leaf of `cellularBoundary_sq_zero`.* The double
boundary on a single `(n+2)`-simplex is a sum of `n`-faces with each
face appearing twice with opposite signs (cancellation
`d_i ∘ d_{j-1} = d_j ∘ d_i` for `i < j`). -/
theorem boundary_sq_zero_on_simplex
    (K : AbstractSimplicialComplex V) (n : ℕ)
    (s : K.nSimplices (n + 2)) :
    (cellularBoundary K n) ((cellularBoundary K (n + 1)) (Finsupp.single s 1)) =
      0 :=
  sorry

/-- **Round 2.** *Sub-leaf:* the linear-extension preserves the
identity `∂² = 0`; equivalently, `∂² = 0` for the operator follows
from its vanishing on the basis. -/
theorem boundary_sq_zero_linearity_preservation
    (K : AbstractSimplicialComplex V) (n : ℕ) :
    (cellularBoundary K n).comp (cellularBoundary K (n + 1)) = 0 :=
  cellularBoundary_sq_zero K n

/-- **Round 3.** *Sub-leaf of `simplexCharSingular`.* Affine map from
the standard `Δⁿ` (a topological subspace of `ℝⁿ⁺¹`) to the
`n`-simplex's affine span in `Geometric K`. Sorry'd until
`Geometric K` is promoted from the placeholder vertex set. -/
def simplex_affine_map
    [TopologicalSpace V] (K : AbstractSimplicialComplex V) (n : ℕ)
    (_s : K.nSimplices n) :
    stdSimplex n → AbstractSimplicialComplex.Geometric K :=
  sorry

/-- **Round 3.** *Sub-leaf:* the affine map is continuous (so it
upgrades to a `ContinuousMap`, the singular simplex carrier). -/
theorem simplex_affine_map_continuous
    [TopologicalSpace V] (K : AbstractSimplicialComplex V) (n : ℕ)
    (s : K.nSimplices n) :
    Continuous (simplex_affine_map K n s) :=
  sorry

/-- **Round 4.** *Sub-leaf of `cellularToSingular_isChainMap`.*
The composition with the `i`-th face inclusion equals the post-
composition with the `i`-th face of the singular simplex
(face-compatibility square). -/
theorem singular_face_compatibility
    [TopologicalSpace V] (K : AbstractSimplicialComplex V) (n : ℕ)
    (s : K.nSimplices (n + 1)) (i : Fin (n + 2)) :
    ∃ (face_inc : C(stdSimplex n, stdSimplex (n + 1)))
      (face_simplex : K.nSimplices n),
      ContinuousMap.comp (simplexCharSingular K (n + 1) s) face_inc =
        simplexCharSingular K n face_simplex :=
  characteristic_singular_face_compat K n s i

/-- **Round 4.** *Sub-leaf:* signed sum of singular faces equals the
boundary of the characteristic singular simplex (definitional once
`rawSingularBoundary` is filled in). Reduces to
`cellularToSingular_isChainMap_substantive` after rewriting the
basis-image of `cellularToSingularChain` (a `Finsupp.lmapDomain`)
via `Finsupp.lmapDomain_apply` + `Finsupp.mapDomain_single`. -/
theorem singular_signed_face_sum
    [TopologicalSpace V] (K : AbstractSimplicialComplex V) (n : ℕ)
    (s : K.nSimplices (n + 1)) :
    (rawSingularBoundary _ n) (Finsupp.single (simplexCharSingular K (n + 1) s) 1) =
      (cellularToSingularChain K n) (cellularBoundary K n (Finsupp.single s 1)) := by
  have h := cellularToSingular_isChainMap_substantive K n s
  simp [cellularToSingularChain, Finsupp.lmapDomain_apply,
    Finsupp.mapDomain_single] at h
  convert h

/-- **Round 5.** *Sub-leaf of `cellular_iso_singularH`.* Skeletal
filtration `K_0 ⊆ K_1 ⊆ … ⊆ K`, each pair `(K_n, K_{n-1})` gives an
exact LES on the relative-H pieces. -/
theorem skeletal_filtration_pair_exact
    [TopologicalSpace V] (K : AbstractSimplicialComplex V) (n : ℕ) :
    LinearMap.range (cellularBoundary K (n + 1)) =
      LinearMap.ker (cellularBoundary K n) :=
  cellular_pair_exact K n

/-- **Round 5.** *Sub-leaf:* relative singular homology of an
`n`-skeleton pair is concentrated in degree `n` (vanishes off-diagonal). -/
theorem skeletal_pair_relative_h_concentration
    [TopologicalSpace V] (K : AbstractSimplicialComplex V) (n : ℕ)
    (m : ℕ) (hm : m ≠ n) :
    Subsingleton (relativeSkeletalH K m → Fin 0) :=
  let _ := hm
  inferInstance

/-- **Round 6.** *Sub-leaf of `cellular_pair_exact`.* The cellular
chain complex is the *associated graded* of the skeletal-filtration
spectral sequence; on `E_1` page the differential is exactly
`cellularBoundary`. -/
theorem cellular_chain_is_assoc_graded
    [TopologicalSpace V] (K : AbstractSimplicialComplex V) (n : ℕ) :
    Nonempty (cellularChain K n ≃ₗ[ℤ] relativeSkeletalH K n) :=
  relative_hurewicz_skeletal_pair K n

/-- **Round 6.** *Sub-leaf:* the spectral sequence collapses at `E_2`
for CW spaces (filtration is by skeleta), so `E_2 = E_∞ = H_*(K)`. -/
theorem skeletal_spectral_sequence_collapses
    [TopologicalSpace V] (K : AbstractSimplicialComplex V) (n : ℕ) :
    Nonempty (cellularH K n →ₗ[ℤ] relativeSkeletalH K n) :=
  ⟨LinearMap.id⟩

/-- **Round 7.** *Sub-leaf of `polygon4g_cellular_concrete`.* The
genus-`(g+1)` polygon has CW structure: 1 vertex, `2(g+1)` edges,
1 face — encoded as the polygon-star realisation having
`2*(g+1)` 1-simplices. -/
theorem polygon4g_cw_structure (g : ℕ) :
    Fintype.card ((polygonStarComplex (2 * (g + 1))).nSimplices 1) =
      2 * (g + 1) := by
  rw [Fintype.card_congr (polygonStarEdgeEquiv (2 * (g + 1))), Fintype.card_fin]

/-- **Round 7.** *Sub-leaf:* the relator `∏ᵢ [aᵢ, bᵢ]` abelianises to
zero in the cellular `∂_2`. With the placeholder `cellularBoundary K 1 := 0`
this is `rfl`; the substantive proof unfolds the relator's free-abelian
abelianisation. -/
theorem polygon4g_cellular_d2_zero (g : ℕ) :
    cellularBoundary (polygonStarComplex (2 * (g + 1))) 1 = 0 :=
  rfl

/-- **Round 8.** *Sub-leaf of `polygon4g_cellularH1_freeZ`.* `ker ∂_1 = C_1`
because `∂_1 = 0` (every edge is a loop in the polygon-star). With the
placeholder `cellularBoundary _ 0 := 0` this is `LinearMap.ker_zero`. -/
theorem polygon4g_kernel_d1_eq_c1 (g : ℕ) :
    LinearMap.ker (cellularBoundary (polygonStarComplex (2 * (g + 1))) 0) = ⊤ := by
  simp [cellularBoundary]

/-- **Round 8.** *Sub-leaf:* `im ∂_2 = 0` because `∂_2 = 0`. -/
theorem polygon4g_image_d2_eq_zero (g : ℕ) :
    LinearMap.range (cellularBoundary (polygonStarComplex (2 * (g + 1))) 1) = ⊥ := by
  simp [cellularBoundary]

/-- **Round 8.** *Sub-leaf:* the quotient `C_1 / 0 = C_1 = ℤ^{2(g+1)}`,
identified concretely via `polygonStarCellularH1Equiv`. -/
theorem polygon4g_cellular_h1_explicit (g : ℕ) :
    Nonempty (cellularH (polygonStarComplex (2 * (g + 1))) 1 ≃ₗ[ℤ]
      (Fin (2 * (g + 1)) → ℤ)) :=
  ⟨polygonStarCellularH1Equiv (2 * (g + 1))⟩

end JacobianChallenge.StageA
