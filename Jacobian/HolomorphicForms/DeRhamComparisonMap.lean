import Jacobian.HolomorphicForms.SmoothDifferentialForm
import Jacobian.HolomorphicForms.DeRhamComplex
import Jacobian.HolomorphicForms.RealSingularH1
import Jacobian.Periods.IntegralOneCycle
import Jacobian.Periods.RealHomologyTensor
import Jacobian.Periods.PathIntegralViaCoverPickRefl
import Jacobian.Periods.PathIntegralViaCoverTrans
import Jacobian.Periods.PathIntegralViaCoverPickSymm
import Jacobian.Periods.PathIntegralViaCoverChartlocal
import Jacobian.Periods.PathIntegralViaCoverPickAdd
import Jacobian.Periods.ChartPullbackStraightPath
import Jacobian.Periods.ChartContDiffPathExistence
import Jacobian.Periods.PrismChainBridge
import Jacobian.Periods.SingularChainDescent
import Jacobian.Periods.LoopToIntegralCycle
import Jacobian.Blueprint.Sec03.PeriodHomologyInvariance
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.Topology.Connected.PathConnected
import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Analysis.Convex.StdSimplex

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

/-!
# De Rham comparison map (frontier API)

The de Rham theorem is the statement that integration of forms over
singular simplices gives a quasi-isomorphism

  Ω^*(X)  ─∫─→  C^*_sing(X, ℝ)

between the smooth de Rham complex and the singular cochain complex
with real coefficients.  Inverting this on H¹ gives

  H¹_dR(X, ℝ)  ≃ℝ  H¹_sing(X, ℝ)  ≃ℝ  Hom_ℤ(H₁(X, ℤ), ℝ).

This file declares the comparison map at degree 1 as a frontier opaque
linear map plus a named frontier identity asserting it is an
isomorphism on H¹ — the **single deepest analytic frontier theorem** in
the entire `hodge_deRham_rank_eq` chain.

## What this file provides (round 2 refinement)

* `deRhamComparisonMap1` — opaque linear map
  `ClosedForm 1 X → (IntegralOneCycle X →ₗ[ℤ] ℂ)`,
  the integration of a closed 1-form over an integer 1-cycle.

* `deRhamComparisonMap1_vanishes_on_exact` — frontier identity
  (sorry, **STOKES**): the integral of an exact form over a 1-cycle
  is zero.

* `deRhamComparisonMap1_descends` — frontier construction (sorry-free
  given the previous): the descent to the closed/exact quotient.

* `deRhamComparisonMap1_isLinearEquiv` — frontier identity (sorry,
  **the de Rham theorem proper**): the descended map is a linear
  isomorphism.

* `realDim_deRhamH1_eq_realDim_singularH1` — top-level identity
  (refined in this file) is now sorry-free assembly of the above.

## TOPDOWN role

The "de Rham theorem on a compact smooth manifold" frontier sorry has
now been split into:
1. **Stokes** (vanishing on exact),
2. **Surjectivity** (every cohomology class has a representative whose
   integral over each cycle is the prescribed value), and
3. **Injectivity** (a closed form integrating to zero on every cycle is
   exact — Poincaré lemma + sheaf cohomology).

Each is a substantial Mathlib effort but now precisely scoped.
-/

namespace JacobianChallenge.HolomorphicForms

open JacobianChallenge.Periods
open JacobianChallenge.TraceDegree
open scoped Topology

open scoped Manifold

open CategoryTheory

/-! ### Concrete period-pairing construction (Increment A foundation)

The de Rham comparison map's value on a singular 1-cycle is the integer
linear combination of path integrals over the cycle's component
simplices. We build this concretely:

1. `pairOnSimplexC` — per-simplex path integral, using `pathIntegralViaCover`
   via the `stdSimplex ℝ (Fin 2) ≃ₜ unitInterval` homeomorphism.
2. `chainPairing` — ℤ-linear extension to `singChain 1 X` via the
   coproduct universal property (`singChain_desc` from `PrismChainBridge`).
3. The descent to homology happens in the `def deRhamComparisonMap1` below,
   routed through `periodPairing_descent_aux` + `singularBoundary_eq_sc_f`
   (in `SingularChainDescent.lean`).
-/

/-- Path from a singular 1-simplex `σ : C(stdSimplex ℝ (Fin 2), X)` via
the `stdSimplex ↔ unitInterval` homeomorphism. -/
private noncomputable def simplex1ToPath {X : Type} [TopologicalSpace X]
    (σ : SingSimplex 1 X) :
    Path
      (σ (stdSimplexHomeomorphUnitInterval.symm (0 : unitInterval)))
      (σ (stdSimplexHomeomorphUnitInterval.symm (1 : unitInterval))) where
  toFun t := σ (stdSimplexHomeomorphUnitInterval.symm t)
  continuous_toFun :=
    σ.continuous.comp stdSimplexHomeomorphUnitInterval.symm.continuous
  source' := rfl
  target' := rfl

/-- **Per-simplex pairing.** Path integral of a closed 1-form along a
singular 1-simplex. -/
private noncomputable def pairOnSimplexC
    {X : Type} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (ω : ClosedForm 1 X) (σ : SingSimplex 1 X) : ℂ :=
  -- `SmoothDiffForm 1 X = HolomorphicOneForm ℂ X` definitionally; the
  -- subtype coercion produces the underlying holomorphic 1-form directly.
  pathIntegralViaCover (ω : HolomorphicOneForm ℂ X) (simplex1ToPath σ)

/-- `ℤ → ℂ` linear map sending `1 ↦ c`. -/
private noncomputable def scalarMul1ℤℂ (c : ℂ) : ModuleCat.of ℤ ℤ ⟶ ModuleCat.of ℤ ℂ :=
  ModuleCat.ofHom (LinearMap.toSpanSingleton ℤ ℂ c)

/-- **Multiplication-by-`k`** on `ℂ` viewed as a ℤ-linear endomorphism
of `ModuleCat.of ℤ ℂ`. Used in the smooth de Rham comparison map's
`map_smul'` proof: scaling the form by `k` post-composes the chain
pairing with this morphism. -/
private noncomputable def mulByKℂ (k : ℂ) :
    ModuleCat.of ℤ ℂ ⟶ ModuleCat.of ℤ ℂ :=
  ModuleCat.ofHom
    { toFun := fun c => k * c
      map_add' := by intro a b; ring
      map_smul' := by
        intro n a
        show k * ((n : ℤ) • a) = (n : ℤ) • (k * a)
        rw [zsmul_eq_mul, zsmul_eq_mul]
        ring }

/-- `scalarMul1ℤℂ` is natural in its argument with respect to scalar
multiplication: `scalarMul1ℤℂ (k • c) = scalarMul1ℤℂ c ≫ mulByKℂ k`. -/
private theorem scalarMul1ℤℂ_smul (k c : ℂ) :
    scalarMul1ℤℂ (k • c) = scalarMul1ℤℂ c ≫ mulByKℂ k := by
  apply ModuleCat.hom_ext
  refine LinearMap.ext (fun n => ?_)
  show n • (k • c) = k * n • c
  rw [smul_eq_mul, zsmul_eq_mul, zsmul_eq_mul]
  ring

/-- `scalarMul1ℤℂ` is additive: `scalarMul1ℤℂ (a + b) = scalarMul1ℤℂ a + scalarMul1ℤℂ b`. -/
private theorem scalarMul1ℤℂ_add (a b : ℂ) :
    scalarMul1ℤℂ (a + b) = scalarMul1ℤℂ a + scalarMul1ℤℂ b := by
  apply ModuleCat.hom_ext
  refine LinearMap.ext (fun n => ?_)
  show n • (a + b) = n • a + n • b
  rw [smul_add]

/-- **Chain-level pairing.** ℤ-linear extension of `pairOnSimplexC ω` to
singular 1-chains, via the coproduct universal property `singChain_desc`. -/
private noncomputable def chainPairing
    {X : Type} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (ω : ClosedForm 1 X) : singChain 1 X ⟶ ModuleCat.of ℤ ℂ :=
  singChain_desc (fun σ => scalarMul1ℤℂ (pairOnSimplexC ω σ))

/-- **Per-basis evaluation of `chainPairing`.** Composing a basis 1-simplex
morphism `singChain_basis σ` with `chainPairing ω` yields the scalar map
`scalarMul1ℤℂ (pairOnSimplexC ω σ)` — direct unfolding of `chainPairing`
via `singChain_desc_basis`. -/
private theorem chainPairing_basis_eq
    {X : Type} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (ω : ClosedForm 1 X) (σ : SingSimplex 1 X) :
    singChain_basis σ ≫ chainPairing ω =
      scalarMul1ℤℂ (pairOnSimplexC ω σ) := by
  unfold chainPairing
  exact singChain_desc_basis _ _

/-- For `t ∈ Icc 0 1`, the pair `![1 - t, t] : Fin 2 → ℝ` lies in
`stdSimplex ℝ (Fin 2)`. -/
private lemma stdSimplexPair_mem_of_Icc (t : ℝ) (ht : t ∈ Set.Icc (0:ℝ) 1) :
    ![1 - t, t] ∈ stdSimplex ℝ (Fin 2) :=
  ⟨Fin.forall_fin_two.2 ⟨by show (0:ℝ) ≤ 1 - t; linarith [ht.2],
                           by show (0:ℝ) ≤ t; linarith [ht.1]⟩,
   by simp⟩

/-- A total clamped parametrization `ℝ → stdSimplex ℝ (Fin 2)` of the 0-1
edge: outside `Icc 0 1` we clamp into the unit interval before forming the
simplex pair. On `Icc 0 1` this agrees with the inverse of
`stdSimplexHomeomorphUnitInterval`. -/
private noncomputable def simplexEdgePoint (t : ℝ) : stdSimplex ℝ (Fin 2) :=
  ⟨![1 - max 0 (min 1 t), max 0 (min 1 t)],
    stdSimplexPair_mem_of_Icc _
      ⟨le_max_left _ _, max_le zero_le_one (min_le_left _ _)⟩⟩

/-- On `Icc 0 1`, the clamped `simplexEdgePoint t` equals `⟨![1-t, t], _⟩`. -/
private lemma simplexEdgePoint_of_Icc (t : ℝ) (ht : t ∈ Set.Icc (0:ℝ) 1) :
    simplexEdgePoint t = ⟨![1 - t, t], stdSimplexPair_mem_of_Icc t ht⟩ := by
  apply Subtype.ext
  show ![1 - max 0 (min 1 t), max 0 (min 1 t)] = ![1 - t, t]
  have hclamp : max 0 (min 1 t) = t := by
    rw [min_eq_right ht.2, max_eq_right ht.1]
  rw [hclamp]

/-- For `t ∈ Icc 0 1`, `(simplex1ToPath σ).extend t = σ (simplexEdgePoint t)`.
The path's extend on the unit interval is just `σ ∘ stdSimplexHomeomorphUnitInterval.symm`,
and on `Icc 0 1` the symm reduces to `simplexEdgePoint`. -/
private lemma simplex1ToPath_extend_of_Icc
    {X : Type} [TopologicalSpace X] (σ : SingSimplex 1 X)
    (t : ℝ) (ht : t ∈ Set.Icc (0:ℝ) 1) :
    (simplex1ToPath σ).extend t = σ (simplexEdgePoint t) := by
  rw [(simplex1ToPath σ).extend_extends' ⟨t, ht⟩,
      simplexEdgePoint_of_Icc t ht]
  show σ (stdSimplexHomeomorphUnitInterval.symm ⟨t, ht⟩) =
       σ ⟨![1 - t, t], stdSimplexPair_mem_of_Icc t ht⟩
  rfl

/-- **Chart-C¹ predicate at the simplex level.** A continuous singular
1-simplex `σ : SingSimplex 1 X` satisfies `IsContDiffSingSimplex σ` if,
for every `p : X`, the chart-pullback `(chartAt ℂ p) ∘ σ ∘ simplexEdgePoint`
is `ContDiffOn ℝ 1` on the preimage of `(chartAt ℂ p).source` intersected
with `Icc 0 1`.

Mathematically: σ is smooth along the 0-1 edge of `stdSimplex ℝ (Fin 2)`,
in chart coordinates. This is the simplex-side analog of the path-level
`IsChartContDiffPath`. -/
private def IsContDiffSingSimplex
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (σ : SingSimplex 1 X) : Prop :=
  ∀ p : X, ContDiffOn ℝ 1
    (fun t : ℝ => (chartAt ℂ p) (σ (simplexEdgePoint t)))
    ((fun t : ℝ => σ (simplexEdgePoint t)) ⁻¹' (chartAt ℂ p).source ∩
      Set.Icc 0 1)

/-- **Simplex → path chart-C¹ bridge.** Routes `IsContDiffSingSimplex σ` to
the path-level predicate `IsChartContDiffPath (simplex1ToPath σ)`. The bridge
is a `ContDiffOn.congr` along the value-equality `simplex1ToPath_extend_of_Icc`,
plus a set-equality from the same identity. Sorry-free. -/
private theorem isChartContDiffPath_of_isContDiffSingSimplex
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    {σ : SingSimplex 1 X} (h : IsContDiffSingSimplex σ) :
    JacobianChallenge.TraceDegree.IsChartContDiffPath (simplex1ToPath σ) := by
  intro p
  set f : ℝ → ℂ := (chartAt ℂ p) ∘ (simplex1ToPath σ).extend with hf_def
  set g : ℝ → ℂ := fun t => (chartAt ℂ p) (σ (simplexEdgePoint t)) with hg_def
  set S : Set ℝ :=
    (simplex1ToPath σ).extend ⁻¹' (chartAt ℂ p).source ∩ Set.Icc 0 1 with hS_def
  set S' : Set ℝ :=
    (fun t : ℝ => σ (simplexEdgePoint t)) ⁻¹' (chartAt ℂ p).source ∩
      Set.Icc 0 1 with hS'_def
  have hS_eq : S = S' := by
    ext t
    refine ⟨?_, ?_⟩
    · rintro ⟨ht_pre, ht_Icc⟩
      refine ⟨?_, ht_Icc⟩
      simp only [Set.mem_preimage] at ht_pre ⊢
      rwa [← simplex1ToPath_extend_of_Icc σ t ht_Icc]
    · rintro ⟨ht_pre, ht_Icc⟩
      refine ⟨?_, ht_Icc⟩
      simp only [Set.mem_preimage] at ht_pre ⊢
      rwa [simplex1ToPath_extend_of_Icc σ t ht_Icc]
  show ContDiffOn ℝ 1 f S
  rw [hS_eq]
  apply (h p).congr
  intro t ht
  obtain ⟨_, ht_Icc⟩ := ht
  show f t = g t
  rw [hf_def, hg_def, Function.comp_apply,
      simplex1ToPath_extend_of_Icc σ t ht_Icc]

/-- **Inverse bridge.** A chart-C¹ path `γ` produces a smooth
1-simplex via `Path.toSingSimplex`. This is the inverse of
`isChartContDiffPath_of_isContDiffSingSimplex` and is needed to
package smooth paths (e.g., `manifoldPathFromBasepoint`) as smooth
chain cycles. Sorry-free under the analogous bridge lemma
`Path.toSingSimplex_simplexEdgePoint_eq` (proven inline). -/
private theorem isContDiffSingSimplex_of_isChartContDiffPath
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    {a b : X} {γ : _root_.Path a b}
    (h : JacobianChallenge.TraceDegree.IsChartContDiffPath γ) :
    IsContDiffSingSimplex (Path.toSingSimplex γ) := by
  intro p
  -- Build the bridge: Path.toSingSimplex γ ∘ simplexEdgePoint t = γ.extend t on Icc 0 1.
  have ht_bridge : ∀ t ∈ Set.Icc (0:ℝ) 1,
      (Path.toSingSimplex γ) (simplexEdgePoint t) = γ.extend t := by
    intro t ht
    -- Both equal γ ⟨t, ht⟩ : X.
    show γ.toContinuousMap (stdSimplexHomeomorphUnitInterval (simplexEdgePoint t)) =
         γ.extend t
    have h_homeo : stdSimplexHomeomorphUnitInterval (simplexEdgePoint t) =
        ⟨t, ht⟩ := by
      rw [simplexEdgePoint_of_Icc t ht]
      apply Subtype.ext
      rfl
    rw [h_homeo]
    -- γ.toContinuousMap ⟨t, ht⟩ = γ ⟨t, ht⟩ = γ.extend t.
    exact (γ.extend_extends' ⟨t, ht⟩).symm
  -- Use ContDiffOn.congr to transfer smoothness across the bridge.
  set f : ℝ → ℂ := fun t => (chartAt ℂ p) ((Path.toSingSimplex γ) (simplexEdgePoint t))
  set g : ℝ → ℂ := (chartAt ℂ p) ∘ γ.extend
  set S : Set ℝ :=
    (fun t : ℝ => (Path.toSingSimplex γ) (simplexEdgePoint t)) ⁻¹'
      (chartAt ℂ p).source ∩ Set.Icc 0 1
  set S' : Set ℝ :=
    γ.extend ⁻¹' (chartAt ℂ p).source ∩ Set.Icc 0 1
  have hS_eq : S = S' := by
    ext t
    refine ⟨?_, ?_⟩
    · rintro ⟨ht_pre, ht_Icc⟩
      refine ⟨?_, ht_Icc⟩
      simp only [Set.mem_preimage] at ht_pre ⊢
      rwa [← ht_bridge t ht_Icc]
    · rintro ⟨ht_pre, ht_Icc⟩
      refine ⟨?_, ht_Icc⟩
      simp only [Set.mem_preimage] at ht_pre ⊢
      rwa [ht_bridge t ht_Icc]
  show ContDiffOn ℝ 1 f S
  rw [hS_eq]
  apply (h p).congr
  intro t ht
  obtain ⟨_, ht_Icc⟩ := ht
  show f t = g t
  show (chartAt ℂ p) ((Path.toSingSimplex γ) (simplexEdgePoint t)) =
       ((chartAt ℂ p) ∘ γ.extend) t
  rw [ht_bridge t ht_Icc]
  rfl

/-- **Generator set** for smooth 1-chains: ℤ-multiples of smooth basis
1-simplices. The smooth chain submodule (below) is `Submodule.span ℤ`
of this set. -/
private def smoothSingChain1Generators
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X] :
    Set (singChain 1 X) :=
  {c | ∃ σ : SingSimplex 1 X, IsContDiffSingSimplex σ ∧
       c = (singChain_basis σ).hom 1}

/-- **The smooth 1-chain submodule.** ℤ-span of smooth basis
1-simplices. Closure under add/neg/smul comes from `Submodule.span`. -/
private noncomputable def smoothSingChain1Submodule
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X] :
    Submodule ℤ (singChain 1 X) :=
  Submodule.span ℤ (smoothSingChain1Generators X)

/-- **Smooth 1-chain predicate.** A chain `c : singChain 1 X` is
smooth iff it lies in the ℤ-submodule generated by smooth basis
1-simplices. This is the chain-level analog of `IsContDiffSingSimplex`. -/
private def IsContDiffOneChain
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (c : singChain 1 X) : Prop :=
  c ∈ smoothSingChain1Submodule X

private theorem IsContDiffOneChain.basis
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    {σ : SingSimplex 1 X} (h : IsContDiffSingSimplex σ) :
    IsContDiffOneChain ((singChain_basis σ).hom 1) :=
  Submodule.subset_span ⟨σ, h, rfl⟩

private theorem IsContDiffOneChain.sum
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    {ι : Type*} (s : Finset ι) (f : ι → singChain 1 X)
    (h : ∀ i ∈ s, IsContDiffOneChain (f i)) :
    IsContDiffOneChain (∑ i ∈ s, f i) :=
  Submodule.sum_mem _ h

-- Inc 11b.5 — Mesh decay for iterated medial subdivision.

/-- **Path-integral cast invariance.** `pathIntegralViaCover` does not
depend on the proof witnesses of `Path`'s source/target fields: casting
a path `γ : Path a b` to `Path a' b'` along Prop-equalities `a' = a`,
`b' = b` does not change the integral. -/
private theorem pathIntegralViaCover_cast_eq
    {X : Type} [TopologicalSpace X]
    [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (α : HolomorphicOneForm ℂ X) {a b a' b' : X} (γ : Path a b)
    (ha : a' = a) (hb : b' = b) :
    pathIntegralViaCover α (γ.cast ha hb) = pathIntegralViaCover α γ := by
  subst ha
  subst hb
  rfl

-- Inc 11b.7 — Boundary cancellation for the medial subdivision.
--
-- The lemmas below identify the 12 medial-subdivision sub-edges
-- (`(σ.comp medSub k).comp face j` for (k, j) ∈ Fin 4 × Fin 3) as
-- pieces of the original boundary: three pairs of internal edges
-- cancel via `Path.symm` reversal, and three pairs of boundary halves
-- reassemble via `Path.trans` concatenation.

-- See `medSub_face_homeoSymm_val_eq` below for the per-(k,j)
-- coordinate normal forms used by the H1–H6 cancellation lemmas.

/-- Scaling the form by `k : ℂ` scales the per-simplex pairing. Uses
`pathIntegralViaCover_smul` (sorry-free). -/
private theorem pairOnSimplexC_smul
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (k : ℂ) (ω : ClosedForm 1 X) (σ : SingSimplex 1 X) :
    pairOnSimplexC (k • ω) σ = k • pairOnSimplexC ω σ := by
  -- (k • ω).val = k • ω.val by Submodule subtype smul; this is the
  -- coercion to `SmoothDiffForm 1 X = HolomorphicOneForm ℂ X`.
  show pathIntegralViaCover ((k • ω : ClosedForm 1 X) : HolomorphicOneForm ℂ X)
      (simplex1ToPath σ) =
    k • pathIntegralViaCover ((ω : ClosedForm 1 X) : HolomorphicOneForm ℂ X)
      (simplex1ToPath σ)
  have hcoe : ((k • ω : ClosedForm 1 X) : HolomorphicOneForm ℂ X) =
      k • ((ω : ClosedForm 1 X) : HolomorphicOneForm ℂ X) := rfl
  rw [hcoe]
  exact pathIntegralViaCover_smul k _ (simplex1ToPath σ)

/-- **Inc 11b.8 (Step 3): Witness-form additivity.** Same conclusion
as `pairOnSimplexC_add` but takes an explicit `IsContDiffSingSimplex σ`
hypothesis instead of the universally-quantified-and-false
`simplex1ToPath_isChartContDiffPath` witness. Sorry-free under the
hypothesis. Used by the smooth de Rham comparison map (Step 9). -/
private theorem pairOnSimplexC_add_of_smooth
    {X : Type} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [JacobianChallenge.Periods.StableChartAt ℂ X]
    (ω η : ClosedForm 1 X) {σ : SingSimplex 1 X}
    (h : IsContDiffSingSimplex σ) :
    pairOnSimplexC (ω + η) σ = pairOnSimplexC ω σ + pairOnSimplexC η σ := by
  show pathIntegralViaCover ((ω + η : ClosedForm 1 X) : HolomorphicOneForm ℂ X)
      (simplex1ToPath σ) =
    pathIntegralViaCover ((ω : ClosedForm 1 X) : HolomorphicOneForm ℂ X)
      (simplex1ToPath σ) +
    pathIntegralViaCover ((η : ClosedForm 1 X) : HolomorphicOneForm ℂ X)
      (simplex1ToPath σ)
  have hcoe : ((ω + η : ClosedForm 1 X) : HolomorphicOneForm ℂ X) =
      ((ω : ClosedForm 1 X) : HolomorphicOneForm ℂ X) +
        ((η : ClosedForm 1 X) : HolomorphicOneForm ℂ X) := rfl
  rw [hcoe]
  exact JacobianChallenge.Periods.pathIntegralViaCover_add_of_witnesses _ _
    (simplex1ToPath σ)
    (isChartContDiffPath_of_isContDiffSingSimplex h)

/-- **Inc 11b.8 (Step 7): Witness-form chain-level additivity for smooth
chains.** For a smooth 1-chain `c` (i.e., `IsContDiffOneChain c`),
`chainPairing` is additive in the form `ω` evaluated at `c`. Proved by
`Submodule.span_induction` on `c`'s membership in
`smoothSingChain1Submodule X`, reducing to the smooth basis case
discharged by `pairOnSimplexC_add_of_smooth`. Sorry-free. -/
private theorem chainPairing_add_apply_of_smooth_chain
    {X : Type} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [JacobianChallenge.Periods.StableChartAt ℂ X]
    (ω η : ClosedForm 1 X) {c : singChain 1 X}
    (hc : IsContDiffOneChain c) :
    (chainPairing (ω + η)).hom c =
      (chainPairing ω).hom c + (chainPairing η).hom c := by
  -- Unfold IsContDiffOneChain to expose the submodule membership.
  have hc' : c ∈ smoothSingChain1Submodule X := hc
  refine Submodule.span_induction (p := fun c _ =>
      (chainPairing (ω + η)).hom c =
        (chainPairing ω).hom c + (chainPairing η).hom c) ?_ ?_ ?_ ?_ hc'
  · -- Generator case: c = (singChain_basis σ).hom 1 for smooth σ.
    rintro b ⟨σ, h_smooth_σ, rfl⟩
    -- Evaluate chainPairing on basis: scalarMul1ℤℂ (pairOnSimplexC ω σ) at 1.
    have hb : ∀ (α : ClosedForm 1 X),
        (chainPairing α).hom ((singChain_basis σ).hom 1) =
          pairOnSimplexC α σ := by
      intro α
      -- singChain_basis σ ≫ chainPairing α = scalarMul1ℤℂ (pairOnSimplexC α σ)
      -- Apply both sides to 1 : ℤ.
      have := chainPairing_basis_eq α σ
      have happ : (singChain_basis σ ≫ chainPairing α).hom 1 =
          (scalarMul1ℤℂ (pairOnSimplexC α σ)).hom 1 := by rw [this]
      -- Simplify both sides.
      simp only [ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply] at happ
      rw [happ]
      show LinearMap.toSpanSingleton ℤ ℂ (pairOnSimplexC α σ) (1 : ℤ) = _
      rw [LinearMap.toSpanSingleton_apply_one]
    rw [hb (ω + η), hb ω, hb η]
    exact pairOnSimplexC_add_of_smooth ω η h_smooth_σ
  · -- Zero case.
    show (chainPairing (ω + η)).hom 0 = (chainPairing ω).hom 0 + (chainPairing η).hom 0
    simp
  · -- Additivity case: c = c₁ + c₂, both with induction hypotheses.
    intro c₁ c₂ _hc₁_mem _hc₂_mem hih₁ hih₂
    simp only [map_add]
    rw [hih₁, hih₂]; ring
  · -- ℤ-smul case: c = n • c', with induction hypothesis on c'.
    intro n c' _hc'_mem hih
    simp only [map_smul]
    rw [hih]; ring

/-- Scaling the form by `k : ℂ` post-composes the chain pairing with
`mulByKℂ k`. Proved via `singChain_hom_ext`. -/
private theorem chainPairing_smul
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (k : ℂ) (ω : ClosedForm 1 X) :
    chainPairing (k • ω) = chainPairing ω ≫ mulByKℂ k := by
  apply singChain_hom_ext
  intro s
  -- LHS = scalarMul1ℤℂ (pairOnSimplexC (k • ω) s)
  -- RHS via assoc = scalarMul1ℤℂ (pairOnSimplexC ω s) ≫ mulByKℂ k
  unfold chainPairing
  rw [singChain_desc_basis]
  rw [← Category.assoc, singChain_desc_basis]
  rw [pairOnSimplexC_smul]
  exact scalarMul1ℤℂ_smul k (pairOnSimplexC ω s)

/-- **Inc 11b.8 (Step 8): Smooth chain-level cycle predicate.** A
chain `c : singChain 1 X` is a "smooth chain-level cycle" iff it is
smooth (`IsContDiffOneChain c`) AND its boundary vanishes
(`(K.d 1 0).hom c = 0` where K is the singular chain complex).

For the flagship's load-bearing path, we work at the chain-level (not
the homology quotient), so that the smooth comparison map can be
built sorry-free WITHOUT needing the
`chainPairing_kills_boundary` cycle-descent machinery. -/
private def IsContDiffOneChainCycle
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (c : singChain 1 X) : Prop :=
  IsContDiffOneChain c ∧
    ((JacobianChallenge.Blueprint.Sec03.singularChainComplexZ X).d 1 0).hom c = 0

/-- **Submodule of smooth chain-level cycles.** Intersection of the
smooth chain submodule with the kernel of the boundary morphism. -/
noncomputable def smoothOneChainCycleSubmodule
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X] :
    Submodule ℤ (singChain 1 X) :=
  smoothSingChain1Submodule X ⊓
    LinearMap.ker
      ((JacobianChallenge.Blueprint.Sec03.singularChainComplexZ X).d 1 0).hom

/-- **Inc 11b.8 (Step 9): Smooth de Rham comparison map.** A
ℂ-linear map sending a closed 1-form `ω` to the ℤ-linear "period
functional" on smooth chain-level cycles, given by `chainPairing ω`.

This is **structurally similar** to the original
`deRhamComparisonMap1`, but its DOMAIN is restricted to smooth
chain-level cycles, and its proof closure DOES NOT reach the
universal-false sorries (`every_singSimplex_isContDiffSingSimplex`,
`path_contDiffOn_obligation`). The additivity proof uses
`chainPairing_add_apply_of_smooth_chain` (sorry-free) instead of the
universal-sorry-bearing `chainPairing_add`. The scalar-mul proof uses
`chainPairing_smul` (already sorry-free). And it operates at
chain-level (no homology descent), so no
`chainPairing_kills_boundary` needed.

The flagship's new hypothesis (Inc 11b.8 Step 10) is
`hω : deRhamComparisonMap1_smooth X ω = 0`. -/
private noncomputable def deRhamComparisonMap1_smooth
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [JacobianChallenge.Periods.StableChartAt ℂ X] :
    ClosedForm 1 X →ₗ[ℂ] (smoothOneChainCycleSubmodule X →ₗ[ℤ] ℂ) where
  toFun ω := (chainPairing ω).hom.domRestrict (smoothOneChainCycleSubmodule X)
  map_add' := by
    intro ω η
    apply LinearMap.ext
    rintro ⟨c, hc⟩
    show (chainPairing (ω + η)).hom c =
        (chainPairing ω).hom c + (chainPairing η).hom c
    exact chainPairing_add_apply_of_smooth_chain ω η hc.1
  map_smul' := by
    intro k ω
    apply LinearMap.ext
    rintro ⟨c, _hc⟩
    show (chainPairing (k • ω)).hom c = k • (chainPairing ω).hom c
    have hcs := chainPairing_smul X k ω
    have h_eq : (chainPairing (k • ω)).hom c =
        (chainPairing ω ≫ mulByKℂ k).hom c := by rw [hcs]
    rw [h_eq]
    show (mulByKℂ k).hom ((chainPairing ω).hom c) = k • (chainPairing ω).hom c
    show k * (chainPairing ω).hom c = k • (chainPairing ω).hom c
    rw [smul_eq_mul]

/-- **0-simplex θ-evaluation.** ℤ-linear functional on singular
0-chains: each 0-simplex `s : C(stdSimplex ℝ (Fin 1), X)` is sent to
`θ` evaluated at the point `s` represents. Used in the chain-Stokes
factorization `chainPairing(dθ) = ∂₁ ≫ θBoundary`. -/
private noncomputable def θBoundary
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (θ : SmoothDiffForm 0 X) :
    singChain 0 X ⟶ ModuleCat.of ℤ ℂ :=
  singChain_desc (fun (s : SingSimplex 0 X) =>
    scalarMul1ℤℂ ((θ : X → ℂ) (s (stdSimplex.vertex (0 : Fin 1)))))

/-- **Inc E.1 — chart-pullback `HasDerivAt` for `mfderivAsForm θ`.**
For a 0-form θ on a complex manifold X under `[StableChartAt ℂ X]`,
the composition `θ ∘ (chartAt ℂ p).symm : ℂ → ℂ` has Euclidean
derivative equal to the chart-pullback scalar `chartPullbackFun
(chartAt ℂ p) (mfderivAsForm θ).toHol z` at every chart-target point.

This is the manifold-to-Euclidean derivative bridge for the exact-form
case `α = mfderivAsForm θ`. It supplies the `HasDerivAt` primitive
hypothesis that `pathIntegralViaCover_eq_F_diff_in_ball` (sorry-free)
needs to FTC-collapse a chart-local segment of a smooth simplex into
`θ(target) − θ(source)`.

**Proof sketch.** Under `[StableChartAt ℂ X]`:
1. `mfderiv 𝓘 𝓘 (chartAt ℂ p).symm z = id` at `z ∈ (chartAt ℂ p).target`.
2. θ is `C^⊤`, hence MDifferentiableAt at every point.
3. Manifold chain rule: the composed mfderiv equals `mfderivAt θ ∘ id`.
4. For self-model `𝓘 ℂ ℂ`, `HasMFDerivAt = HasFDerivAt`; evaluating
   the CLM at `1 : ℂ` extracts the scalar derivative.
5. `chartedFormPullback_chartAt_eq_of_stable` identifies the
   chart-pullback value as `(mfderivAt θ (c.symm z)) (1 : ℂ)`. -/
theorem chartPullbackFun_mfderivAsForm_hasDerivAt
    {X : Type} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [JacobianChallenge.Periods.StableChartAt ℂ X]
    (θ : SmoothDiffForm 0 X) (p : X) {z : ℂ}
    (hz : z ∈ (chartAt ℂ p).target) :
    HasDerivAt (fun w => (θ : X → ℂ) ((chartAt ℂ p).symm w))
      (JacobianChallenge.Periods.chartPullbackFun (chartAt ℂ p)
        (((⟨mfderivAsForm θ,
            by
              show mfderivAsForm θ ∈ LinearMap.ker (exteriorDerivative 1 X)
              rw [LinearMap.mem_ker]; rfl⟩ :
            ClosedForm 1 X) : SmoothDiffForm 1 X) :
          HolomorphicOneForm ℂ X) z) z := by
  set c := chartAt ℂ p with hc_def
  set α : HolomorphicOneForm ℂ X :=
    (((⟨mfderivAsForm θ,
        by
          show mfderivAsForm θ ∈ LinearMap.ker (exteriorDerivative 1 X)
          rw [LinearMap.mem_ker]; rfl⟩ :
        ClosedForm 1 X) : SmoothDiffForm 1 X) :
      HolomorphicOneForm ℂ X) with hα_def
  have hα_toFun : α.toFun = mfderivAt θ := rfl
  have h_csymm_src : c.symm z ∈ c.source := c.map_target hz
  have h_cpb_eq : JacobianChallenge.Periods.chartPullbackFun c α z =
      (mfderivAt θ (c.symm z)) (1 : ℂ) := by
    rw [JacobianChallenge.Periods.chartPullbackFun_apply,
        JacobianChallenge.Periods.chartedFormPullback_chartAt_eq_of_stable p α hz,
        hα_toFun]
    rfl
  rw [h_cpb_eq]
  haveI : IsManifold (modelWithCornersSelf ℂ ℂ) (1 : WithTop ℕ∞) X :=
    IsManifold.of_le le_top
  have h_csymm_mdiff_at :
      MDifferentiableAt (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ)
        c.symm z :=
    (mdifferentiable_of_mem_atlas (chart_mem_atlas ℂ p)).symm.mdifferentiableAt hz
  have h_csymm_mfderiv :
      mfderiv (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) c.symm z =
        ContinuousLinearMap.id ℂ ℂ :=
    JacobianChallenge.Periods.mfderiv_chartAt_symm_eq_id_of_stable p hz
  have h_csymm_hmfd :
      HasMFDerivAt (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ)
        c.symm z (ContinuousLinearMap.id ℂ ℂ) := by
    convert h_csymm_mdiff_at.hasMFDerivAt
    exact h_csymm_mfderiv.symm
  have hθ_mdiff_at :
      MDifferentiableAt (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ)
        (θ : X → ℂ) (c.symm z) :=
    θ.contMDiff.mdifferentiableAt (by decide)
  have hθ_hmfd :
      HasMFDerivAt (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ)
        (θ : X → ℂ) (c.symm z) (mfderivAt θ (c.symm z)) :=
    hθ_mdiff_at.hasMFDerivAt
  have h_comp_hmfd :
      HasMFDerivAt (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ)
        (fun w => (θ : X → ℂ) (c.symm w)) z
        ((mfderivAt θ (c.symm z)).comp (ContinuousLinearMap.id ℂ ℂ)) :=
    hθ_hmfd.comp z h_csymm_hmfd
  have h_comp_id :
      (mfderivAt θ (c.symm z)).comp (ContinuousLinearMap.id ℂ ℂ) =
        mfderivAt θ (c.symm z) :=
    ContinuousLinearMap.comp_id _
  rw [h_comp_id] at h_comp_hmfd
  have h_comp_hfd :
      HasFDerivAt (fun w => (θ : X → ℂ) (c.symm w))
        (mfderivAt θ (c.symm z)) z := by
    rw [← hasMFDerivAt_iff_hasFDerivAt]
    exact h_comp_hmfd
  exact h_comp_hfd.hasDerivAt

/-- **Inc D.3.a — Per-simplex FTC for smooth 1-simplices (named frontier).**
The pairing of an exact 1-form `mfderivAsForm θ` against a SMOOTH
singular 1-simplex (with `IsContDiffSingSimplex σ` hypothesis) equals
the endpoint difference of `θ`. This is the smooth-restricted version
of `pairOnSimplexC_mfderivAsForm` — true and provable, unlike the
universal version (which is false for non-smooth simplices).

To be discharged sorry-free by future work via:
1. Chart-cover partition of `simplex1ToPath σ` (via
   `JacobianChallenge.Periods.exists_uniform_chart_partition` +
   `isChartContDiffPath_of_isContDiffSingSimplex hσ`).
2. Per-segment FTC via the existing
   `JacobianChallenge.Periods.pathIntegralViaCover_eq_F_diff_in_ball`
   with primitive `F_i = θ ∘ (chartAt ℂ (pickChart i)).symm` and the
   chart-pullback HasDerivAt bridge (manifold-to-Euclidean derivative
   identification for `mfderivAsForm θ`).
3. Telescoping the endpoint differences across segments.

Estimated proof LOC: ~150-250. -/
private theorem pairOnSimplexC_mfderivAsForm_of_smooth
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [JacobianChallenge.Periods.StableChartAt ℂ X]
    (θ : SmoothDiffForm 0 X) (σ : SingSimplex 1 X)
    (hσ : IsContDiffSingSimplex σ) :
    pairOnSimplexC (X := X)
        ⟨mfderivAsForm θ,
         by
           show mfderivAsForm θ ∈ LinearMap.ker (exteriorDerivative 1 X)
           rw [LinearMap.mem_ker]; rfl⟩ σ =
      (θ : X → ℂ) (σ (stdSimplexHomeomorphUnitInterval.symm (1 : unitInterval))) -
      (θ : X → ℂ) (σ (stdSimplexHomeomorphUnitInterval.symm (0 : unitInterval))) := by
  set γ : Path
      (σ (stdSimplexHomeomorphUnitInterval.symm (0 : unitInterval)))
      (σ (stdSimplexHomeomorphUnitInterval.symm (1 : unitInterval))) :=
    simplex1ToPath σ with hγ_def
  set α : HolomorphicOneForm ℂ X :=
    (((⟨mfderivAsForm θ,
        by
          show mfderivAsForm θ ∈ LinearMap.ker (exteriorDerivative 1 X)
          rw [LinearMap.mem_ker]; rfl⟩ :
        ClosedForm 1 X) : SmoothDiffForm 1 X) :
      HolomorphicOneForm ℂ X) with hα_def
  -- pairOnSimplexC reduces to pathIntegralViaCover.
  show pathIntegralViaCover α γ
    = (θ : X → ℂ) (σ (stdSimplexHomeomorphUnitInterval.symm (1 : unitInterval)))
      - (θ : X → ℂ) (σ (stdSimplexHomeomorphUnitInterval.symm (0 : unitInterval)))
  -- Chart-C¹ witness for γ via hσ.
  have hγ_chartContDiff : IsChartContDiffPath γ :=
    isChartContDiffPath_of_isContDiffSingSimplex hσ
  -- Uniform chart partition with ball.
  obtain ⟨n, hn, pickChart, radius, hr_pos, hr_subset, hcov_with_ball⟩ :=
    JacobianChallenge.Periods.exists_uniform_chart_partition_with_ball γ.toContinuousMap
  have hcov : ∀ (i : Fin n) (t : unitInterval),
      (i : ℝ) / n ≤ (t : ℝ) → (t : ℝ) ≤ ((i : ℝ) + 1) / n →
      γ t ∈ (chartAt ℂ (pickChart i)).source :=
    fun i t ht₁ ht₂ => (hcov_with_ball i t ht₁ ht₂).1
  have hcov_ball : ∀ (i : Fin n) (t : unitInterval),
      (i : ℝ) / n ≤ (t : ℝ) → (t : ℝ) ≤ ((i : ℝ) + 1) / n →
      (chartAt ℂ (pickChart i)) (γ t) ∈
        Metric.ball ((chartAt ℂ (pickChart i)) (pickChart i)) (radius i) :=
    fun i t ht₁ ht₂ => (hcov_with_ball i t ht₁ ht₂).2
  -- Bridge pathIntegralViaCover to pathIntegralViaCoverWith with our partition.
  have h_to_with :
      pathIntegralViaCover α γ =
        JacobianChallenge.Periods.pathIntegralViaCoverWith α γ n hn pickChart hcov := by
    unfold pathIntegralViaCover
    exact JacobianChallenge.Periods.pathIntegralViaCoverWith_refinement_invariant'
      α γ hγ_chartContDiff _ _ _ _ n hn pickChart hcov
  rw [h_to_with]
  -- Unfold pathIntegralViaCoverWith to the sum form.
  show ∑ i : Fin n,
      JacobianChallenge.Periods.pathIntegralViaChartCorrect
        (chartAt ℂ (pickChart i)) α
        (γ.subpath
          (JacobianChallenge.Periods.divFinIcc n hn i.val (le_of_lt i.isLt))
          (JacobianChallenge.Periods.divFinIcc n hn (i.val + 1) i.isLt)) _
    = _
  -- Per-segment FTC: i-th term = θ(γ(div_{i+1})) - θ(γ(div_i)).
  have h_endpoint_mem : ∀ (i : Fin n) (k : ℕ) (hk : k ≤ n)
      (hk_lo : (i : ℝ) / n ≤ (k : ℝ) / n) (hk_hi : (k : ℝ) / n ≤ ((i : ℝ) + 1) / n),
      γ (JacobianChallenge.Periods.divFinIcc n hn k hk) ∈
        (chartAt ℂ (pickChart i)).source :=
    fun i k hk hk_lo hk_hi =>
      hcov i (JacobianChallenge.Periods.divFinIcc n hn k hk) hk_lo hk_hi
  -- The two endpoints of segment i: div(i) and div(i+1).
  have h_segment : ∀ i : Fin n,
      JacobianChallenge.Periods.pathIntegralViaChartCorrect
        (chartAt ℂ (pickChart i)) α
        (γ.subpath
          (JacobianChallenge.Periods.divFinIcc n hn i.val (le_of_lt i.isLt))
          (JacobianChallenge.Periods.divFinIcc n hn (i.val + 1) i.isLt))
        (by
          rw [Path.range_subpath]
          intro x hx
          obtain ⟨t, ht, rfl⟩ := hx
          rw [Set.uIcc_of_le
            (JacobianChallenge.Periods.divFinIcc_le_succ n hn i.val i.isLt)] at ht
          rcases Set.mem_Icc.mp ht with ⟨h1, h2⟩
          have hle1 : ((i.val : ℝ) / n) ≤ (t : ℝ) := h1
          have hle2 : (t : ℝ) ≤ ((i.val : ℝ) + 1) / n := by
            have h2' : (t : ℝ) ≤
                (JacobianChallenge.Periods.divFinIcc n hn (i.val + 1) i.isLt : ℝ) := h2
            rw [JacobianChallenge.Periods.divFinIcc_val] at h2'
            push_cast at h2'
            exact h2'
          exact hcov i t hle1 hle2)
      = (θ : X → ℂ) (γ (JacobianChallenge.Periods.divFinIcc n hn (i.val + 1) i.isLt))
        - (θ : X → ℂ)
          (γ (JacobianChallenge.Periods.divFinIcc n hn i.val (le_of_lt i.isLt))) := by
    intro i
    set c := chartAt ℂ (pickChart i) with hc_def
    set F : ℂ → ℂ := fun w => (θ : X → ℂ) (c.symm w) with hF_def
    -- HasDerivAt witness via E.1.
    have hF_HDA : ∀ z ∈ Metric.ball (c (pickChart i)) (radius i),
        HasDerivAt F (JacobianChallenge.Periods.chartPullbackFun c α z) z := by
      intro z hz
      have hz_target : z ∈ c.target := hr_subset i hz
      exact chartPullbackFun_mfderivAsForm_hasDerivAt θ (pickChart i) hz_target
    -- Subpath endpoints: γ(div_i), γ(div_{i+1}).
    set sub_path : Path (γ (JacobianChallenge.Periods.divFinIcc n hn i.val
            (le_of_lt i.isLt)))
        (γ (JacobianChallenge.Periods.divFinIcc n hn (i.val + 1) i.isLt)) :=
      γ.subpath
        (JacobianChallenge.Periods.divFinIcc n hn i.val (le_of_lt i.isLt))
        (JacobianChallenge.Periods.divFinIcc n hn (i.val + 1) i.isLt) with sub_path_def
    -- Subpath range ⊆ c.source.
    have h_subrange : Set.range sub_path ⊆ c.source := by
      rw [Path.range_subpath]
      intro x hx
      obtain ⟨t, ht, rfl⟩ := hx
      rw [Set.uIcc_of_le
        (JacobianChallenge.Periods.divFinIcc_le_succ n hn i.val i.isLt)] at ht
      rcases Set.mem_Icc.mp ht with ⟨h1, h2⟩
      have hle1 : ((i.val : ℝ) / n) ≤ (t : ℝ) := h1
      have hle2 : (t : ℝ) ≤ ((i.val : ℝ) + 1) / n := by
        have h2' : (t : ℝ) ≤
            (JacobianChallenge.Periods.divFinIcc n hn (i.val + 1) i.isLt : ℝ) := h2
        rw [JacobianChallenge.Periods.divFinIcc_val] at h2'
        push_cast at h2'
        exact h2'
      exact hcov i t hle1 hle2
    -- Bounds on i.val/n used repeatedly.
    have hn_pos : (0 : ℝ) < n := by exact_mod_cast hn
    have hi_succ_le_n : (i.val + 1 : ℕ) ≤ n := Nat.succ_le_of_lt i.isLt
    have hi_le_succ_R : ((i.val : ℝ)) / n ≤ ((i.val : ℝ) + 1) / n := by
      apply div_le_div_of_nonneg_right _ (le_of_lt hn_pos)
      linarith
    have hi_succ_le_one_R : ((i.val : ℝ) + 1) / n ≤ 1 := by
      rw [div_le_one hn_pos]
      exact_mod_cast hi_succ_le_n
    have hi_le_one_R : ((i.val : ℝ)) / n ≤ 1 := le_trans hi_le_succ_R hi_succ_le_one_R
    have hi_nonneg_R : (0 : ℝ) ≤ (i.val : ℝ) / n := by positivity
    -- Subpath chart-lift ⊆ ball.
    have h_sublift_ball : ∀ t : unitInterval,
        c (sub_path t) ∈ Metric.ball (c (pickChart i)) (radius i) := by
      intro t
      -- sub_path t = γ (subpathAux div_i div_{i+1} t) = γ ⟨(1-t)*div_i + t*div_{i+1}, _⟩.
      have h_interp_mem : (1 - (t : ℝ)) *
          (JacobianChallenge.Periods.divFinIcc n hn i.val (le_of_lt i.isLt) : ℝ)
          + (t : ℝ) *
          (JacobianChallenge.Periods.divFinIcc n hn (i.val + 1) i.isLt : ℝ)
          ∈ unitInterval := by
        rw [JacobianChallenge.Periods.divFinIcc_val,
            JacobianChallenge.Periods.divFinIcc_val]
        constructor
        · have h1 : (0 : ℝ) ≤ (1 - (t : ℝ)) * ((i.val : ℝ) / n) :=
            mul_nonneg (by linarith [t.2.2]) hi_nonneg_R
          have h2 : (0 : ℝ) ≤ (t : ℝ) * (((i.val + 1 : ℕ) : ℝ) / n) := by
            apply mul_nonneg t.2.1
            push_cast; positivity
          linarith
        · -- (1-t)·a + t·b ≤ (1-t)·1 + t·1 = 1.
          have h1 : (1 - (t : ℝ)) * ((i.val : ℝ) / n) ≤ (1 - (t : ℝ)) := by
            have ht_nonneg : (0 : ℝ) ≤ 1 - (t : ℝ) := by linarith [t.2.2]
            nlinarith
          have h2 : (t : ℝ) * (((i.val + 1 : ℕ) : ℝ) / n) ≤ (t : ℝ) := by
            have hcast : (((i.val + 1 : ℕ) : ℝ) / n) = ((i.val : ℝ) + 1) / n := by
              push_cast; ring
            rw [hcast]
            nlinarith [t.2.1]
          linarith
      have h_sub_eq : (sub_path t : X) = γ
          ⟨(1 - (t : ℝ)) *
            (JacobianChallenge.Periods.divFinIcc n hn i.val (le_of_lt i.isLt) : ℝ)
            + (t : ℝ) *
            (JacobianChallenge.Periods.divFinIcc n hn (i.val + 1) i.isLt : ℝ),
            h_interp_mem⟩ := rfl
      rw [h_sub_eq]
      apply hcov_ball i
      · show ((i.val : ℝ) / n) ≤ (1 - (t : ℝ)) *
            (JacobianChallenge.Periods.divFinIcc n hn i.val (le_of_lt i.isLt) : ℝ)
            + (t : ℝ) *
            (JacobianChallenge.Periods.divFinIcc n hn (i.val + 1) i.isLt : ℝ)
        show ((i.val : ℝ) / n) ≤ (1 - (t : ℝ)) * ((i.val : ℝ) / n)
            + (t : ℝ) * (((i.val + 1 : ℕ) : ℝ) / n)
        push_cast
        nlinarith [t.2.1, t.2.2, hi_le_succ_R]
      · show (1 - (t : ℝ)) *
            (JacobianChallenge.Periods.divFinIcc n hn i.val (le_of_lt i.isLt) : ℝ)
            + (t : ℝ) *
            (JacobianChallenge.Periods.divFinIcc n hn (i.val + 1) i.isLt : ℝ)
            ≤ ((i.val : ℝ) + 1) / n
        show (1 - (t : ℝ)) * ((i.val : ℝ) / n)
            + (t : ℝ) * (((i.val + 1 : ℕ) : ℝ) / n) ≤ ((i.val : ℝ) + 1) / n
        push_cast
        nlinarith [t.2.1, t.2.2, hi_le_succ_R]
    have h_sublift_ball' : ∀ t : unitInterval,
        c (sub_path t) ∈ Metric.ball (c (pickChart i)) (radius i) := h_sublift_ball
    -- Chart-C¹ witness for subpath.
    have hsub_chartContDiff : IsChartContDiffPath sub_path :=
      hγ_chartContDiff.subpath _ _
    -- Apply E.2.
    have h_E2 :=
      JacobianChallenge.Periods.pathIntegralViaChartCorrect_eq_F_diff_in_ball
        α (radius i) (hr_pos i) (hr_subset i) hF_HDA
        sub_path h_subrange h_sublift_ball' hsub_chartContDiff
    rw [h_E2]
    -- Now F(c(γ x)) = θ(γ x) for x ∈ c.source.
    have h_F_left :
        F (c (γ (JacobianChallenge.Periods.divFinIcc n hn i.val
                  (le_of_lt i.isLt)))) =
          (θ : X → ℂ)
            (γ (JacobianChallenge.Periods.divFinIcc n hn i.val
                  (le_of_lt i.isLt))) := by
      show (θ : X → ℂ) (c.symm (c (γ _))) = _
      rw [c.left_inv (h_endpoint_mem i i.val (le_of_lt i.isLt) (le_refl _)
        hi_le_succ_R)]
    have h_F_right :
        F (c (γ (JacobianChallenge.Periods.divFinIcc n hn (i.val + 1)
                  i.isLt))) =
          (θ : X → ℂ)
            (γ (JacobianChallenge.Periods.divFinIcc n hn (i.val + 1)
                  i.isLt)) := by
      show (θ : X → ℂ) (c.symm (c (γ _))) = _
      have h_lo : ((i.val : ℝ)) / n ≤ ((i.val + 1 : ℕ) : ℝ) / n := by
        push_cast; exact hi_le_succ_R
      have h_hi : ((i.val + 1 : ℕ) : ℝ) / n ≤ ((i.val : ℝ) + 1) / n := by
        push_cast; exact le_refl _
      rw [c.left_inv (h_endpoint_mem i (i.val + 1) i.isLt h_lo h_hi)]
    rw [h_F_right, h_F_left]
  -- Sum the per-segment results.
  rw [Finset.sum_congr rfl (fun i _ => h_segment i)]
  -- Convert Fin n to range n and telescope.
  set fθ : ℕ → ℂ := fun k =>
    if h : k ≤ n then
      (θ : X → ℂ) (γ (JacobianChallenge.Periods.divFinIcc n hn k h))
    else 0 with hfθ_def
  have hfθ_k : ∀ (k : ℕ) (hk : k ≤ n),
      fθ k = (θ : X → ℂ) (γ (JacobianChallenge.Periods.divFinIcc n hn k hk)) := by
    intro k hk
    simp [hfθ_def, hk]
  rw [show (∑ i : Fin n,
        ((θ : X → ℂ) (γ (JacobianChallenge.Periods.divFinIcc n hn (i.val + 1) i.isLt))
        - (θ : X → ℂ) (γ (JacobianChallenge.Periods.divFinIcc n hn i.val
              (le_of_lt i.isLt))))) =
      ∑ i : Fin n, (fθ (i.val + 1) - fθ i.val) from by
    apply Finset.sum_congr rfl
    intro i _
    rw [hfθ_k (i.val + 1) i.isLt, hfθ_k i.val (le_of_lt i.isLt)]]
  rw [Fin.sum_univ_eq_sum_range (fun i => fθ (i + 1) - fθ i)]
  rw [Finset.sum_range_sub fθ]
  -- Vertex identification.
  rw [hfθ_k n (le_refl n), hfθ_k 0 (Nat.zero_le n)]
  rw [JacobianChallenge.Periods.divFinIcc_zero n hn,
      JacobianChallenge.Periods.divFinIcc_self n hn]
  -- γ at 0 = simplex1ToPath σ at 0 = σ(symm 0). γ at 1 = σ(symm 1).
  show (θ : X → ℂ) (γ 1) - (θ : X → ℂ) (γ 0) = _
  rw [γ.source, γ.target]

/-- **Inc D.3.b — smooth chain-Stokes via span induction (sorry-free
modulo D.3.a).** The chain-Stokes factorization restricted to smooth
1-chains. Replaces the universal-quantification proof (via
`singChain_hom_ext`) with a span-induction proof on `smoothSingChain1Submodule`,
so that the per-simplex sub-case can use the smooth-restricted
`pairOnSimplexC_mfderivAsForm_of_smooth` (a true statement) rather
than the universal `pairOnSimplexC_mfderivAsForm` (a false statement).

The induction proceeds on `c ∈ smoothSingChain1Submodule X`:
- Generator case (smooth basis simplex): apply D.3.a + face/vertex
  bookkeeping mirroring the universal proof's tail.
- Zero/add/smul: linearity of `chainPairing`, `θBoundary`, and `∂`. -/
private theorem chainPairing_mfderivAsForm_eq_d_comp_θBoundary_apply_of_smooth
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [JacobianChallenge.Periods.StableChartAt ℂ X]
    (θ : SmoothDiffForm 0 X) (c : singChain 1 X)
    (hc : IsContDiffOneChain c) :
    (chainPairing (X := X)
        ⟨mfderivAsForm θ,
         by
           show mfderivAsForm θ ∈ LinearMap.ker (exteriorDerivative 1 X)
           rw [LinearMap.mem_ker]; rfl⟩).hom c =
      (θBoundary θ).hom
        (((JacobianChallenge.Blueprint.Sec03.singularChainComplexZ X).d 1 0).hom c) := by
  -- Set up the closed form once.
  set α : ClosedForm 1 X := ⟨mfderivAsForm θ,
    by show mfderivAsForm θ ∈ LinearMap.ker (exteriorDerivative 1 X)
       rw [LinearMap.mem_ker]; rfl⟩ with hα_def
  -- Vertex identifications (mirror deleted universal proof).
  have h0 : (stdSimplexHomeomorphUnitInterval.symm (0 : unitInterval) :
              stdSimplex ℝ (Fin 2)) = stdSimplex.vertex 0 := by
    apply stdSimplexHomeomorphUnitInterval.injective
    rw [stdSimplexHomeomorphUnitInterval.apply_symm_apply]
    show (0 : unitInterval) = stdSimplexHomeomorphUnitInterval (stdSimplex.vertex 0)
    rw [show stdSimplex.vertex (S := ℝ) (0 : Fin 2) =
        ⟨_, single_mem_stdSimplex _ 0⟩ from rfl,
        stdSimplexHomeomorphUnitInterval_zero]
  have h1 : (stdSimplexHomeomorphUnitInterval.symm (1 : unitInterval) :
              stdSimplex ℝ (Fin 2)) = stdSimplex.vertex 1 := by
    apply stdSimplexHomeomorphUnitInterval.injective
    rw [stdSimplexHomeomorphUnitInterval.apply_symm_apply]
    show (1 : unitInterval) = stdSimplexHomeomorphUnitInterval (stdSimplex.vertex 1)
    rw [show stdSimplex.vertex (S := ℝ) (1 : Fin 2) =
        ⟨_, single_mem_stdSimplex _ 1⟩ from rfl,
        stdSimplexHomeomorphUnitInterval_one]
  -- chainPairing at basis simplex = pairOnSimplexC.
  have hPair_basis : ∀ (s : SingSimplex 1 X),
      (chainPairing α).hom ((singChain_basis s).hom 1) = pairOnSimplexC α s := by
    intro s
    have := chainPairing_basis_eq α s
    have happ : (singChain_basis s ≫ chainPairing α).hom 1 =
        (scalarMul1ℤℂ (pairOnSimplexC α s)).hom 1 := by rw [this]
    simp only [ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply] at happ
    rw [happ]
    show LinearMap.toSpanSingleton ℤ ℂ (pairOnSimplexC α s) (1 : ℤ) = _
    rw [LinearMap.toSpanSingleton_apply_one]
  -- θBoundary at basis 0-simplex = θ at the vertex.
  have hθB_basis : ∀ (s : SingSimplex 0 X),
      (θBoundary θ).hom ((singChain_basis s).hom 1)
        = (θ : X → ℂ) (s (stdSimplex.vertex 0)) := by
    intro s
    have hdesc := singChain_desc_basis
      (fun (t : SingSimplex 0 X) =>
        scalarMul1ℤℂ ((θ : X → ℂ) (t (stdSimplex.vertex (0 : Fin 1))))) s
    have happ : (singChain_basis s ≫ θBoundary θ).hom 1 =
        (scalarMul1ℤℂ ((θ : X → ℂ) (s (stdSimplex.vertex (0 : Fin 1))))).hom 1 := by
      unfold θBoundary
      rw [hdesc]
    simp only [ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply] at happ
    rw [happ]
    show LinearMap.toSpanSingleton ℤ ℂ _ (1 : ℤ) = _
    rw [LinearMap.toSpanSingleton_apply_one]
  -- Span induction on smooth chain membership.
  have hc' : c ∈ smoothSingChain1Submodule X := hc
  refine Submodule.span_induction (p := fun c _ =>
      (chainPairing α).hom c =
        (θBoundary θ).hom
          (((JacobianChallenge.Blueprint.Sec03.singularChainComplexZ X).d 1 0).hom c))
    ?_ ?_ ?_ ?_ hc'
  · -- Generator case: c = (singChain_basis σ).hom 1 with smooth σ.
    rintro b ⟨σ, h_smooth_σ, rfl⟩
    rw [hPair_basis σ]
    -- D.3.a → LHS = θ(σ(symm 1)) - θ(σ(symm 0)).
    rw [pairOnSimplexC_mfderivAsForm_of_smooth X θ σ h_smooth_σ]
    -- RHS via singChain_d_basis_apply_one: (K.d 1 0) at basis σ
    --   = basis(constSimplex0 (σ vertex 1)).hom 1 - basis(constSimplex0 (σ vertex 0)).hom 1.
    show _ = (θBoundary θ).hom
      (((JacobianChallenge.Blueprint.Sec03.singularChainComplexZ X).d 1 0).hom
        ((singChain_basis σ).hom 1))
    rw [show ((JacobianChallenge.Blueprint.Sec03.singularChainComplexZ X).d 1 0).hom
            ((singChain_basis σ).hom 1)
          = (singChain_basis (constSimplex0 (σ (stdSimplex.vertex 1)))).hom 1
              - (singChain_basis (constSimplex0 (σ (stdSimplex.vertex 0)))).hom 1 from
        JacobianChallenge.Periods.singChain_d_basis_apply_one σ]
    -- Apply (θBoundary θ).hom linearly across the subtraction.
    rw [show (θBoundary θ).hom
            ((singChain_basis (constSimplex0 (σ (stdSimplex.vertex 1)))).hom 1
              - (singChain_basis (constSimplex0 (σ (stdSimplex.vertex 0)))).hom 1)
          = (θBoundary θ).hom
              ((singChain_basis (constSimplex0 (σ (stdSimplex.vertex 1)))).hom 1)
              - (θBoundary θ).hom
                ((singChain_basis (constSimplex0 (σ (stdSimplex.vertex 0)))).hom 1) from
        map_sub _ _ _]
    rw [hθB_basis (constSimplex0 (σ (stdSimplex.vertex 1))),
        hθB_basis (constSimplex0 (σ (stdSimplex.vertex 0)))]
    show (θ : X → ℂ) (σ (stdSimplexHomeomorphUnitInterval.symm 1))
        - (θ : X → ℂ) (σ (stdSimplexHomeomorphUnitInterval.symm 0))
      = (θ : X → ℂ) (constSimplex0 (σ (stdSimplex.vertex 1)) (stdSimplex.vertex 0))
        - (θ : X → ℂ) (constSimplex0 (σ (stdSimplex.vertex 0)) (stdSimplex.vertex 0))
    -- constSimplex0 v at any point = v.
    have hcs0 : ∀ (v : X) (x : stdSimplex ℝ (Fin 1)),
        constSimplex0 v x = v := fun _ _ => rfl
    rw [hcs0, hcs0]
    -- σ (symm k) = σ (vertex k) via h0/h1.
    congr 1
    · show (θ : X → ℂ) (σ (stdSimplexHomeomorphUnitInterval.symm 1))
        = (θ : X → ℂ) (σ (stdSimplex.vertex 1))
      rw [show (stdSimplexHomeomorphUnitInterval.symm 1 : stdSimplex ℝ (Fin 2))
            = stdSimplex.vertex 1 from h1]
    · show (θ : X → ℂ) (σ (stdSimplexHomeomorphUnitInterval.symm 0))
        = (θ : X → ℂ) (σ (stdSimplex.vertex 0))
      rw [show (stdSimplexHomeomorphUnitInterval.symm 0 : stdSimplex ℝ (Fin 2))
            = stdSimplex.vertex 0 from h0]
  · -- Zero case.
    show (chainPairing α).hom 0
      = (θBoundary θ).hom (((JacobianChallenge.Blueprint.Sec03.singularChainComplexZ X).d 1 0).hom 0)
    simp
  · -- Add case.
    intro c₁ c₂ _ _ h₁ h₂
    simp only [map_add]
    rw [h₁, h₂]
  · -- Smul case.
    intro n c' _ h
    rw [LinearMap.map_smul (chainPairing α).hom n c', h,
        LinearMap.map_smul
          ((JacobianChallenge.Blueprint.Sec03.singularChainComplexZ X).d 1 0).hom n c',
        LinearMap.map_smul (θBoundary θ).hom n _]

/-! ### Path-integral primitive for closed 1-forms with vanishing periods

The classical injectivity argument for the de Rham comparison map: a
closed 1-form `ω` with zero periods admits a global smooth primitive
`θ` (a 0-form with `dθ = ω`). The standard proof decomposes as:

1. Line-integrate `ω` along paths (uses the repo's `pathIntegralViaCover`).
2. Show every loop integrates to zero (the loop ↔ smooth-1-cycle
   bridge under `deRhamComparisonMap1`).
3. Conclude path-independence of `∫ ω` between fixed endpoints.
4. Define `θ(x) := ∫_{x₀ → x} ω` via Classical choice of paths,
   using path-connectedness of a connected manifold.
5. Pull back through a chart with star-shaped image and apply the
   Euclidean Poincaré lemma to conclude `dθ = ω`.

We carry out steps 1, 3, 4 with real Lean proofs, and isolate the
genuine frontier content (loop ↔ cycle bridge, sign-flip on path
reversal at the unparameterised level, path-connectedness of a
connected manifold, FTC / placeholder-model lift) as named sub-sorries.
-/

/-- Underlying holomorphic 1-form of a closed 1-form. With the refined
model where `SmoothDiffForm 1 X = HolomorphicOneForm ℂ X`, this is
just the subtype coercion. -/
noncomputable def ClosedForm.toHolomorphicOneForm
    {X : Type} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (ω : ClosedForm 1 X) : HolomorphicOneForm ℂ X :=
  (ω : SmoothDiffForm 1 X)

/-- Line integral of a closed 1-form along a path. Defined via the
repo's existing `pathIntegralViaCover`, which handles chart-crossing
paths via a uniform chart-cover partition. -/
noncomputable def ClosedForm.lineIntegral
    {X : Type} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (ω : ClosedForm 1 X) {x y : X} (γ : Path x y) : ℂ :=
  pathIntegralViaCover (ClosedForm.toHolomorphicOneForm ω) γ

/-- **Witness-form variant of `lineIntegral_trans`** (Stage III).
Takes explicit `IsChartContDiffPath` witnesses for `γ`, `δ`, and `γ.trans δ`
instead of relying on the universal `[PiecewiseC1PathRegularity X]`
typeclass. Sorry-free under `[StableChartAt ℂ X]` alone (besides the
manifold structure on X). -/
theorem ClosedForm.lineIntegral_trans_of_witnesses
    {X : Type} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [StableChartAt ℂ X]
    (ω : ClosedForm 1 X) {x y z : X} (γ : Path x y) (δ : Path y z)
    (hγ : IsChartContDiffPath γ) (hδ : IsChartContDiffPath δ)
    (hγδ : IsChartContDiffPath (γ.trans δ)) :
    ClosedForm.lineIntegral ω (γ.trans δ) =
      ClosedForm.lineIntegral ω γ + ClosedForm.lineIntegral ω δ :=
  pathIntegralViaCover_trans_eq_add_of_witnesses
    (ClosedForm.toHolomorphicOneForm ω) γ δ hγ hδ hγδ

/-- Line integral over a constant path is zero. Direct consequence of
`pathIntegralViaCover_refl`. -/
@[simp] theorem ClosedForm.lineIntegral_refl
    {X : Type} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (ω : ClosedForm 1 X) (x : X) :
    ClosedForm.lineIntegral ω (Path.refl x) = 0 :=
  pathIntegralViaCover_refl (ClosedForm.toHolomorphicOneForm ω) x

/-- **Witness-form variant of `lineIntegral_symm`** (Stage III). -/
theorem ClosedForm.lineIntegral_symm_of_witnesses
    {X : Type} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [StableChartAt ℂ X]
    (ω : ClosedForm 1 X) {x y : X} (γ : Path x y)
    (hγ : IsChartContDiffPath γ) (hγsymm : IsChartContDiffPath γ.symm) :
    ClosedForm.lineIntegral ω γ.symm = - ClosedForm.lineIntegral ω γ :=
  pathIntegralViaCover_symm_eq_neg_of_witnesses
    (ClosedForm.toHolomorphicOneForm ω) γ hγ hγsymm

/-- **Per-simplex pairing of a `Path.toSingSimplex` equals the path
integral.** This is the natural-content residual obligation isolated
by the decomposition above — a well-definedness identity of standard
form. -/
private theorem pairOnSimplexC_toSingSimplex
    {X : Type} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (ω : ClosedForm 1 X) {a b : X} (γ : Path a b) :
    pairOnSimplexC ω (Path.toSingSimplex γ) =
      pathIntegralViaCover (ClosedForm.toHolomorphicOneForm ω) γ := by
  -- Endpoint identities: `(toSingSimplex γ) (s.symm 0) = a` and similarly for `b`,
  -- via `Homeomorph.apply_symm_apply` and `γ.source` / `γ.target`.
  have ha : (Path.toSingSimplex γ)
        (stdSimplexHomeomorphUnitInterval.symm (0 : unitInterval)) = a := by
    show γ.toContinuousMap
        (stdSimplexHomeomorphUnitInterval
          (stdSimplexHomeomorphUnitInterval.symm (0 : unitInterval))) = a
    rw [Homeomorph.apply_symm_apply]
    exact γ.source
  have hb : (Path.toSingSimplex γ)
        (stdSimplexHomeomorphUnitInterval.symm (1 : unitInterval)) = b := by
    show γ.toContinuousMap
        (stdSimplexHomeomorphUnitInterval
          (stdSimplexHomeomorphUnitInterval.symm (1 : unitInterval))) = b
    rw [Homeomorph.apply_symm_apply]
    exact γ.target
  -- The simplex1ToPath built from toSingSimplex γ is `γ` (up to endpoint Prop-cast):
  -- both have `.toFun t = γ t` pointwise after `s.apply_symm_apply`.
  have hpath :
      simplex1ToPath (Path.toSingSimplex γ) = γ.cast ha hb := by
    apply DFunLike.ext
    intro t
    show γ.toContinuousMap
        (stdSimplexHomeomorphUnitInterval
          (stdSimplexHomeomorphUnitInterval.symm t)) = γ t
    rw [Homeomorph.apply_symm_apply]
    rfl
  -- Conclude: pairOnSimplexC ω (toSingSimplex γ) = pathIntegralViaCover _ (γ.cast _ _)
  --        = pathIntegralViaCover _ γ via `pathIntegralViaCover_cast_eq`.
  show pathIntegralViaCover (ω : HolomorphicOneForm ℂ X)
      (simplex1ToPath (Path.toSingSimplex γ)) = _
  rw [hpath]
  exact pathIntegralViaCover_cast_eq (ClosedForm.toHolomorphicOneForm ω) γ ha hb

/-- **Chain pairing on the singleton partition chain.** The chain pairing
of a closed 1-form against `Path.partitionChain γ 1 hn` (the singleton
basis simplex for a unit partition) reduces to the per-simplex pairing
on the corresponding 0-to-1 subpath. Routes through
`singChain_desc_basis` + `Fin.sum_univ_one`. -/
private theorem chainPairing_partitionChain_one
    {X : Type} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (ω : ClosedForm 1 X) {a b : X} (γ : Path a b) :
    (chainPairing ω).hom (Path.partitionChain γ 1 Nat.one_pos) =
      pairOnSimplexC ω (Path.toSingSimplex
        (γ.subpath (divFinIcc 1 Nat.one_pos 0 (le_of_lt (0 : Fin 1).isLt))
                   (divFinIcc 1 Nat.one_pos (0 + 1) (0 : Fin 1).isLt))) := by
  -- partitionChain γ 1 _ = Σ i : Fin 1, (singChain_basis (toSingSimplex (γ.subpath ...))).hom 1
  unfold Path.partitionChain
  -- Distribute (chainPairing ω).hom over the sum.
  rw [map_sum]
  -- Collapse the singleton sum.
  rw [Fin.sum_univ_one]
  -- The 0-th term: (chainPairing ω).hom ((singChain_basis ...).hom 1) = pairOnSimplexC ω ...
  -- This is `singChain_desc_basis` applied at the element 1, combined with
  -- `scalarMul1ℤℂ_apply_one`.
  -- singChain_basis s ≫ chainPairing ω = scalarMul1ℤℂ (pairOnSimplexC ω s).
  have hbasis :
      singChain_basis
          (Path.toSingSimplex
            (γ.subpath (divFinIcc 1 Nat.one_pos ((0 : Fin 1) : ℕ)
                          (le_of_lt (0 : Fin 1).isLt))
                       (divFinIcc 1 Nat.one_pos (((0 : Fin 1) : ℕ) + 1)
                          (0 : Fin 1).isLt)))
        ≫ chainPairing ω =
          scalarMul1ℤℂ (pairOnSimplexC ω
            (Path.toSingSimplex
              (γ.subpath (divFinIcc 1 Nat.one_pos ((0 : Fin 1) : ℕ)
                            (le_of_lt (0 : Fin 1).isLt))
                         (divFinIcc 1 Nat.one_pos (((0 : Fin 1) : ℕ) + 1)
                            (0 : Fin 1).isLt)))) := by
    unfold chainPairing
    exact singChain_desc_basis _ _
  -- Apply at element 1.
  have happ := congrArg (fun (φ : _ ⟶ ModuleCat.of ℤ ℂ) => φ.hom (1 : ℤ)) hbasis
  -- LHS = (chainPairing ω).hom ((singChain_basis ...).hom 1)
  -- RHS = (scalarMul1ℤℂ (pairOnSimplexC ω ...)).hom 1 = pairOnSimplexC ω ...
  simp only [ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply] at happ
  -- Goal now matches happ once we unfold scalarMul1ℤℂ.
  show ((chainPairing ω).hom ((singChain_basis _).hom 1) : ℂ) = _
  rw [happ]
  -- Evaluate (scalarMul1ℤℂ c).hom 1 = c.
  show (scalarMul1ℤℂ _).hom (1 : ℤ) = _
  unfold scalarMul1ℤℂ
  rw [ModuleCat.hom_ofHom]
  exact LinearMap.toSpanSingleton_apply_one ℤ ℂ _

/-- **Inc 11b.8 (Step 11 helper): smoothness of a partition chain.**
For a smooth path γ (with `IsChartContDiffPath` witness), the
partition chain `Path.partitionChain γ n hn` is a smooth 1-chain.
Each summand `(singChain_basis (Path.toSingSimplex (γ.subpath ...))).hom 1`
is smooth via the inverse bridge `isContDiffSingSimplex_of_isChartContDiffPath`
applied to the subpath's chart-C¹ witness from
`IsChartContDiffPath.subpath`. Sorry-free. -/
private theorem isContDiffOneChain_partitionChain
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    {a b : X} {γ : _root_.Path a b}
    (hγ : JacobianChallenge.TraceDegree.IsChartContDiffPath γ)
    (n : ℕ) (hn : 0 < n) :
    IsContDiffOneChain (Path.partitionChain γ n hn) := by
  unfold Path.partitionChain
  refine IsContDiffOneChain.sum _ _ ?_
  intro i _
  refine IsContDiffOneChain.basis ?_
  refine isContDiffSingSimplex_of_isChartContDiffPath ?_
  exact hγ.subpath _ _

/-- **Inc 11b.8 (Step 11 helper): smooth chain-cycle from a smooth loop.**
For a smooth loop `γ : Path x x`, the partition chain
`Path.partitionChain γ 1 Nat.one_pos` is a smooth chain-level cycle. -/
private theorem isContDiffOneChainCycle_partitionChain_loop
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    {x : X} {γ : _root_.Path x x}
    (hγ : JacobianChallenge.TraceDegree.IsChartContDiffPath γ) :
    IsContDiffOneChainCycle (Path.partitionChain γ 1 Nat.one_pos) :=
  ⟨isContDiffOneChain_partitionChain hγ 1 Nat.one_pos,
   Path.partitionChain_boundary_eq_zero γ 1 Nat.one_pos⟩

/-- **Inc 11b.8 (Step 11 bridge): smooth comparison map applied to a
loop's smooth chain-cycle equals its path integral.** This is the
witness-form analog of `loopToIntegralOneCycle_comparisonMap_eq` but
operating at the chain-cycle level via `deRhamComparisonMap1_smooth`.
Sorry-free under the smoothness witness. -/
private theorem deRhamComparisonMap1_smooth_partitionChain_loop_eq
    {X : Type} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [JacobianChallenge.Periods.StableChartAt ℂ X]
    (ω : ClosedForm 1 X) {x : X} {γ : _root_.Path x x}
    (hγ : JacobianChallenge.TraceDegree.IsChartContDiffPath γ) :
    deRhamComparisonMap1_smooth X ω
        ⟨Path.partitionChain γ 1 Nat.one_pos,
         isContDiffOneChainCycle_partitionChain_loop hγ⟩ =
      pathIntegralViaCover (ClosedForm.toHolomorphicOneForm ω) γ := by
  -- Unfold deRhamComparisonMap1_smooth: domRestrict of (chainPairing ω).hom.
  show (chainPairing ω).hom (Path.partitionChain γ 1 Nat.one_pos) = _
  -- Apply chainPairing_partitionChain_one + pairOnSimplexC_toSingSimplex.
  rw [chainPairing_partitionChain_one]
  rw [pairOnSimplexC_toSingSimplex]
  -- Now goal: pathIntegralViaCover ω (γ.subpath div0 div1) = pathIntegralViaCover ω γ.
  -- The divFinIcc values for n=1 are 0 and 1, so γ.subpath = γ.cast _ _.
  have h_div0 : divFinIcc 1 Nat.one_pos (0 : ℕ)
        (le_of_lt (0 : Fin 1).isLt) = (0 : unitInterval) := by
    apply Subtype.ext; simp [divFinIcc]
  have h_div1 : divFinIcc 1 Nat.one_pos (0 + 1)
        (0 : Fin 1).isLt = (1 : unitInterval) := by
    apply Subtype.ext
    show ((0 + 1 : ℕ) : ℝ) / (1 : ℕ) = 1
    push_cast; norm_num
  rw [h_div0, h_div1, Path.subpath_zero_one]
  exact pathIntegralViaCover_cast_eq (ClosedForm.toHolomorphicOneForm ω) γ
    γ.source γ.target

/-- **Inc 11b.8 (Step 11): smooth-cycle witness-form variant.** Line
integral of a closed 1-form over a SMOOTH loop vanishes when the
form's SMOOTH period homomorphism is zero. Sorry-free under the
hypothesis `hω : deRhamComparisonMap1_smooth X ω = 0` (which DOES
NOT reach the false-universal sorries) + explicit chart-C¹ witness
on the loop. -/
theorem ClosedForm.lineIntegral_loop_eq_zero_of_smooth_zero_periods
    {X : Type} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [JacobianChallenge.Periods.StableChartAt ℂ X]
    (ω : ClosedForm 1 X) (hω : deRhamComparisonMap1_smooth X ω = 0)
    {x : X} (γ : _root_.Path x x)
    (hγ : JacobianChallenge.TraceDegree.IsChartContDiffPath γ) :
    ClosedForm.lineIntegral ω γ = 0 := by
  -- ClosedForm.lineIntegral ω γ = pathIntegralViaCover ω γ by def.
  show pathIntegralViaCover (ClosedForm.toHolomorphicOneForm ω) γ = 0
  -- Bridge: this equals (deRhamComparisonMap1_smooth X ω) applied to the
  -- smooth chain cycle from γ.
  rw [← deRhamComparisonMap1_smooth_partitionChain_loop_eq ω hγ]
  rw [hω, LinearMap.zero_apply]

/-- A chosen path from a basepoint to a target on a connected
manifold. Constructed via `exists_chartContDiffPath_constantTail` so
that the path is chart-`C¹` *and* constant on a small interval near
its endpoint — the constant-tail property is needed by the flagship's
chart-local concatenation step (`Path.trans` is only chart-`C¹` at the
join when both side derivatives match; a constant tail makes one side
zero). -/
noncomputable def manifoldPathFromBasepoint
    {X : Type} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (x₀ x : X) : Path x₀ x :=
  (JacobianChallenge.Periods.exists_chartContDiffPath_constantTail x₀ x).choose

/-- **`manifoldPathFromBasepoint` is chart-`C¹`.** Sorry-free; extracts
the chart-`C¹` clause from `exists_chartContDiffPath_constantTail`'s
witness via `choose_spec.1`. -/
theorem manifoldPathFromBasepoint_isChartContDiffPath
    {X : Type} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (x₀ x : X) :
    JacobianChallenge.TraceDegree.IsChartContDiffPath
      (manifoldPathFromBasepoint x₀ x) :=
  (JacobianChallenge.Periods.exists_chartContDiffPath_constantTail x₀ x).choose_spec.1

/-- **`manifoldPathFromBasepoint` has a constant tail near its endpoint.**
Sorry-free; extracts the constant-tail clause from
`exists_chartContDiffPath_constantTail`'s witness via `choose_spec.2`.
The constant-tail property is consumed by
`IsChartContDiffPath.trans_of_constant_join` to discharge the trans-
witness obligations on the flagship descent. -/
theorem manifoldPathFromBasepoint_constantTail
    {X : Type} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (x₀ x : X) :
    ∃ ε > 0, ∀ t ∈ Set.Icc (1 - ε) (1 : ℝ),
      (manifoldPathFromBasepoint x₀ x).extend t = x :=
  (JacobianChallenge.Periods.exists_chartContDiffPath_constantTail x₀ x).choose_spec.2

/-- **Trans-witness for the flagship chart-local pattern** (Stage III).
The specific trans path `(manifoldPathFromBasepoint x₀ p).trans
(chartPullbackStraightPath p x …)` is `IsChartContDiffPath`. TRUE iff
`manifoldPathFromBasepoint x₀ p` is constructed to have a chart-derivative
matching the chart-pullback straight path's starting derivative at `p`
(e.g. via a constant tail / constant head construction in Increment 3+).

This sorry replaces B's role on the flagship descent at the
`pathPotential_chartLocal_eventually` → `pathPotential_concat` step. -/
theorem manifoldPathFromBasepoint_trans_chartPullbackStraightPathFullyWarmed_isChartContDiffPath
    {X : Type} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (x₀ p x : X) (r : ℝ) (hr_pos : 0 < r)
    (hr_subset : Metric.ball ((chartAt ℂ p) p) r ⊆ (chartAt ℂ p).target)
    (hx_ball : (chartAt ℂ p) x ∈ Metric.ball ((chartAt ℂ p) p) r)
    (hx_source : x ∈ (chartAt ℂ p).source)
    (ε : ℝ) (hε : 0 < ε ∧ ε < 1/2) :
    JacobianChallenge.TraceDegree.IsChartContDiffPath
      ((manifoldPathFromBasepoint x₀ p).trans
        (JacobianChallenge.Periods.chartPullbackStraightPathFullyWarmed p x r hr_pos
          hr_subset hx_ball hx_source ε hε)) := by
  obtain ⟨εL, hεL_pos, hL_tail⟩ := manifoldPathFromBasepoint_constantTail x₀ p
  set εL' : ℝ := min εL 1 with hεL'_def
  have hεL'_pos : 0 < εL' := lt_min hεL_pos one_pos
  have hεL'_le : εL' ≤ 1 := min_le_right _ _
  have hL_tail' : ∀ t ∈ Set.Icc (1 - εL') 1, (manifoldPathFromBasepoint x₀ p).extend t = p := by
    intro t ⟨ht_lb, ht_ub⟩
    have h_min_le : εL' ≤ εL := min_le_left _ _
    refine hL_tail t ⟨?_, ht_ub⟩
    linarith
  have hε_le_one : ε ≤ 1 := le_of_lt (lt_trans hε.2 (by norm_num : (1:ℝ)/2 < 1))
  have h_head_property :
      ∀ t ∈ Set.Icc (0 : ℝ) ε,
        (JacobianChallenge.Periods.chartPullbackStraightPathFullyWarmed
          p x r hr_pos hr_subset hx_ball hx_source ε hε).extend t = p := by
    intro t ⟨ht_lb, ht_ub⟩
    exact JacobianChallenge.Periods.chartPullbackStraightPathFullyWarmed_extend_eq_source
      p x r hr_pos hr_subset hx_ball hx_source ε hε t ht_lb ht_ub
  exact IsChartContDiffPath.trans_of_constant_join
    (manifoldPathFromBasepoint_isChartContDiffPath x₀ p)
    (JacobianChallenge.Periods.chartPullbackStraightPathFullyWarmed_isChartContDiffPath
      p x r hr_pos hr_subset hx_ball hx_source ε hε)
    hεL'_pos hεL'_le hL_tail'
    hε.1 hε_le_one h_head_property

/-- **Loop-trans-witness for the flagship chart-local pattern** (Stage III).
The triple-trans `(manifoldPathFromBasepoint x₀ x).trans
((manifoldPathFromBasepoint x₀ p).trans (chartPullbackStraightPath p x …)).symm`
is `IsChartContDiffPath`. This is the loop-witness needed by
`pathPotential_eq_lineIntegral_of_witnesses` (path-independence via
`lineIntegral_eq_of_zero_periods_of_witnesses`).

TRUE iff the underlying `manifoldPathFromBasepoint` constructions and the
chart-pullback straight path have compatible chart-derivatives at their
joins; dischargeable in Increment 3+ alongside the simpler outer trans. -/
theorem manifoldPathFromBasepoint_loop_chartPullbackStraightPathFullyWarmed_isChartContDiffPath
    {X : Type} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (x₀ p x : X) (r : ℝ) (hr_pos : 0 < r)
    (hr_subset : Metric.ball ((chartAt ℂ p) p) r ⊆ (chartAt ℂ p).target)
    (hx_ball : (chartAt ℂ p) x ∈ Metric.ball ((chartAt ℂ p) p) r)
    (hx_source : x ∈ (chartAt ℂ p).source)
    (ε : ℝ) (hε : 0 < ε ∧ ε < 1/2) :
    JacobianChallenge.TraceDegree.IsChartContDiffPath
      ((manifoldPathFromBasepoint x₀ x).trans
        ((manifoldPathFromBasepoint x₀ p).trans
          (JacobianChallenge.Periods.chartPullbackStraightPathFullyWarmed p x r hr_pos
            hr_subset hx_ball hx_source ε hε)).symm) := by
  -- Inner trans: manifoldPath(x₀, p) .trans fullyWarmedCPS(p, x). IsChartContDiffPath via outer discharge.
  have h_inner_chartC1 :
      JacobianChallenge.TraceDegree.IsChartContDiffPath
        ((manifoldPathFromBasepoint x₀ p).trans
          (JacobianChallenge.Periods.chartPullbackStraightPathFullyWarmed
            p x r hr_pos hr_subset hx_ball hx_source ε hε)) :=
    manifoldPathFromBasepoint_trans_chartPullbackStraightPathFullyWarmed_isChartContDiffPath
      x₀ p x r hr_pos hr_subset hx_ball hx_source ε hε
  -- Its .symm is IsChartContDiffPath via the .symm preservation lemma.
  have h_inner_symm_chartC1 :=
    JacobianChallenge.TraceDegree.IsChartContDiffPath.symm h_inner_chartC1
  -- The inner trans has constant tail at x on [1 - ε/2, 1]:
  -- For t ∈ (1/2, 1], (inner_trans).extend t = fullyWarmedCPS.extend(2t - 1).
  -- 2t - 1 ∈ (0, 1]. For t ≥ 1 - ε/2, 2t - 1 ≥ 1 - ε, so fullyWarmedCPS's tail kicks in.
  set γ_inner := (manifoldPathFromBasepoint x₀ p).trans
        (JacobianChallenge.Periods.chartPullbackStraightPathFullyWarmed
          p x r hr_pos hr_subset hx_ball hx_source ε hε) with hγ_inner_def
  have h_inner_tail : ∀ t ∈ Set.Icc (1 - ε / 2) (1 : ℝ), γ_inner.extend t = x := by
    intro t ⟨ht_lb, ht_ub⟩
    have hε_half_pos : 0 < ε / 2 := by linarith [hε.1]
    have hε_half_lt_half : ε / 2 < 1 / 2 := by linarith [hε.2]
    have ht_pos : 0 < t := by linarith
    have ht_gt_half : 1 / 2 < t := by linarith
    have ht_unit : t ∈ unitInterval := ⟨le_of_lt ht_pos, ht_ub⟩
    -- (γ_inner).extend t = (Path.trans).toFun ⟨t, ht_unit⟩.
    rw [γ_inner.extend_extends' ⟨t, ht_unit⟩]
    show (Path.trans (manifoldPathFromBasepoint x₀ p) _).toFun ⟨t, ht_unit⟩ = x
    simp only [Path.trans, Path.coe_mk_mk, Function.comp]
    rw [if_neg (not_le.mpr ht_gt_half)]
    -- Goal: chartPullbackStraightPathFullyWarmed.extend (2t - 1) = x.
    have h2t1_in : (2 * t - 1) ∈ Set.Icc (1 - ε) (1 : ℝ) := by
      constructor
      · linarith
      · linarith
    exact JacobianChallenge.Periods.chartPullbackStraightPathFullyWarmed_extend_eq_target
      p x r hr_pos hr_subset hx_ball hx_source ε hε (2 * t - 1) h2t1_in.1 h2t1_in.2
  -- inner_trans.symm has constant head at x on [0, ε/2]: by extend_symm_apply.
  have h_inner_symm_head : ∀ t ∈ Set.Icc (0 : ℝ) (ε / 2), γ_inner.symm.extend t = x := by
    intro t ⟨ht_lb, ht_ub⟩
    rw [γ_inner.extend_symm_apply t]
    apply h_inner_tail
    have hε_half_le_half : ε / 2 ≤ 1 / 2 := by linarith [hε.2]
    refine ⟨?_, ?_⟩
    · linarith
    · linarith
  -- Apply trans_of_constant_join.
  obtain ⟨εL, hεL_pos, hL_tail⟩ := manifoldPathFromBasepoint_constantTail x₀ x
  set εL' : ℝ := min εL 1 with hεL'_def
  have hεL'_pos : 0 < εL' := lt_min hεL_pos one_pos
  have hεL'_le : εL' ≤ 1 := min_le_right _ _
  have hL_tail' : ∀ t ∈ Set.Icc (1 - εL') 1, (manifoldPathFromBasepoint x₀ x).extend t = x := by
    intro t ⟨ht_lb, ht_ub⟩
    have h_min_le : εL' ≤ εL := min_le_left _ _
    refine hL_tail t ⟨?_, ht_ub⟩
    linarith
  have hε_half_pos : 0 < ε / 2 := by linarith [hε.1]
  have hε_half_le_one : ε / 2 ≤ 1 := by linarith [hε.2]
  exact IsChartContDiffPath.trans_of_constant_join
    (manifoldPathFromBasepoint_isChartContDiffPath x₀ x)
    h_inner_symm_chartC1
    hεL'_pos hεL'_le hL_tail'
    hε_half_pos hε_half_le_one h_inner_symm_head

/-- **Inc 11b.8 (Step 11): smooth-cycle path-independence.** Same
conclusion as `lineIntegral_eq_of_zero_periods_of_witnesses` but with
`hω : deRhamComparisonMap1_smooth X ω = 0` (sorry-free closure).
Takes chart-C¹ witnesses for both paths and their trans-symm loop. -/
theorem ClosedForm.lineIntegral_eq_of_smooth_zero_periods
    {X : Type} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [JacobianChallenge.Periods.StableChartAt ℂ X]
    (ω : ClosedForm 1 X) (hω : deRhamComparisonMap1_smooth X ω = 0)
    {x y : X} (γ₀ γ₁ : _root_.Path x y)
    (hγ₀ : JacobianChallenge.TraceDegree.IsChartContDiffPath γ₀)
    (hγ₁ : JacobianChallenge.TraceDegree.IsChartContDiffPath γ₁)
    (htrans : JacobianChallenge.TraceDegree.IsChartContDiffPath
      (γ₀.trans γ₁.symm)) :
    ClosedForm.lineIntegral ω γ₀ = ClosedForm.lineIntegral ω γ₁ := by
  have hloop : ClosedForm.lineIntegral ω (γ₀.trans γ₁.symm) = 0 :=
    ClosedForm.lineIntegral_loop_eq_zero_of_smooth_zero_periods ω hω
      (γ₀.trans γ₁.symm) htrans
  have hadd : ClosedForm.lineIntegral ω (γ₀.trans γ₁.symm)
              = ClosedForm.lineIntegral ω γ₀ + ClosedForm.lineIntegral ω γ₁.symm :=
    ClosedForm.lineIntegral_trans_of_witnesses ω γ₀ γ₁.symm hγ₀ hγ₁.symm htrans
  have hsym : ClosedForm.lineIntegral ω γ₁.symm = - ClosedForm.lineIntegral ω γ₁ :=
    ClosedForm.lineIntegral_symm_of_witnesses ω γ₁ hγ₁ hγ₁.symm
  have hzero : ClosedForm.lineIntegral ω γ₀ + (- ClosedForm.lineIntegral ω γ₁) = 0 := by
    calc ClosedForm.lineIntegral ω γ₀ + (- ClosedForm.lineIntegral ω γ₁)
        = ClosedForm.lineIntegral ω γ₀ + ClosedForm.lineIntegral ω γ₁.symm := by rw [hsym]
      _ = ClosedForm.lineIntegral ω (γ₀.trans γ₁.symm) := hadd.symm
      _ = 0 := hloop
  linear_combination hzero

/-! ### Inc 11b.8 (Step 11 cascade): smooth-cycle flagship variant.

The following declarations build a parallel `_smooth` cascade of the
path-potential and chart-local FTC pipeline, consuming the smooth
hypothesis `hω : deRhamComparisonMap1_smooth X ω = 0`. Each smooth
helper mirrors an existing helper whose closure reaches the universal-
false sorries; the smooth variants close their closures through the
sorry-free `_smooth_zero_periods` and `_of_witnesses` machinery
established earlier. The terminal flagship
`closedForm_pathIntegral_primitive_exists_smooth` is sorry-free under
`#print axioms`. -/

/-- **Smooth-cycle path-integral primitive.** Same body as
`pathPotential`, consuming the smooth-cycle hypothesis instead of the
universal-cycle one. The hypothesis is unused in the body; it is
recorded for downstream consumers (path-independence and concat
lemmas) to invoke. -/
noncomputable def ClosedForm.pathPotential_smooth
    {X : Type} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [JacobianChallenge.Periods.StableChartAt ℂ X]
    (ω : ClosedForm 1 X)
    (_hω : deRhamComparisonMap1_smooth X ω = 0)
    (x₀ x : X) : ℂ :=
  ClosedForm.lineIntegral ω (manifoldPathFromBasepoint x₀ x)

/-- Path-independence for `pathPotential_smooth` (witness form).
The potential equals the line integral along ANY chart-C¹ alternative
path `η`, provided the trans-symm loop is chart-C¹. Sorry-free via
`lineIntegral_eq_of_smooth_zero_periods`. -/
theorem ClosedForm.pathPotential_smooth_eq_lineIntegral_of_witnesses
    {X : Type} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [JacobianChallenge.Periods.StableChartAt ℂ X]
    (ω : ClosedForm 1 X)
    (hω : deRhamComparisonMap1_smooth X ω = 0)
    (x₀ x : X) (η : _root_.Path x₀ x)
    (hη : JacobianChallenge.TraceDegree.IsChartContDiffPath η)
    (htrans : JacobianChallenge.TraceDegree.IsChartContDiffPath
      ((manifoldPathFromBasepoint x₀ x).trans η.symm)) :
    ClosedForm.pathPotential_smooth ω hω x₀ x = ClosedForm.lineIntegral ω η :=
  ClosedForm.lineIntegral_eq_of_smooth_zero_periods ω hω
    (manifoldPathFromBasepoint x₀ x) η
    (manifoldPathFromBasepoint_isChartContDiffPath x₀ x) hη htrans

/-- Concat for `pathPotential_smooth` (witness form). The potential at
endpoint of a path equals the potential at the start plus the line
integral. Sorry-free via `_smooth_eq_lineIntegral_of_witnesses` and
`lineIntegral_trans_of_witnesses`. -/
theorem ClosedForm.pathPotential_smooth_concat_of_witnesses
    {X : Type} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [JacobianChallenge.Periods.StableChartAt ℂ X]
    (ω : ClosedForm 1 X)
    (hω : deRhamComparisonMap1_smooth X ω = 0)
    (x₀ x y : X) (γ : _root_.Path x y)
    (hγ : JacobianChallenge.TraceDegree.IsChartContDiffPath γ)
    (htrans_outer : JacobianChallenge.TraceDegree.IsChartContDiffPath
      ((manifoldPathFromBasepoint x₀ x).trans γ))
    (htrans_loop : JacobianChallenge.TraceDegree.IsChartContDiffPath
      ((manifoldPathFromBasepoint x₀ y).trans
        ((manifoldPathFromBasepoint x₀ x).trans γ).symm)) :
    ClosedForm.pathPotential_smooth ω hω x₀ y =
      ClosedForm.pathPotential_smooth ω hω x₀ x + ClosedForm.lineIntegral ω γ := by
  rw [ClosedForm.pathPotential_smooth_eq_lineIntegral_of_witnesses ω hω x₀ y
        ((manifoldPathFromBasepoint x₀ x).trans γ) htrans_outer htrans_loop]
  rw [ClosedForm.lineIntegral_trans_of_witnesses ω
        (manifoldPathFromBasepoint x₀ x) γ
        (manifoldPathFromBasepoint_isChartContDiffPath x₀ x) hγ htrans_outer]
  rfl

/-- Smooth-cycle variant of `pathPotential_chartLocal_eventually`. Same
body, smooth hypothesis, sorry-free closure. -/
private theorem pathPotential_smooth_chartLocal_eventually
    {X : Type} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [JacobianChallenge.Periods.StableChartAt ℂ X]
    (ω : ClosedForm 1 X) (hω : deRhamComparisonMap1_smooth X ω = 0)
    (x₀ : X) (p : X) (r : ℝ) (hr_pos : 0 < r)
    (hr_subset : Metric.ball ((chartAt ℂ p) p) r ⊆ (chartAt ℂ p).target)
    (F : ℂ → ℂ)
    (hF : ∀ z ∈ Metric.ball ((chartAt ℂ p) p) r,
            HasDerivAt F
              (JacobianChallenge.Periods.chartPullbackFun (chartAt ℂ p)
                (ClosedForm.toHolomorphicOneForm ω) z) z) :
    ∀ᶠ x in 𝓝 p,
      ClosedForm.pathPotential_smooth ω hω x₀ x =
        (ClosedForm.pathPotential_smooth ω hω x₀ p - F ((chartAt ℂ p) p))
          + F ((chartAt ℂ p) x) := by
  filter_upwards [JacobianChallenge.Periods.chartAt_preimage_ball_mem_nhds p r hr_pos]
    with x hx
  obtain ⟨hx_ball, hx_source⟩ := hx
  set ε_warmup : ℝ := 1 / 4 with hε_warmup_def
  have hε_warmup : (0 : ℝ) < ε_warmup ∧ ε_warmup < 1/2 := ⟨by norm_num, by norm_num⟩
  set γ := JacobianChallenge.Periods.chartPullbackStraightPathFullyWarmed p x r hr_pos hr_subset
      hx_ball hx_source ε_warmup hε_warmup with hγ_def
  have h_γ_isChartContDiff :
      JacobianChallenge.TraceDegree.IsChartContDiffPath γ :=
    JacobianChallenge.Periods.chartPullbackStraightPathFullyWarmed_isChartContDiffPath
      p x r hr_pos hr_subset hx_ball hx_source ε_warmup hε_warmup
  have h_trans_outer :
      JacobianChallenge.TraceDegree.IsChartContDiffPath
        ((manifoldPathFromBasepoint x₀ p).trans γ) :=
    manifoldPathFromBasepoint_trans_chartPullbackStraightPathFullyWarmed_isChartContDiffPath
      x₀ p x r hr_pos hr_subset hx_ball hx_source ε_warmup hε_warmup
  have h_trans_loop :
      JacobianChallenge.TraceDegree.IsChartContDiffPath
        ((manifoldPathFromBasepoint x₀ x).trans
          ((manifoldPathFromBasepoint x₀ p).trans γ).symm) :=
    manifoldPathFromBasepoint_loop_chartPullbackStraightPathFullyWarmed_isChartContDiffPath
      x₀ p x r hr_pos hr_subset hx_ball hx_source ε_warmup hε_warmup
  have h_concat :
      ClosedForm.pathPotential_smooth ω hω x₀ x =
        ClosedForm.pathPotential_smooth ω hω x₀ p + ClosedForm.lineIntegral ω γ :=
    ClosedForm.pathPotential_smooth_concat_of_witnesses ω hω x₀ p x γ
      h_γ_isChartContDiff h_trans_outer h_trans_loop
  have h_range : Set.range γ ⊆ (chartAt ℂ p).source :=
    JacobianChallenge.Periods.chartPullbackStraightPathFullyWarmed_range_subset_source
      p x r hr_pos hr_subset hx_ball hx_source ε_warmup hε_warmup
  have h_lift_in_ball : ∀ t : unitInterval,
      (chartAt ℂ p) (γ t) ∈ Metric.ball ((chartAt ℂ p) p) r := fun t =>
    JacobianChallenge.Periods.chartPullbackStraightPathFullyWarmed_image_in_ball
      p x r hr_pos hr_subset hx_ball hx_source ε_warmup hε_warmup t
  have h_line_integral_eq :
      ClosedForm.lineIntegral ω γ = F ((chartAt ℂ p) x) - F ((chartAt ℂ p) p) := by
    show JacobianChallenge.Periods.pathIntegralViaCover (ClosedForm.toHolomorphicOneForm ω) γ
        = F ((chartAt ℂ p) x) - F ((chartAt ℂ p) p)
    exact JacobianChallenge.Periods.pathIntegralViaCover_eq_primitive_diff_of_witnesses
      (ClosedForm.toHolomorphicOneForm ω) r hr_pos hr_subset hx_ball hF γ h_range h_lift_in_ball
      h_γ_isChartContDiff
  rw [h_concat, h_line_integral_eq]
  ring

/-- Smooth-cycle variant of `pathPotential_chartLocal_eventuallyEq`. -/
private theorem pathPotential_smooth_chartLocal_eventuallyEq
    {X : Type} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [JacobianChallenge.Periods.StableChartAt ℂ X]
    (ω : ClosedForm 1 X) (hω : deRhamComparisonMap1_smooth X ω = 0) (x₀ : X)
    (p : X) :
    ∃ (F : ℂ → ℂ) (c : ℂ) (r : ℝ) (_hr_pos : 0 < r)
        (_hr_subset : Metric.ball ((chartAt ℂ p) p) r ⊆ (chartAt ℂ p).target),
      (∀ z ∈ Metric.ball ((chartAt ℂ p) p) r,
          HasDerivAt F
            (JacobianChallenge.Periods.chartPullbackFun (chartAt ℂ p)
              (ClosedForm.toHolomorphicOneForm ω) z) z) ∧
      ContMDiffAt (modelWithCornersSelf ℂ ℂ)
        (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) F ((chartAt ℂ p) p) ∧
      ∀ᶠ x in 𝓝 p,
        ClosedForm.pathPotential_smooth ω hω x₀ x = c + F ((chartAt ℂ p) x) := by
  obtain ⟨r, hr_pos, hr_subset⟩ :=
    JacobianChallenge.Periods.exists_ballShaped_chartAt p
  set c := chartAt ℂ p with hc_def
  set α : HolomorphicOneForm ℂ X := ClosedForm.toHolomorphicOneForm ω with hα_def
  have h_diff_ball :
      DifferentiableOn ℂ
        (JacobianChallenge.Periods.chartPullbackFun c α)
        (Metric.ball (c p) r) :=
    (JacobianChallenge.Periods.chartPullbackFun_chartAt_differentiableOn p α).mono hr_subset
  obtain ⟨F, hF⟩ : Complex.IsExactOn
        (JacobianChallenge.Periods.chartPullbackFun c α)
        (Metric.ball (c p) r) :=
    h_diff_ball.isExactOn_ball
  have h_F_diff_ball : DifferentiableOn ℂ F (Metric.ball (c p) r) :=
    fun z hz => (hF z hz).differentiableAt.differentiableWithinAt
  have h_cp_mem_ball : c p ∈ Metric.ball (c p) r := Metric.mem_ball_self hr_pos
  have h_F_analytic : AnalyticAt ℂ F (c p) :=
    h_F_diff_ball.analyticOnNhd Metric.isOpen_ball (c p) h_cp_mem_ball
  have h_F_contMDiffAt :
      ContMDiffAt (modelWithCornersSelf ℂ ℂ)
        (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) F (c p) :=
    h_F_analytic.contDiffAt (n := (⊤ : WithTop ℕ∞)).contMDiffAt
  refine ⟨F,
    ClosedForm.pathPotential_smooth ω hω x₀ p - F (c p),
    r, hr_pos, hr_subset, hF, h_F_contMDiffAt, ?_⟩
  exact pathPotential_smooth_chartLocal_eventually ω hω x₀ p r hr_pos hr_subset F hF

/-- Smooth-cycle variant of `pathPotential_smooth` (smoothness of the
potential function). -/
private theorem pathPotential_smooth_isContMDiff
    {X : Type} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [JacobianChallenge.Periods.StableChartAt ℂ X]
    (ω : ClosedForm 1 X) (hω : deRhamComparisonMap1_smooth X ω = 0) (x₀ : X) :
    ContMDiff (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ)
              (⊤ : WithTop ℕ∞)
              (fun x => ClosedForm.pathPotential_smooth ω hω x₀ x) := by
  intro p
  obtain ⟨F, c, _r, _hr_pos, _hr_subset, _hF_primitive, hF_smooth, h_eq⟩ :=
    pathPotential_smooth_chartLocal_eventuallyEq ω hω x₀ p
  have h_chartAt_smooth :
      ContMDiffAt (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ)
        (⊤ : WithTop ℕ∞) (chartAt ℂ p) p :=
    (contMDiffOn_chart (n := (⊤ : WithTop ℕ∞)) (I := modelWithCornersSelf ℂ ℂ)
        (M := X) (x := p)).contMDiffAt
      ((chartAt ℂ p).open_source.mem_nhds (mem_chart_source ℂ p))
  have h_comp_smooth :
      ContMDiffAt (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ)
        (⊤ : WithTop ℕ∞) (fun x => F ((chartAt ℂ p) x)) p :=
    hF_smooth.comp p h_chartAt_smooth
  have h_target_smooth :
      ContMDiffAt (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ)
        (⊤ : WithTop ℕ∞) (fun x => c + F ((chartAt ℂ p) x)) p :=
    contMDiffAt_const.add h_comp_smooth
  exact h_target_smooth.congr_of_eventuallyEq h_eq

/-- Lift `pathPotential_smooth ω hω x₀` to a `SmoothDiffForm 0 X`. -/
noncomputable def ClosedForm.pathPotentialAsForm_smooth
    {X : Type} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [JacobianChallenge.Periods.StableChartAt ℂ X]
    (ω : ClosedForm 1 X) (hω : deRhamComparisonMap1_smooth X ω = 0)
    (x₀ : X) : SmoothDiffForm 0 X :=
  ⟨fun x => ClosedForm.pathPotential_smooth ω hω x₀ x,
    pathPotential_smooth_isContMDiff ω hω x₀⟩

/-- Smooth-cycle variant of `pathPotential_chartLocal_mfderiv_eq_omega`.
The hypothesis `_hω` is unused in the body — it carries through only
for signature compatibility with the smooth flagship descent. -/
private theorem pathPotential_smooth_chartLocal_mfderiv_eq_omega
    {X : Type} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [JacobianChallenge.Periods.StableChartAt ℂ X]
    (ω : ClosedForm 1 X) (_hω : deRhamComparisonMap1_smooth X ω = 0) (_x₀ : X)
    (p : X) (F : ℂ → ℂ) (c : ℂ) (r : ℝ) (hr_pos : 0 < r)
    (_hr_subset : Metric.ball ((chartAt ℂ p) p) r ⊆ (chartAt ℂ p).target)
    (hF_primitive : ∀ z ∈ Metric.ball ((chartAt ℂ p) p) r,
        HasDerivAt F (JacobianChallenge.Periods.chartPullbackFun (chartAt ℂ p)
          (ClosedForm.toHolomorphicOneForm ω) z) z) :
    mfderiv (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ)
      (fun y => c + F ((chartAt ℂ p) y)) p =
        ((ω : SmoothDiffForm 1 X) : HolomorphicOneForm ℂ X) p := by
  have h_chart_p_ball : (chartAt ℂ p) p ∈ Metric.ball ((chartAt ℂ p) p) r :=
    Metric.mem_ball_self hr_pos
  have h_F_hasDerivAt :
      HasDerivAt F
        (JacobianChallenge.Periods.chartPullbackFun (chartAt ℂ p)
          (ClosedForm.toHolomorphicOneForm ω) ((chartAt ℂ p) p))
        ((chartAt ℂ p) p) :=
    hF_primitive ((chartAt ℂ p) p) h_chart_p_ball
  have h_chart_left_inv :
      (chartAt ℂ p).symm ((chartAt ℂ p) p) = p :=
    (chartAt ℂ p).left_inv (mem_chart_source ℂ p)
  have h_chart_target : (chartAt ℂ p) p ∈ (chartAt ℂ p).target :=
    mem_chart_target ℂ p
  have h_chartPullback_at_basepoint :
      JacobianChallenge.Periods.chartPullbackFun (chartAt ℂ p)
        (ClosedForm.toHolomorphicOneForm ω) ((chartAt ℂ p) p) =
        ((ClosedForm.toHolomorphicOneForm ω).toFun p) (1 : ℂ) := by
    rw [JacobianChallenge.Periods.chartPullbackFun_apply,
        JacobianChallenge.Periods.chartedFormPullback_chartAt_eq_of_stable p
          (ClosedForm.toHolomorphicOneForm ω) h_chart_target,
        h_chart_left_inv]
    rfl
  have h_mfderiv_chart :
      mfderiv (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ)
        (chartAt ℂ p) p = ContinuousLinearMap.id ℂ ℂ := by
    haveI : IsManifold (modelWithCornersSelf ℂ ℂ) (1 : WithTop ℕ∞) X :=
      IsManifold.of_le le_top
    exact mfderiv_chartAt_eq_id_of_stable (I := modelWithCornersSelf ℂ ℂ) p
      (mem_chart_source ℂ p)
  have h_F_hasFDerivAt :
      HasFDerivAt F
        ((ContinuousLinearMap.id ℂ ℂ).smulRight
          (JacobianChallenge.Periods.chartPullbackFun (chartAt ℂ p)
            (ClosedForm.toHolomorphicOneForm ω) ((chartAt ℂ p) p)))
        ((chartAt ℂ p) p) :=
    h_F_hasDerivAt.hasFDerivAt
  have h_clm_smulRight :
      (ContinuousLinearMap.id ℂ ℂ).smulRight
          (((ClosedForm.toHolomorphicOneForm ω).toFun p) (1 : ℂ))
        = (ClosedForm.toHolomorphicOneForm ω).toFun p := by
    refine ContinuousLinearMap.ext fun w => ?_
    show w • ((ClosedForm.toHolomorphicOneForm ω).toFun p) (1 : ℂ)
        = ((ClosedForm.toHolomorphicOneForm ω).toFun p) w
    have hw : w = w • (1 : ℂ) := by simp
    conv_rhs => rw [hw, ((ClosedForm.toHolomorphicOneForm ω).toFun p).map_smul]
  have h_const_add_F :
      HasMFDerivAt (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ)
        (fun w : ℂ => c + F w)
        ((chartAt ℂ p) p)
        ((ContinuousLinearMap.id ℂ ℂ).smulRight
          (JacobianChallenge.Periods.chartPullbackFun (chartAt ℂ p)
            (ClosedForm.toHolomorphicOneForm ω) ((chartAt ℂ p) p))) := by
    rw [hasMFDerivAt_iff_hasFDerivAt]
    exact h_F_hasFDerivAt.const_add c
  have h_chart_hasMFDeriv :
      HasMFDerivAt (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ)
        (chartAt ℂ p) p (ContinuousLinearMap.id ℂ ℂ) := by
    haveI : IsManifold (modelWithCornersSelf ℂ ℂ) (1 : WithTop ℕ∞) X :=
      IsManifold.of_le le_top
    have h_mdiff : MDifferentiableAt
        (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ)
        (chartAt ℂ p) p :=
      (mdifferentiable_of_mem_atlas (chart_mem_atlas ℂ p)).mdifferentiableAt
        (mem_chart_source ℂ p)
    convert h_mdiff.hasMFDerivAt
    exact h_mfderiv_chart.symm
  have h_comp_hasMFDeriv :
      HasMFDerivAt (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ)
        (fun y => c + F ((chartAt ℂ p) y)) p
        (((ContinuousLinearMap.id ℂ ℂ).smulRight
            (JacobianChallenge.Periods.chartPullbackFun (chartAt ℂ p)
              (ClosedForm.toHolomorphicOneForm ω) ((chartAt ℂ p) p))).comp
          (ContinuousLinearMap.id ℂ ℂ)) :=
    h_const_add_F.comp p h_chart_hasMFDeriv
  have h_mfderiv_eq := h_comp_hasMFDeriv.mfderiv
  rw [h_mfderiv_eq, h_chartPullback_at_basepoint]
  refine ContinuousLinearMap.ext fun w => ?_
  have h_pt := congr_fun (congrArg DFunLike.coe h_clm_smulRight) w
  exact h_pt

/-- Smooth-cycle variant of
`ClosedForm.pathPotentialAsForm_exteriorDerivative`. -/
theorem ClosedForm.pathPotentialAsForm_smooth_exteriorDerivative
    {X : Type} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [JacobianChallenge.Periods.StableChartAt ℂ X]
    (ω : ClosedForm 1 X) (hω : deRhamComparisonMap1_smooth X ω = 0) (x₀ : X) :
    exteriorDerivative 0 X (ClosedForm.pathPotentialAsForm_smooth ω hω x₀) =
      (ω : SmoothDiffForm 1 X) := by
  apply ContMDiffSection.coe_inj
  funext p
  show mfderiv (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ)
        (fun y => ClosedForm.pathPotential_smooth ω hω x₀ y) p =
      ((ω : SmoothDiffForm 1 X) : HolomorphicOneForm ℂ X) p
  obtain ⟨F, c, r, hr_pos, hr_subset, hF_primitive, _hF_smooth, h_eq⟩ :=
    pathPotential_smooth_chartLocal_eventuallyEq ω hω x₀ p
  rw [Filter.EventuallyEq.mfderiv_eq
        (h_eq : (fun y => ClosedForm.pathPotential_smooth ω hω x₀ y) =ᶠ[𝓝 p] _)]
  exact pathPotential_smooth_chartLocal_mfderiv_eq_omega
    ω hω x₀ p F c r hr_pos hr_subset hF_primitive

/-- **Smooth-cycle flagship.** A closed 1-form whose smooth-cycle
period functional vanishes admits a global smooth 0-form whose
exterior derivative is the form. Sorry-free closure under
`#print axioms`: this is the soundness milestone of Inc 11b.8. -/
theorem closedForm_pathIntegral_primitive_exists_smooth
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [JacobianChallenge.Periods.StableChartAt ℂ X]
    (ω : ClosedForm 1 X)
    (hω : deRhamComparisonMap1_smooth X ω = 0) :
    ∃ θ : SmoothDiffForm 0 X, exteriorDerivative 0 X θ = (ω : SmoothDiffForm 1 X) := by
  obtain ⟨x₀⟩ := (inferInstance : Nonempty X)
  exact ⟨ClosedForm.pathPotentialAsForm_smooth ω hω x₀,
         ClosedForm.pathPotentialAsForm_smooth_exteriorDerivative ω hω x₀⟩

/-- **Injectivity sub-obligation 1a (existence of path-integral
primitive) — PR 158 main theorem, smooth-cycle discharge.** A closed
1-form whose **smooth-cycle** period functional vanishes admits a
global smooth 0-form whose exterior derivative is the original form.

**Inc 12.6 refactor (2026-05-15):** the hypothesis was changed from
`deRhamComparisonMap1 X ω = 0` (the universal-cycle map, defined
through `chainPairing_kills_boundary` which carries reachable
sorries) to `deRhamComparisonMap1_smooth X ω = 0` (the smooth-cycle
map, defined sorry-free via `smoothSingChain1Submodule`). The body
delegates to `closedForm_pathIntegral_primitive_exists_smooth`, whose
`#print axioms` closure is already standard-axioms-only.

This is the honest discharge path that PR 158 itself documented in
its Triage section: "a refinement of `deRhamComparisonMap1` into a
concrete `def` together with a proof that it is injective." The
smooth-cycle map IS that refinement; this rewires the named flagship
to consume it. -/
theorem closedForm_pathIntegral_primitive_exists
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [JacobianChallenge.Periods.StableChartAt ℂ X]
    (ω : ClosedForm 1 X)
    (hω : deRhamComparisonMap1_smooth X ω = 0) :
    ∃ θ : SmoothDiffForm 0 X, exteriorDerivative 0 X θ = (ω : SmoothDiffForm 1 X) :=
  closedForm_pathIntegral_primitive_exists_smooth X ω hω

/-- **Injectivity sub-obligation 1 (path-integral primitive).**
A closed 1-form whose smooth-cycle period functional vanishes
defines a global smooth 0-form via path integration. Defined as the
`Exists.choose` of `closedForm_pathIntegral_primitive_exists`. -/
noncomputable def closedForm_pathIntegral_primitive
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [JacobianChallenge.Periods.StableChartAt ℂ X]
    (ω : ClosedForm 1 X)
    (hω : deRhamComparisonMap1_smooth X ω = 0) :
    SmoothDiffForm 0 X :=
  (closedForm_pathIntegral_primitive_exists X ω hω).choose

/-- **Injectivity sub-obligation 2 (derivative correctness).**
The exterior derivative of the path-integral primitive is the original 1-form.
Proved from the specification of `closedForm_pathIntegral_primitive_exists`. -/
theorem closedForm_pathIntegral_primitive_derivative
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [JacobianChallenge.Periods.StableChartAt ℂ X]
    (ω : ClosedForm 1 X)
    (hω : deRhamComparisonMap1_smooth X ω = 0) :
    exteriorDerivative 0 X (closedForm_pathIntegral_primitive X ω hω) = (ω : SmoothDiffForm 1 X) :=
  (closedForm_pathIntegral_primitive_exists X ω hω).choose_spec

/-- **Injectivity sub-obligation (zero smooth-cycle periods give a global
potential).** If a closed 1-form has zero smooth-cycle comparison
functional, then it is the exterior derivative of a smooth 0-form.

This is the constructive heart of the injectivity half of de Rham:
the potential is obtained by integrating the closed form along paths
and using zero periods to prove path-independence. The final kernel
statement below is only the range-membership packaging of this
potential. -/
theorem deRhamComparisonMap1_zero_period_potential
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [JacobianChallenge.Periods.StableChartAt ℂ X]
    (ω : ClosedForm 1 X)
    (hω : deRhamComparisonMap1_smooth X ω = 0) :
    ∃ θ : SmoothDiffForm 0 X, exteriorDerivative 0 X θ = (ω : SmoothDiffForm 1 X) := by
  exact ⟨closedForm_pathIntegral_primitive X ω hω, closedForm_pathIntegral_primitive_derivative X ω hω⟩

/-- **Smooth-cycle chain-Stokes vanishing on `mfderivAsForm θ`.**
Smooth-cycle parallel of `deRhamComparisonMap1_vanishes_on_mfderiv`,
avoiding the homology descent (which would route through
`chainPairing_kills_boundary`). Routes through the chain-Stokes
factorization `chainPairing dθ = K.d ≫ θBoundary θ` and uses the
smooth chain-cycle's boundary-zero clause directly. -/
theorem deRhamComparisonMap1_smooth_vanishes_on_mfderiv
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [JacobianChallenge.Periods.StableChartAt ℂ X]
    (θ : SmoothDiffForm 0 X) :
    deRhamComparisonMap1_smooth X
        ⟨mfderivAsForm θ,
         by
           show mfderivAsForm θ ∈ LinearMap.ker (exteriorDerivative 1 X)
           rw [LinearMap.mem_ker]; rfl⟩ = 0 := by
  apply LinearMap.ext
  rintro ⟨c, hc⟩
  show (chainPairing _).hom c = 0
  -- Inc D.3.b's smooth chain-Stokes (per-chain version, requires
  -- `IsContDiffOneChain c`, which `hc.1` provides) factors the LHS
  -- through `θBoundary` ∘ `∂`, and the boundary `(K.d 1 0).hom c`
  -- vanishes by the smooth chain-CYCLE clause `hc.2` (kernel
  -- membership).
  have hboundary : (((JacobianChallenge.Blueprint.Sec03.singularChainComplexZ X).d 1 0).hom) c = 0 :=
    LinearMap.mem_ker.mp hc.2
  rw [chainPairing_mfderivAsForm_eq_d_comp_θBoundary_apply_of_smooth X θ c hc.1,
      hboundary, LinearMap.map_zero]

/-- **Smooth-cycle injectivity (closed and zero smooth periods ⇒ exact).**
A closed 1-form whose smooth-cycle period functional vanishes lies in
the exact submodule. Sorry-free parallel of
`deRhamComparisonMap1_kernel_subset_exact`, routed through the smooth
flagship. Downstream consumers of the kernel-subset-exact identity can
be rewired to consume this variant once they have access to the
smooth-cycle hypothesis. -/
theorem deRhamComparisonMap1_smooth_kernel_subset_exact
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [JacobianChallenge.Periods.StableChartAt ℂ X]
    (ω : ClosedForm 1 X)
    (hω : deRhamComparisonMap1_smooth X ω = 0) :
    (ω : SmoothDiffForm 1 X) ∈ ExactForm 0 X := by
  rw [ExactForm]
  exact closedForm_pathIntegral_primitive_exists_smooth X ω hω

/-! ### Inc D.2: smooth-cycle de Rham LinearEquiv (post-unhook plan)

The smooth-cycle parallel of the deleted `deRhamH1_linearEquiv`. Built
via first iso theorem on `deRhamComparisonMap1_smooth`:

```
deRhamH1Cocycle X ≃ₗ[ℂ] (smoothOneChainCycleSubmodule X →ₗ[ℤ] ℂ)
```

Sub-obligations (sub-sorries):
- `comparison_ker_eq_exact_smooth` — kernel of the smooth-cycle map
  equals the exact-form submodule (de Rham injectivity, smooth side).
- `comparison_range_eq_top_smooth` — range of the smooth-cycle map is
  all of `smoothOneChainCycleSubmodule X →ₗ[ℤ] ℂ` (de Rham surjectivity,
  smooth side; frontier).

Both are textbook results restricted to smooth chain-cycles; the
`comparison_ker_eq_exact_smooth` half is the analytic content that
Inc D.3 (per-simplex smooth FTC + chain-Stokes via span induction)
will discharge sorry-free. -/

/-- **Inc D.3.c (vanishes-on-exact, smooth-cycle).** A closed 1-form that
lies in the exact submodule has vanishing smooth-cycle period functional.
Smooth-cycle parallel of the deleted universal-cycle
`deRhamComparisonMap1_vanishes_on_exact`.

`rcases` extracts a primitive `θ` with `exteriorDerivative 0 X θ = ω.val`;
then `ω` itself equals (the closed-form lift of) `mfderivAsForm θ`, so
its smooth-cycle pairing reduces to
`deRhamComparisonMap1_smooth_vanishes_on_mfderiv` (which still inherits
sorry through `pairOnSimplexC_mfderivAsForm`; Inc D.3.a + D.3.b will
discharge that sub-sorry). -/
theorem deRhamComparisonMap1_smooth_vanishes_on_exact
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [JacobianChallenge.Periods.StableChartAt ℂ X]
    (η : ClosedFormSub 1 X)
    (hη : η ∈ ExactForm.toClosedSubmodule 0 X) :
    deRhamComparisonMap1_smooth X η = 0 := by
  -- Unfold membership: η.val = exteriorDerivative 0 X θ for some θ.
  rcases hη with ⟨θ, hθ⟩
  -- `exteriorDerivative 0 X θ = mfderivAsForm θ` by definitional `rfl` on
  -- the `n = 0` branch of `exteriorDerivative`.
  -- So η as a `ClosedFormSub` is `⟨mfderivAsForm θ, _⟩`.
  have hη_eq : η = ⟨mfderivAsForm θ,
      by show mfderivAsForm θ ∈ LinearMap.ker (exteriorDerivative 1 X)
         rw [LinearMap.mem_ker]; rfl⟩ := by
    apply Subtype.ext
    exact hθ.symm
  rw [hη_eq]
  exact deRhamComparisonMap1_smooth_vanishes_on_mfderiv X θ

/-- **Frontier sub-obligation (Inc D.2, half 1) — discharged via D.3.c.**
Kernel of the smooth de Rham comparison map equals the exact 1-form
submodule. The smooth-cycle parallel of the deleted universal-cycle
`comparison_ker_eq_exact`, now provable by combining the two halves:
- (⊆) `deRhamComparisonMap1_smooth_kernel_subset_exact` (sorry-free,
  from the smooth flagship).
- (⊇) `deRhamComparisonMap1_smooth_vanishes_on_exact` (new in D.3.c,
  reduces to `deRhamComparisonMap1_smooth_vanishes_on_mfderiv`).

Sorry inheritance: the ⊇ direction still propagates sorry through
`chainPairing_mfderivAsForm_eq_d_comp_θBoundary` → `pairOnSimplexC_mfderivAsForm`
(universal-form per-simplex FTC). Inc D.3.a will discharge that sub-sorry
sorry-free with `pairOnSimplexC_mfderivAsForm_of_smooth` (per-simplex FTC
restricted to smooth simplices) + Inc D.3.b's smooth chain-Stokes via span
induction. -/
theorem comparison_ker_eq_exact_smooth
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [JacobianChallenge.Periods.StableChartAt ℂ X] :
    LinearMap.ker (deRhamComparisonMap1_smooth X)
      = ExactForm.toClosedSubmodule 0 X := by
  ext η
  constructor
  · intro hη
    show (ClosedForm 1 X).subtype η ∈ ExactForm 0 X
    exact deRhamComparisonMap1_smooth_kernel_subset_exact X η
      (LinearMap.mem_ker.mp hη)
  · intro hη
    apply LinearMap.mem_ker.mpr
    exact deRhamComparisonMap1_smooth_vanishes_on_exact X η hη

/-- **Frontier sub-obligation (Inc D.2, half 2).** Range of the smooth
de Rham comparison map is all of `smoothOneChainCycleSubmodule X →ₗ[ℤ] ℂ`.
Surjectivity of the smooth-cycle period pairing: every ℤ-linear
functional on smooth 1-chain cycles is realized by integrating some
closed 1-form.

Frontier obligation. The deleted universal-cycle parallel
`deRhamComparisonMap1_surjective` routed through `closed_form_from_cech_cocycle`
+ `integral_closed_form_from_cech_eq` (Čech-cohomology surjectivity, also
absent from Mathlib v4.28.0). The smooth-cycle version may admit a more
direct proof using harmonic representatives (Hodge theory on a compact
Riemann surface), or by porting the universal-cycle argument with
chart-local primitives restricted to smooth chains. Inc D.5 will
investigate. -/
theorem comparison_range_eq_top_smooth
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [JacobianChallenge.Periods.StableChartAt ℂ X] :
    LinearMap.range (deRhamComparisonMap1_smooth X) = ⊤ :=
  sorry

/-- **Smooth-cycle de Rham LinearEquiv (Inc D.2 main).** The smooth de
Rham comparison map descends to a ℂ-linear equivalence

```
deRhamH1Cocycle X ≃ₗ[ℂ] (smoothOneChainCycleSubmodule X →ₗ[ℤ] ℂ).
```

Built via the first isomorphism theorem from
`comparison_ker_eq_exact_smooth` (kernel) and
`comparison_range_eq_top_smooth` (range). Same pattern as the deleted
universal-cycle `deRhamH1_linearEquiv` (Strip 1), but on the smooth-
cycle codomain — which is the codomain where the kernel-equality is
honest. -/
noncomputable def deRhamH1_smooth_linearEquiv
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [JacobianChallenge.Periods.StableChartAt ℂ X] :
    deRhamH1Cocycle X ≃ₗ[ℂ]
      (smoothOneChainCycleSubmodule X →ₗ[ℤ] ℂ) :=
  -- Step 1: deRhamH1Cocycle X = ClosedFormSub 1 X ⧸ ExactForm
  --       ≃ₗ[ℂ] ClosedFormSub 1 X ⧸ ker (deRhamComparisonMap1_smooth X)
  (Submodule.quotEquivOfEq _ _
      (comparison_ker_eq_exact_smooth X).symm) |>.trans
  -- Step 2: ClosedFormSub 1 X ⧸ ker ≃ₗ[ℂ] range
  ((LinearMap.quotKerEquivRange (deRhamComparisonMap1_smooth X)).trans
  -- Step 3: range = ⊤ ⇒ range ≃ₗ[ℂ] codomain
  (LinearEquiv.ofTop _ (comparison_range_eq_top_smooth X)))

/-- **Inc D.2 dim equality.** Through the smooth-cycle LinearEquiv,
the ℂ-dimensions of `deRhamH1Cocycle X` and `smoothOneChainCycleSubmodule X →ₗ[ℤ] ℂ`
agree. Sorry-free given the LinearEquiv above. -/
theorem deRhamH1Cocycle_finrank_eq_finrank_homℤℂ_smoothCycle
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [JacobianChallenge.Periods.StableChartAt ℂ X] :
    Module.finrank ℂ (deRhamH1Cocycle X)
      = Module.finrank ℂ (smoothOneChainCycleSubmodule X →ₗ[ℤ] ℂ) :=
  (deRhamH1_smooth_linearEquiv X).finrank_eq

end JacobianChallenge.HolomorphicForms
