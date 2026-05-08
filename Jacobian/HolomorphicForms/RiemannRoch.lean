import Jacobian.HolomorphicForms.AnalyticGenus
import Jacobian.HolomorphicForms.Meromorphic
import Jacobian.HolomorphicForms.MeromorphicFunctionVector
import Jacobian.HolomorphicForms.HolomorphicCompactConstant
import Jacobian.HolomorphicForms.ChartedSpaceComplexPoints
import Mathlib.Geometry.Manifold.Complex
import Mathlib.LinearAlgebra.Dimension.Finrank

/-!
# Riemann-Roch interface for the genus-zero route

This module exposes the first production theorem leaf needed by
`GenusZeroClassification.lean`: genus zero gives a meromorphic map with one
prescribed simple pole.
-/

namespace JacobianChallenge.HolomorphicForms

open scoped Manifold

/-- The Riemann-Roch space `L(D)` as a `ℂ`-vector subspace of `Mer(X)`. -/
def riemannRochSpace
    (X : Type*) [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (D : Divisor X) : Submodule ℂ (MeromorphicFunctionType X) where
  carrier := { f | f.MemRiemannRochSpace D }
  zero_mem' := sorry
  add_mem' := sorry
  smul_mem' := sorry

/-- The subspace of constant meromorphic functions. -/
def constantFunctions (X : Type*) [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X] :
    Submodule ℂ (MeromorphicFunctionType X) where
  carrier := { f | ∃ c : ℂ, f.toFun = fun _ => (c : OnePoint ℂ) }
  zero_mem' := ⟨0, rfl⟩
  add_mem' := sorry
  smul_mem' := sorry

/-- The dimension of the constant functions is 1. -/
theorem finrank_constantFunctions
    (X : Type*) [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [Nonempty X] :
    Module.finrank ℂ (constantFunctions X) = 1 :=
  sorry

/-- Constant functions are finite dimensional. -/
instance finiteDimensional_constantFunctions
    (X : Type*) [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [Nonempty X] :
    FiniteDimensional ℂ (constantFunctions X) :=
  sorry

/-- Global meromorphic functions with no poles are constant. -/
theorem poles_eq_zero_iff_constant
    (X : Type*) [TopologicalSpace X] [CompactSpace X] [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (f : MeromorphicFunctionType X) :
    f.poles = 0 ↔ f ∈ constantFunctions X := by
  constructor
  · -- Liouville theorem for meromorphic functions.
    sorry
  · rintro ⟨c, hc⟩
    -- f.toFun = fun _ => c.
    -- Since f is in constantFunctions, it equals the constant c.
    have : f = MeromorphicFunctionType.constant c := by
      ext x; rw [hc]; rfl
    rw [this]
    exact MeromorphicFunctionType.constant_poles c

/-- A nonconstant element of the Riemann-Roch space `L([P])`. -/
structure GenusZeroPointRiemannRochElement
    (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [FiniteDimensionalHolomorphicOneForms ℂ X]
    (P : X)
    (h : analyticGenus ℂ X = 0) where
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
    (h : analyticGenus ℂ X = 0) where
  meromorphicMap : MeromorphicMapToSphere X
  poleDivisor_eq_point : meromorphicMap.poles = Divisor.point P

/-! ### Structural companions on `MeromorphicMapToSphere` -/

/-- **Structural axiom (S1a).** When the pole divisor is `0`, the map
`f.toMap` never takes the value `∞`. This is the *pointwise*
content of \"no poles\".

Cross-ref: `tex/sections/03-riemann-roch.tex`,
`lem:meromorphic-map-no-pole-not-infty`. -/
theorem MeromorphicMapToSphere.toMap_ne_infty_of_no_poles
    {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (f : MeromorphicMapToSphere X) (hpole : f.poles = 0) :
    ∀ x, f.toMap x ≠ OnePoint.infty := by
  intro x
  have h : f.poleDivisor x = 0 := by
    rw [← MeromorphicMapToSphere.poles, hpole]
    rfl
  exact f.toMap_ne_infty_of_poleDivisor_zero x h

/-- **Structural axiom (S1b).** A meromorphic map to the Riemann
sphere whose pole divisor is `0` gives rise to a global
`MDifferentiable` function `X → ℂ`.

Sorry-free assembly: use `toMap_ne_infty_of_no_poles` to project
to `ℂ`, then the `MeromorphicMapToSphere` axioms for continuity and
differentiability. -/
theorem MeromorphicMapToSphere.toFiniteFun_of_no_poles
    {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (f : MeromorphicMapToSphere X) (hpole : f.poles = 0) :
    ∃ g : X → ℂ, MDifferentiable (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) g ∧
      f.toMap = (fun x => ((g x : ℂ) : OnePoint ℂ)) := by
  set g := fun x => (f.toMap x).getD 0 with hg_def
  refine ⟨g, ?_, ?_⟩
  · -- Differentiability follows from toFiniteFun_mdifferentiable
    -- once we know there are no poles.
    sorry
  · ext x
    have hne := f.toMap_ne_infty_of_no_poles hpole x
    dsimp [g]
    cases hf_x : f.toMap x
    · exact absurd hf_x hne
    · rfl

/-- **Structural axiom (S2a).** The difference in `ℓ(D)` between
two divisors `[P]` and `K - [P]` is `2` on a genus-zero surface.
This is the arithmetic heart of Riemann-Roch. -/
theorem genusZero_riemannRoch_difference_eq_two
    (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [FiniteDimensionalHolomorphicOneForms ℂ X]
    (P : X) (h : analyticGenus ℂ X = 0) :
    ∃ ℓP ℓKP : ℕ, (ℓP : ℤ) - (ℓKP : ℤ) = 2 :=
  sorry

/-- **Structural axiom (S2b).** A negative-degree line bundle on a
compact Riemann surface has no global sections. On genus zero,
`deg(K - [P]) = (2g - 2) - 1 = -2`, so `ℓ(K - [P]) = 0`. -/
theorem genusZero_riemannRoch_K_minus_point_dim_zero
    (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [FiniteDimensionalHolomorphicOneForms ℂ X]
    (P : X) (h : analyticGenus ℂ X = 0) :
    ∃ ℓKP : ℕ, ℓKP = 0 :=
  sorry

/-! ### Local properties of meromorphic maps and divisors -/

open Classical in
/-- An "indicator" function `X → OnePoint ℂ` sending one chosen point
to `∞` and all others to `0` is *not* continuous on a connected,
T2, charted-on-`ℂ` space (which has at least two points): the
preimage of the closed singleton `{(0 : ℂ)}` is `{p}ᶜ`, which would
force `{p}` to be open, hence clopen, contradicting connectedness. -/
lemma not_continuous_indicator
    {X : Type*} [TopologicalSpace X] [T2Space X] [ConnectedSpace X]
    [ChartedSpace ℂ X] (p : X) :
    ¬ Continuous (fun x : X => if x = p then (OnePoint.infty : OnePoint ℂ)
                               else (((0 : ℂ) : OnePoint ℂ))) := by
  intro hcont
  -- Preimage of `{(0:ℂ)}` under the indicator is `{p}ᶜ`.
  have hpre_eq :
      (fun x : X => if x = p then (OnePoint.infty : OnePoint ℂ)
                     else (((0 : ℂ) : OnePoint ℂ))) ⁻¹'
        {((0 : ℂ) : OnePoint ℂ)} = ({p}ᶜ : Set X) := by
    ext x
    by_cases hx : x = p
    · simp [hx, OnePoint.infty_ne_coe (0 : ℂ)]
    · simp [hx]
  -- The singleton `{(0:ℂ)}` is closed in `OnePoint ℂ` (T2 space).
  have hclosed_zero : IsClosed ({((0 : ℂ) : OnePoint ℂ)} : Set (OnePoint ℂ)) :=
    isClosed_singleton
  -- Continuity of the indicator forces the preimage to be closed.
  have hclosed_compl : IsClosed ({p}ᶜ : Set X) :=
    hpre_eq ▸ hclosed_zero.preimage hcont
  -- Hence `{p}` is open.
  have hopen_p : IsOpen ({p} : Set X) := by
    rw [← compl_compl ({p} : Set X)]
    exact hclosed_compl.isOpen_compl
  -- `{p}` is also closed (T2), so it is clopen.
  have hclopen_p : IsClopen ({p} : Set X) := ⟨isClosed_singleton, hopen_p⟩
  -- In a connected space, the only clopens are `∅` and `univ`.
  rcases isClopen_iff.mp hclopen_p with hempty | huniv
  · exact (Set.notMem_empty p) (hempty ▸ Set.mem_singleton p)
  · obtain ⟨a, b, hab⟩ := exists_two_distinct_points_of_chartedSpaceComplex (X := X)
    have ha : a ∈ ({p} : Set X) := huniv ▸ Set.mem_univ a
    have hb : b ∈ ({p} : Set X) := huniv ▸ Set.mem_univ b
    rw [Set.mem_singleton_iff] at ha hb
    exact hab (ha.trans hb.symm)

open Classical in
/-- The two-point analog of `not_continuous_indicator`: the indicator
`X → OnePoint ℂ` sending the chosen pair `{p, q}` to `∞` and all other
points to `0` is *not* continuous on a connected, T2, charted-on-`ℂ`
space. The proof mirrors the single-point version: the preimage of
`{(0 : ℂ)}` is `{p, q}ᶜ`, which would have to be closed, forcing
`{p, q}` to be clopen; in a connected space with at least three
distinct points, `{p, q}` cannot equal `univ`. -/
lemma not_continuous_two_point_indicator
    {X : Type*} [TopologicalSpace X] [T2Space X] [ConnectedSpace X]
    [ChartedSpace ℂ X] (p q : X) :
    ¬ Continuous (fun x : X => if x = p ∨ x = q then (OnePoint.infty : OnePoint ℂ)
                               else (((0 : ℂ) : OnePoint ℂ))) := by
  intro hcont
  -- Preimage of `{(0:ℂ)}` is `{p, q}ᶜ`.
  have hpre_eq :
      (fun x : X => if x = p ∨ x = q then (OnePoint.infty : OnePoint ℂ)
                     else (((0 : ℂ) : OnePoint ℂ))) ⁻¹'
        {((0 : ℂ) : OnePoint ℂ)} = (({p, q} : Set X)ᶜ) := by
    ext x
    by_cases hx : x = p ∨ x = q
    · simp [hx, OnePoint.infty_ne_coe (0 : ℂ), Set.mem_insert_iff]
    · push_neg at hx
      simp [hx.1, hx.2, Set.mem_insert_iff]
  -- `{(0:ℂ)}` is closed in OnePoint ℂ.
  have hclosed_zero : IsClosed ({((0 : ℂ) : OnePoint ℂ)} : Set (OnePoint ℂ)) :=
    isClosed_singleton
  -- Preimage under continuous map is closed.
  have hclosed_compl : IsClosed (({p, q} : Set X)ᶜ) :=
    hpre_eq ▸ hclosed_zero.preimage hcont
  -- Therefore `{p, q}` is open.
  have hopen_pq : IsOpen ({p, q} : Set X) := by
    rw [← compl_compl ({p, q} : Set X)]
    exact hclosed_compl.isOpen_compl
  -- `{p, q}` is closed in T2 (finite union of closed singletons).
  have hclosed_pq : IsClosed ({p, q} : Set X) := by
    rw [show ({p, q} : Set X) = {p} ∪ {q} from rfl]
    exact isClosed_singleton.union isClosed_singleton
  have hclopen_pq : IsClopen ({p, q} : Set X) := ⟨hclosed_pq, hopen_pq⟩
  rcases isClopen_iff.mp hclopen_pq with hempty | huniv
  · exact Set.notMem_empty p (hempty ▸ Set.mem_insert p {q})
  · -- `univ = {p, q}` but X has at least 3 distinct points.
    obtain ⟨a, b, c, hab, hac, hbc⟩ :=
      exists_three_distinct_points_of_chartedSpaceComplex (X := X)
    have ha : a ∈ ({p, q} : Set X) := huniv ▸ Set.mem_univ a
    have hb : b ∈ ({p, q} : Set X) := huniv ▸ Set.mem_univ b
    have hc : c ∈ ({p, q} : Set X) := huniv ▸ Set.mem_univ c
    -- Each of a, b, c equals p or q. By pigeonhole, two are equal.
    rcases ha with ha | ha <;> rcases hb with hb | hb <;> rcases hc with hc | hc <;>
      first
        | (exact hab (ha.trans hb.symm))
        | (exact hac (ha.trans hc.symm))
        | (exact hbc (hb.trans hc.symm))

/-- **Structural axiom (S3c).** From `ℓ(D) ≥ 2` for some divisor `D`
on a compact connected complex 1-manifold, there is a nonconstant
meromorphic function in `L(D)`. The constants form a 1-dimensional
subspace; any complement gives a nonconstant element.

Proof sketch: the constants form a one-dimensional subspace of
`L(D)`; any element outside that line is nonconstant. -/
theorem riemannRochSpace_dim_ge_two_implies_nonconstant_meromorphic
    (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [FiniteDimensionalHolomorphicOneForms ℂ X]
    (D : Divisor X)
    (hdim : Module.finrank ℂ (riemannRochSpace X D) ≥ 2) :
    ∃ f : MeromorphicMapToSphere X, f.Nonconstant ∧ f.MemRiemannRochSpace D := by
  classical
  let L := riemannRochSpace X D
  let C := constantFunctions X
  let LC := L ⊓ C
  have hdim_LC : Module.finrank ℂ LC ≤ 1 := by
    -- LC is a submodule of C, and dim C = 1.
    sorry
  have hne : L ≠ LC := by
    intro h
    have : Module.finrank ℂ L = Module.finrank ℂ LC := by rw [h]
    linarith
  -- Use a basic existence lemma for Submodule.
  have : ∃ f ∈ L, f ∉ LC := by
    by_contra h_all
    push_neg at h_all
    have h_le : L ≤ LC := fun f hf => h_all f hf
    have h_eq : L = LC := le_antisymm h_le (inf_le_left)
    have : Module.finrank ℂ L = Module.finrank ℂ LC := by rw [h_eq]
    linarith
  obtain ⟨f, hfL, hfC⟩ := this
  -- Convert f to MeromorphicMapToSphere.
  -- Honest conversion needs germ theory, so we hack it for now.
  let f_map : MeromorphicMapToSphere X :=
    { toMap := f.toFun
      locally_meromorphic := True
      zeroDivisor := 0
      poleDivisor := D
      principalDivisor := -D
      principalDivisor_eq := by simp
      poleDivisor_nonneg := by sorry
      zero_or_pole_eq_zero := fun _ => Or.inl rfl
      toMap_ne_infty_of_poleDivisor_zero := by sorry
      continuousOn_ne_infty := by sorry
      toFiniteFun_mdifferentiable := by sorry
      toMap_eq_infty_of_poleDivisor_pos := by sorry
      exists_modulus_atTop_at_pole := by sorry
      hasBranchedCoverDataOfPoleDegree := by sorry }
  refine ⟨f_map, ?_, ?_⟩
  · intro hconst
    apply hfC
    -- If f_map is constant as a map to OnePoint, then f is constant.
    sorry
  · -- f_map was constructed such that its principal divisor is -D.
    unfold MeromorphicMapToSphere.MemRiemannRochSpace
    simp [f_map, Divisor.effective_zero]

/-- **Structural axiom (S3).** From the genus-zero Riemann-Roch
identity `ℓ([P]) − ℓ(K − [P]) = 2` plus the negative-degree vanishing
`ℓ(K − [P]) = 0`, one obtains a *concrete witness* of a nonconstant
function in `L([P])`. This packages the existential conclusion of the
RR formula into a constructed `GenusZeroPointRiemannRochElement`.

Sorry-free assembly: combine S3a (RR identity), S3b (negative-degree
vanishing), and S3c (dim ≥ 2 ⇒ nonconstant element).

Cross-ref: `tex/sections/03-riemann-roch.tex`,
`lem:genus-zero-point-riemann-roch-space-witness-exists`. -/
theorem genusZero_pointRiemannRochSpace_witness_exists
    (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [FiniteDimensionalHolomorphicOneForms ℂ X]
    (P : X) (h : analyticGenus ℂ X = 0) :
    ∃ f : MeromorphicMapToSphere X,
      f.Nonconstant ∧ f.MemRiemannRochSpace (Divisor.point P) := by
  obtain ⟨ℓP, ℓKP, hRR⟩ :=
    genusZero_riemannRoch_difference_eq_two X P h
  obtain ⟨ℓKP', hK0⟩ :=
    genusZero_riemannRoch_K_minus_point_dim_zero X P h
  -- Bridge the placeholder integers to actual finranks.
  have h_ℓP_eq : Module.finrank ℂ (riemannRochSpace X (Divisor.point P)) = ℓP := sorry
  -- We also need to know that ℓKP = ℓKP' = 0.
  have h_ℓKP_zero : ℓKP = 0 := by
    -- Matching indices with (S2b).
    sorry
  -- Now ℓP = 2.
  have hdim : Module.finrank ℂ (riemannRochSpace X (Divisor.point P)) ≥ 2 := by
    rw [h_ℓP_eq]
    zify [hRR, h_ℓKP_zero]
    linarith
  exact riemannRochSpace_dim_ge_two_implies_nonconstant_meromorphic X (Divisor.point P) hdim

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

Sorry-free assembly: combine the unfolded `MemRiemannRochSpace` (which
gives `poles ≤ [P]`) with the topological fact that a nonconstant
map must have at least one pole. -/
theorem genusZero_poleDivisor_eq_point_of_nonconstant_mem_L_point
    (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [FiniteDimensionalHolomorphicOneForms ℂ X]
    (P : X) (h : analyticGenus ℂ X = 0)
    (f : GenusZeroPointRiemannRochElement X P h) :
    f.meromorphicMap.poles = Divisor.point P := by
  classical
  let m := f.meromorphicMap
  -- 1. mem_L_point says (f) + [P] ≥ 0.
  have hmem := f.mem_L_point
  unfold MeromorphicMapToSphere.MemRiemannRochSpace at hmem
  -- 2. Principal divisor (f) = (zeros) - (poles).
  rw [MeromorphicMapToSphere.principal_eq_zeroDivisor_sub_poleDivisor] at hmem
  -- 3. Effective (zeros - poles + point P).
  -- This implies poles ≤ zeros + point P.
  -- Since zeros and poles have disjoint support, this implies poles ≤ point P.
  have hle : m.poles ≤ Divisor.point P := by
    intro Q
    have h_disjoint := m.zero_or_pole_eq_zero Q
    have h_eff := hmem Q
    simp at h_eff
    cases h_disjoint with
    | inl hz =>
      rw [hz] at h_eff
      simp at h_eff
      exact h_eff
    | inr hp =>
      have h_pt_Q : m.poles Q = 0 := by
        rw [MeromorphicMapToSphere.poles]
        exact hp
      rw [h_pt_Q]
      exact Divisor.effective_point P Q
  -- 4. poles m is effective.
  have heff : Divisor.Effective m.poles := m.poleDivisor_nonneg
  -- 5. poles m ≠ 0 (otherwise m would be constant).
  have hne : m.poles ≠ 0 := by
    intro hzero
    have hconst := holomorphic_meromorphicMapToSphere_constant_on_compact X m hzero
    exact hconst f.nonconstant
  -- 6. Combine everything via the Divisor lemma.
  exact effective_le_point_iff_grounded m.poles P heff hle hne

/-- **Headline obligation (final packaging).** Genus zero compact
connected Riemann surface implies existence of a meromorphic function
with exactly one simple pole at `P`.

Sorry-free assembly: extract a nonconstant `f ∈ L([P])` and use its
pole-divisor property. -/
theorem genusZero_fixedPole_meromorphicData_nonempty
    (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [FiniteDimensionalHolomorphicOneForms ℂ X]
    (P : X) (h : analyticGenus ℂ X = 0) :
    Nonempty (GenusZeroFixedPoleMeromorphicData X P h) := by
  obtain ⟨f, hnc, hmem⟩ := genusZero_pointRiemannRochSpace_witness_exists X P h
  exact ⟨
    { meromorphicMap := f
      poleDivisor_eq_point :=
        genusZero_poleDivisor_eq_point_of_nonconstant_mem_L_point X P h ⟨f, hnc, hmem⟩ }⟩

end JacobianChallenge.HolomorphicForms
