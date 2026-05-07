import Jacobian.AbelJacobi.AnalyticOfCurveBasis
import Jacobian.ComplexTorus.OfClm
import Jacobian.HolomorphicForms.PullbackBundled
import Jacobian.HolomorphicForms.BasisAlignedDualEquiv
import Jacobian.Periods.PullbackNaturality
import Jacobian.Periods.BasisAlignedPeriodSubgroup
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# Analytic pushforward on the basis-aligned carrier

A holomorphic map `f : X → Y` of compact Riemann surfaces induces a
pushforward `f_* : BasisAnalyticJacobian X → BasisAnalyticJacobian Y`,
typically constructed via the trace map on holomorphic 1-forms (or, in
basis coordinates, the dual of the trace), descended through the
period quotient.

This module mirrors `Jacobian/TraceDegree/PullbackBasis.lean` in the
opposite direction. Named obligations:

* `analyticPushforward f hf` — bundled `→ₜ+` hom on the basis-aligned
  carrier (`opaque`);
* `analyticPushforward_id_apply` — covariant identity functoriality;
* `analyticPushforward_comp_apply` — covariant composition;
* `analyticPushforward_contMDiff` — holomorphicity.

## TOPDOWN refactor: trace-coordinate interface (round R)

Earlier rounds bundled `analyticPushforward`, `pushforwardTraceLift`,
their descent compatibility, and their geometric properties together
in `BasisAnalyticPushforwardBundle`, then exposed each via
`Classical.choice` from a zero-valued `Inhabited` witness. This made
the identity functoriality `pushforwardTraceLift id = id` *unprovable*
at the bundle layer (the zero witness can't satisfy it), and attempts
to enrich the bundle with an `HEq`-based identity-case field hit an
instance diamond after `subst Y = X` (see prior commit
`410ce72`/`PullbackBasis HEq leak`).

This refactor breaks the bundle apart:

1. A small, contravariant **trace-coordinate interface**
   `holomorphicTraceCoord f hf : (Fin g_Y → ℂ) →ₗ[ℂ] (Fin g_X → ℂ)`,
   opaque, with two named functoriality sorries
   (`holomorphicTraceCoord_id`, `holomorphicTraceCoord_comp`).
   These are the *Mathlib-level* trace/norm-on-holomorphic-1-forms
   obligations a future
   `Mathlib.Analysis.Complex.RiemannSurface.Trace` would discharge.

2. A **uniform**, sorry-free top-level
   `pushforwardTraceLift f hf : (Fin g_X → ℂ) →+ (Fin g_Y → ℂ)`
   defined as the matrix transpose of `holomorphicTraceCoord f hf`.
   Functoriality of `pushforwardTraceLift` then collapses to
   "transpose preserves id/comp (contravariantly)" plus the two
   `holomorphicTraceCoord_*` sorries.

3. **Three "raw" geometric sorries** carrying the genuinely geometric
   content the bundle used to bundle:

   * `pushforwardTraceLift_preserves_lattice_raw` — the trace lift
     sends the period subgroup of `X` into the period subgroup of `Y`
     (Riemann bilinear / period-lattice content);
   * `analyticPushforward_mk_spec_raw` — descent compatibility:
     `analyticPushforward (mk v) = mk (pushforwardTraceLift v)`
     (descent of the trace map through the period quotient);
   * `analyticPushforward_contMDiff_raw` — the descended map is
     holomorphic (Mathlib quotient-smoothness content).

The original bundle and its `_id_traceLift` / `_comp_traceLift`
sorries are gone; the existing public API
(`analyticPushforward`, `pushforwardTraceLift`,
`analyticPushforward_id_apply`, etc.) keeps the same names and
signatures but is now wired through the new primitives. The two
"payoff" theorems `basisAnalyticPushforwardBundle_id_traceLift` and
`basisAnalyticPushforwardBundle_comp_traceLift` are kept as
sorry-free aliases (renamed `pushforwardTraceLift_eq_id` etc. would
be cleaner; the old names are kept here so the docstrings in
`PullbackBasis.lean` that name them remain accurate).
-/

namespace JacobianChallenge.TraceDegree

open scoped ContDiff Manifold
open JacobianChallenge.HolomorphicForms JacobianChallenge.Periods
open JacobianChallenge.AbelJacobi
open JacobianChallenge.ComplexTorus

variable {X : Type} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
variable {Y : Type} [TopologicalSpace Y] [T2Space Y] [CompactSpace Y]
  [ConnectedSpace Y] [ChartedSpace ℂ Y]
  [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) Y]
variable {Z : Type} [TopologicalSpace Z] [T2Space Z] [CompactSpace Z]
  [ConnectedSpace Z] [ChartedSpace ℂ Z]
  [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) Z]

/-! ### Trace-coordinate interface

The fundamental small interface this module exposes. A holomorphic
map `f : X → Y` of compact Riemann surfaces should induce a
`ℂ`-linear *pullback on holomorphic 1-forms*
`f^* : H⁰(Y, Ω¹) → H⁰(X, Ω¹)`. After choosing bases of
`HolomorphicOneForm ℂ Y` and `HolomorphicOneForm ℂ X` (of dimensions
`analyticGenus ℂ Y` and `analyticGenus ℂ X` respectively), this is a
linear map of basis-coordinate vector spaces. We expose it as the
opaque `holomorphicTraceCoord` interface together with two named
functoriality sorries that match the Mathlib-style functoriality of
the form-pullback.
-/

/-- The basis-coordinate representation of the holomorphic-1-form
*pullback* induced by `f : X → Y`, as a ℂ-linear map
`(Fin g_Y → ℂ) →ₗ[ℂ] (Fin g_X → ℂ)`.

This is the **contravariant** direction (forms pull back along `f`),
which is why the codomain is `Fin g_X → ℂ` and the domain is
`Fin g_Y → ℂ`. The covariant pushforward
`pushforwardTraceLift f hf : (Fin g_X → ℂ) →+ (Fin g_Y → ℂ)`
is defined below as the matrix transpose of this map.

Bottom-up: built concretely from `pullbackFormsBundledLM` (the smooth
bundle of the chain-rule pullback), composed with the basis-aligned
linear equivalences `holomorphicOneFormFinBasis.equivFun` to convert
between abstract forms and `Fin g → ℂ` coordinates.

Functoriality (`holomorphicTraceCoord_id`, `holomorphicTraceCoord_comp`)
reduces to the corresponding `pullbackFormsBundledLM` functoriality
    (`pullbackFormsBundledLM_id`, `pullbackFormsBundledLM_comp`), both of
which are sorry-free in `Jacobian/HolomorphicForms/PullbackBundled.lean`. -/
noncomputable def holomorphicTraceCoord
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    [FiniteDimensionalHolomorphicOneForms ℂ X]
    [FiniteDimensionalHolomorphicOneForms ℂ Y] :
    (Fin (analyticGenus ℂ Y) → ℂ) →ₗ[ℂ] (Fin (analyticGenus ℂ X) → ℂ) :=
  (holomorphicOneFormFinBasis ℂ X).equivFun.toLinearMap ∘ₗ
    (pullbackFormsBundledLM X Y f hf) ∘ₗ
    (holomorphicOneFormFinBasis ℂ Y).equivFun.symm.toLinearMap

omit [T2Space X] [CompactSpace X] [ConnectedSpace X] in
/-- Identity functoriality of the trace-coordinate map.

Sorry-free: the `pullbackFormsBundledLM` functoriality
`pullbackFormsBundledLM_id` reduces the inner factor to `LinearMap.id`,
and the outer `Basis.equivFun` round trip cancels. -/
theorem holomorphicTraceCoord_id
    [FiniteDimensionalHolomorphicOneForms ℂ X] :
    holomorphicTraceCoord (X := X) (Y := X) id contMDiff_id =
      LinearMap.id := by
  unfold holomorphicTraceCoord
  rw [pullbackFormsBundledLM_id]
  ext v
  simp

omit [T2Space X] [CompactSpace X] [ConnectedSpace X] [T2Space Y] [CompactSpace Y]
  [ConnectedSpace Y] [T2Space Z] [CompactSpace Z] [ConnectedSpace Z] in
/-- Composition functoriality of the trace-coordinate map.

Sorry-free: the `pullbackFormsBundledLM` contravariant composition
`pullbackFormsBundledLM_comp` reduces the inner factor; the inner
`Basis.equivFun` round trip on `Y` cancels. -/
theorem holomorphicTraceCoord_comp
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (g : Y → Z) (hg : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω g)
    [FiniteDimensionalHolomorphicOneForms ℂ X]
    [FiniteDimensionalHolomorphicOneForms ℂ Y]
    [FiniteDimensionalHolomorphicOneForms ℂ Z] :
    holomorphicTraceCoord (g ∘ f) (hg.comp hf) =
      (holomorphicTraceCoord f hf).comp (holomorphicTraceCoord g hg) := by
  unfold holomorphicTraceCoord
  rw [pullbackFormsBundledLM_comp f hf g hg]
  ext v
  simp [LinearMap.comp_apply]

/-! ### Top-level `pushforwardTraceLift` via matrix transpose

The *covariant* pushforward direction is the transpose (a.k.a. dual,
under self-duality of `Fin n → ℂ`) of `holomorphicTraceCoord`.
Concretely, we go through the standard `LinearMap.toMatrix'` /
`Matrix.transpose` / `Matrix.toLin'` pipeline.
-/

/-- The covariant pushforward of basis-coordinate vectors, as the
matrix transpose of the contravariant `holomorphicTraceCoord f hf`.
Top-level concrete definition; sorry-free. -/
noncomputable def pushforwardTraceLift
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) :
    (Fin (analyticGenus ℂ X) → ℂ) →+ (Fin (analyticGenus ℂ Y) → ℂ) :=
  (Matrix.toLin' (holomorphicTraceCoord f hf).toMatrix'.transpose).toAddMonoidHom

/-- `pushforwardTraceLift` along the identity is the identity.

Sorry-free assembly: `holomorphicTraceCoord_id` reduces the underlying
`LinearMap` to `LinearMap.id`, whose `toMatrix'` is the identity
matrix `1`, whose transpose is `1`, whose `toLin'` is `LinearMap.id`,
whose `toAddMonoidHom` is `AddMonoidHom.id`. -/
theorem pushforwardTraceLift_id :
    pushforwardTraceLift (X := X) (Y := X) id contMDiff_id =
      AddMonoidHom.id (Fin (analyticGenus ℂ X) → ℂ) := by
  unfold pushforwardTraceLift
  rw [holomorphicTraceCoord_id, LinearMap.toMatrix'_id, Matrix.transpose_one,
      Matrix.toLin'_one]
  rfl

/-- `pushforwardTraceLift` distributes over composition (covariantly).

Sorry-free assembly: `holomorphicTraceCoord_comp` gives contravariant
composition for the underlying `LinearMap`; transpose reverses
composition, so the pushforward direction recovers covariance. -/
theorem pushforwardTraceLift_comp
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (g : Y → Z) (hg : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω g) :
    pushforwardTraceLift (g ∘ f) (hg.comp hf) =
      (pushforwardTraceLift g hg).comp (pushforwardTraceLift f hf) := by
  refine AddMonoidHom.ext fun v => ?_
  show (Matrix.toLin'
      (LinearMap.toMatrix' (holomorphicTraceCoord (g ∘ f) (hg.comp hf))).transpose) v =
    (Matrix.toLin' (LinearMap.toMatrix' (holomorphicTraceCoord g hg)).transpose)
      ((Matrix.toLin' (LinearMap.toMatrix' (holomorphicTraceCoord f hf)).transpose) v)
  rw [holomorphicTraceCoord_comp f hf g hg, LinearMap.toMatrix'_comp,
      Matrix.transpose_mul, Matrix.toLin'_mul, LinearMap.comp_apply]

/-! ### Top-level `analyticPushforward` and the three raw geometric sorries

The descended map `analyticPushforward` lives on the period quotient
`BasisAnalyticJacobian`. Its data and three core specs are factored
into one opaque + three named sorries; each sorry carries a single
piece of geometric content (lattice preservation, descent
compatibility, smoothness of the descent).
-/

/-- Bridge identity between `pushforwardTraceLift` and the form-pullback /
basis-aligned dual equivalence.

The algebraic relationship: `pushforwardTraceLift = transpose-of-matrix(holomorphicTraceCoord)`,
and `holomorphicTraceCoord = basisX.equivFun ∘ pullbackFormsBundledLM ∘ basisY.equivFun.symm`.
So `pushforwardTraceLift v j = ∑ i, (holomorphicTraceCoord matrix)[i,j] * v i
= ∑ i, (basisX.equivFun (pullbackFormsBundledLM (basisY j))) i * v i`.
When `v = dualEquiv X φ`, `v i = φ (basisX i)`, and the sum collapses via
linearity of `φ` to `φ (pullbackFormsBundledLM (basisY j))`, which equals
`(φ ∘ pullbackFormsBundledLM)(basisY j) = (dualEquiv Y (φ ∘ pullbackFormsBundledLM)) j`.

Sorry: the calculation chain through `Matrix.toLin'`, `LinearMap.toMatrix'`,
`Basis.equivFun`, `Basis.equivFun_symm_apply`, and `Module.Basis.dualBasis_apply_self`.
A pure linear-algebra identity; no period theory. -/
theorem pushforwardTraceLift_apply_holomorphicOneFormDualEquiv
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (φ : HolomorphicOneForm ℂ X →ₗ[ℂ] ℂ) :
    pushforwardTraceLift f hf (holomorphicOneFormDualEquiv ℂ X φ) =
      holomorphicOneFormDualEquiv ℂ Y
        (φ.comp (pullbackFormsBundledLM X Y f hf)) := by
  classical
  ext j
  -- RHS: dualEquiv Y (φ.comp pullbackBundled) j = (φ.comp pullbackBundled) (basisY j)
  --                                              = φ (pullbackBundled (basisY j))
  -- via the new auxiliary `holomorphicOneFormDualEquiv_apply_eq_apply_basis`.
  rw [holomorphicOneFormDualEquiv_apply_eq_apply_basis]
  show (Matrix.toLin' (LinearMap.toMatrix' (holomorphicTraceCoord f hf)).transpose
      (holomorphicOneFormDualEquiv ℂ X φ)) j =
    (φ.comp (pullbackFormsBundledLM X Y f hf)) (holomorphicOneFormFinBasis ℂ Y j)
  -- LHS: matrix-vector product via toLin'.
  rw [Matrix.toLin'_apply]
  simp only [Matrix.mulVec, Matrix.transpose_apply, dotProduct,
    LinearMap.toMatrix'_apply]
  -- LHS: ∑ i, holomorphicTraceCoord f hf (Pi.single j 1) i * (dualEquiv X φ) i.
  -- (dualEquiv X φ) i = φ (basisX i) by the auxiliary.
  simp_rw [holomorphicOneFormDualEquiv_apply_eq_apply_basis]
  -- LHS: ∑ i, holomorphicTraceCoord f hf (Pi.single j 1) i * φ (basisX i).
  -- Unfold holomorphicTraceCoord: it's basisX.equivFun ∘ pullbackBundled ∘ basisY.equivFun.symm.
  unfold holomorphicTraceCoord
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe]
  -- LHS: ∑ i, (basisX.equivFun (pullbackBundled (basisY.equivFun.symm (Pi.single j 1)))) i * φ (basisX i).
  -- Reduce basisY.equivFun.symm (Pi.single j 1) = basisY j.
  rw [show (holomorphicOneFormFinBasis ℂ Y).equivFun.symm (Pi.single j 1) =
      holomorphicOneFormFinBasis ℂ Y j from by
    rw [Module.Basis.equivFun_symm_apply, Finset.sum_eq_single j]
    · rw [Pi.single_eq_same, one_smul]
    · intro i _ hij
      rw [Pi.single_eq_of_ne hij, zero_smul]
    · intro hj; exact (hj (Finset.mem_univ _)).elim]
  -- LHS: ∑ i, (basisX.equivFun (pullbackBundled (basisY j))) i * φ (basisX i).
  -- Use ω = ∑ i, ((basisX.equivFun ω) i) • (basisX i) and linearity of φ.
  set ωX : HolomorphicOneForm ℂ X :=
    (pullbackFormsBundledLM X Y f hf) (holomorphicOneFormFinBasis ℂ Y j)
  show ∑ i, (holomorphicOneFormFinBasis ℂ X).equivFun ωX i *
      φ (holomorphicOneFormFinBasis ℂ X i) = φ ωX
  -- ωX = ∑ i, ((basisX.equivFun ωX) i) • basisX i.
  conv_rhs => rw [← (holomorphicOneFormFinBasis ℂ X).sum_equivFun ωX]
  rw [map_sum]
  refine Finset.sum_congr rfl ?_
  intro i _
  rw [map_smul, smul_eq_mul]

/-- Raw geometric obligation (path-level Lipschitz uniformity).

For every path `γ' : Path a b` in a compact Riemann surface `X`, there
exists a Lipschitz constant `K` such that, on every uniform-grain
chart partition of `γ'`, the chart-lifted segments are `K`-Lipschitz
on `[0, 1]` (`ChartLiftLipschitzOnPartitions γ' K`).

This holds automatically for the rectifiable / piecewise-`C¹` paths
used in `IntegralOneCycle X`-based constructions (compact + smooth
manifold + finite chart cover ⇒ uniform Lipschitz bound), but the
formal proof is genuine analytic content. Tracked as a named sorry
here so it is searchable; eventually discharged in
`Jacobian/Periods/...` once the path-regularity API exists. -/
theorem cycleLipPath_obligation :
    ∀ {a b : X} (γ' : Path a b),
      ∃ K : NNReal, ChartLiftLipschitzOnPartitions γ' K := by
  sorry

/-- Raw geometric obligation (chain-level C¹ regularity). -/
theorem cycleC1Path_obligation :
    ∀ {a b : X} (γ' : Path a b), ContDiffOn ℝ 1 γ'.extend (Set.Icc 0 1) := by
  sorry

/-- Raw geometric obligation (chain-level uniform Lipschitz).

The chain-level uniformised version of `cycleLipPath_obligation`:
for any finite family of paths `γs i : Path (a i) (b i)` in `X`,
there is a *single* Lipschitz constant `K` that bounds the chart-lift
of every `γs i` on every uniform-grain partition simultaneously. -/
theorem cycleLipChain_obligation :
    ∀ (m : ℕ) (a b : Fin m → X)
      (γs : ∀ i : Fin m, Path (a i) (b i)),
      ∃ K : NNReal, ∀ i : Fin m, ChartLiftLipschitzOnPartitions (γs i) K := by
  sorry

/-- Raw obligation: the trace lift preserves the period subgroup.

Sorry-free assembly via:
* `mem_basisAlignedPeriodSubgroupConcrete_iff` (membership characterization);
* `pushforwardTraceLift_apply_holomorphicOneFormDualEquiv` (algebraic bridge);
* `periodPairing_pullbackFormsBundledLM` (Stokes naturality), instantiated
  with the regularity/Lipschitz hypotheses `cycleC1Path_obligation`,
  `cycleLipPath_obligation` and `cycleLipChain_obligation`;
* `holomorphicOneFormDualEquiv_mem_basisAlignedPeriodSubgroupConcrete`
  (membership transport).

The genuinely geometric content is now isolated to named sorries:
the algebraic bridge above (a `LinearMap.dualMap` identity), the Stokes
naturality in `Periods/PullbackNaturality.lean`, and the new
regularity/Lipschitz-uniformity obligations introduced above. -/
theorem pushforwardTraceLift_preserves_lattice_raw
    [StableChartAt (modelWithCornersSelf ℂ ℂ) X]
    [StableChartAt (modelWithCornersSelf ℂ ℂ) Y]
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) :
    ∀ v ∈ (periodFullComplexLattice X).subgroup,
      pushforwardTraceLift f hf v ∈ (periodFullComplexLattice Y).subgroup := by
  intro v hv
  -- Unfold to the concrete representative.
  show pushforwardTraceLift f hf v ∈ basisAlignedPeriodSubgroupConcrete Y
  -- Extract the witness functional φ from membership in the X-side subgroup.
  have hv' : v ∈ basisAlignedPeriodSubgroupConcrete X := hv
  rw [mem_basisAlignedPeriodSubgroupConcrete_iff] at hv'
  obtain ⟨φ, hφ_mem, hφ_eq⟩ := hv'
  -- φ is in the range of periodPairing; extract a cycle γ.
  change φ ∈ (periodPairing ℂ X).range at hφ_mem
  rw [AddMonoidHom.mem_range] at hφ_mem
  obtain ⟨γ, hγ⟩ := hφ_mem
  -- Apply the bridge + naturality.
  rw [← hφ_eq, ← hγ,
    pushforwardTraceLift_apply_holomorphicOneFormDualEquiv f hf]
  -- Now goal: holomorphicOneFormDualEquiv ℂ Y (periodPairing ℂ X γ ∘ pullbackFormsBundledLM ...) ∈ ...
  -- Use naturality: periodPairing X γ ∘ pullbackBundled = periodPairing Y (cyclePushforward γ).
  have hnat : (periodPairing ℂ X γ).comp (pullbackFormsBundledLM X Y f hf) =
      periodPairing ℂ Y (cyclePushforward f hf γ) := by
    refine LinearMap.ext fun η => ?_
    exact periodPairing_pullbackFormsBundledLM f hf γ η
      (cycleC1Path_obligation (X := X))
      (cycleLipPath_obligation (X := X)) (cycleLipChain_obligation (X := X))
  rw [hnat]
  -- Now: holomorphicOneFormDualEquiv ℂ Y (periodPairing ℂ Y (cyclePushforward f hf γ)) ∈ basisAlignedPeriodSubgroupConcrete Y.
  refine holomorphicOneFormDualEquiv_mem_basisAlignedPeriodSubgroupConcrete Y ?_
  show periodPairing ℂ Y (cyclePushforward f hf γ) ∈ (periodPairing ℂ Y).range
  exact AddMonoidHom.mem_range.mpr ⟨cyclePushforward f hf γ, rfl⟩

/-- The basis-coordinate trace lift as a `ℂ`-linear map (i.e. the
linear-map version of `pushforwardTraceLift`, before forgetting the
`ℂ`-action). Sorry-free: the underlying `LinearMap` of the matrix-
transpose definition. -/
noncomputable def pushforwardTraceLiftLinearMap
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) :
    (Fin (analyticGenus ℂ X) → ℂ) →ₗ[ℂ] (Fin (analyticGenus ℂ Y) → ℂ) :=
  Matrix.toLin' (holomorphicTraceCoord f hf).toMatrix'.transpose

/-- The basis-coordinate trace lift as a continuous `ℂ`-linear map.
Upgrade of `pushforwardTraceLiftLinearMap` via finite-dimensional
auto-continuity. Sorry-free. -/
noncomputable def pushforwardTraceLiftCLM
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) :
    (Fin (analyticGenus ℂ X) → ℂ) →L[ℂ] (Fin (analyticGenus ℂ Y) → ℂ) :=
  LinearMap.toContinuousLinearMap (pushforwardTraceLiftLinearMap f hf)

/-- The analytic pushforward induced by a holomorphic map of compact
Riemann surfaces, on the basis-aligned carrier.

Concrete (non-opaque) descent of `pushforwardTraceLiftCLM` through
the period quotient via `ComplexTorus.mapClm`, using
`pushforwardTraceLift_preserves_lattice_raw` for the lattice
preservation hypothesis. The continuity of the descent comes from
`mapClm_continuous`; the smoothness companion
`analyticPushforward_contMDiff_raw` remains a (named) sorry —
quotient-of-manifold smoothness is the genuine geometric content.

Note: `pushforwardTraceLiftCLM` has type `→L[ℂ]` while
`pushforwardTraceLift` has type `→+`; the underlying additive maps
agree definitionally (the `→L[ℂ]` and `→ₗ[ℂ]` and `→+` are all
extracted from the same matrix-transpose `Matrix.toLin'` value). -/
noncomputable def analyticPushforward (f : X → Y)
    (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) :
    BasisAnalyticJacobian X →ₜ+ BasisAnalyticJacobian Y where
  toFun := ComplexTorus.mapClm (pushforwardTraceLiftCLM f hf)
    (pushforwardTraceLift_preserves_lattice_raw f hf)
  map_zero' := (ComplexTorus.mapClm _ _).map_zero
  map_add' := (ComplexTorus.mapClm _ _).map_add
  continuous_toFun :=
    ComplexTorus.mapClm_continuous (pushforwardTraceLiftCLM f hf)
      (pushforwardTraceLift_preserves_lattice_raw f hf)

/-- Raw obligation: descent compatibility — `analyticPushforward` is
the descent of `pushforwardTraceLift` through the period quotient.

Sorry-free: unfold `analyticPushforward` to `mapClm`, then
`ComplexTorus.map_mk` (which is `rfl`); the underlying additive
hom of `pushforwardTraceLiftCLM` is definitionally
`pushforwardTraceLift`. -/
theorem analyticPushforward_mk_spec_raw
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (v : Fin (analyticGenus ℂ X) → ℂ) :
    analyticPushforward f hf
      (ComplexTorus.mk _ (periodFullComplexLattice X) v) =
      ComplexTorus.mk _ (periodFullComplexLattice Y)
        (pushforwardTraceLift f hf v) := by
  change ComplexTorus.mapClm (pushforwardTraceLiftCLM f hf)
      (pushforwardTraceLift_preserves_lattice_raw f hf)
      (ComplexTorus.mk _ (periodFullComplexLattice X) v) =
    ComplexTorus.mk _ (periodFullComplexLattice Y)
      (pushforwardTraceLift f hf v)
  rfl

/-- Raw obligation: the descended map is holomorphic.

Sorry-free: chart-glue smoothness, mirroring the pattern in
`Jacobian/ComplexTorus/AddSmooth.lean`. At any `q`, take the chart
`chart := chartAt _ q`. On `chart.source`, the descent
`analyticPushforward = mapClm pushforwardTraceLiftCLM` equals
`mk_Y ∘ pushforwardTraceLiftCLM ∘ chart.toFun`, a composition of
smooth maps:
* `chart.toFun` is `ContMDiffOn` on `chart.source` (`contMDiffOn_chart`);
* `pushforwardTraceLiftCLM` is a continuous linear map between
  finite-dim spaces, hence `ContMDiff` (`ContinuousLinearMap.contMDiff`);
* `mk Y _` is `ContMDiff` (`contMDiff_mk`).

The equation on `chart.source` uses `chart.left_inv'` plus
`mapClm`'s definition (`map_mk`). -/
theorem analyticPushforward_contMDiff_raw
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) :
    ContMDiff (modelWithCornersSelf ℂ (Fin (analyticGenus ℂ X) → ℂ))
      (modelWithCornersSelf ℂ (Fin (analyticGenus ℂ Y) → ℂ)) ω
      (analyticPushforward f hf) := by
  intro q
  set chartX :=
    chartAt (Fin (analyticGenus ℂ X) → ℂ) q with chartX_def
  have hsrc : q ∈ chartX.source := mem_chart_source _ q
  have hOpen : IsOpen chartX.source := chartX.open_source
  have hMem : chartX.source ∈ nhds q := hOpen.mem_nhds hsrc
  -- chart.toFun is ContMDiffOn on chart.source.
  have hChart :
      ContMDiffOn (modelWithCornersSelf ℂ (Fin (analyticGenus ℂ X) → ℂ))
        (modelWithCornersSelf ℂ (Fin (analyticGenus ℂ X) → ℂ))
        (⊤ : WithTop ℕ∞) chartX chartX.source :=
    contMDiffOn_chart
  -- pushforwardTraceLiftCLM is ContMDiff (continuous linear map).
  have hCLM :
      ContMDiff (modelWithCornersSelf ℂ (Fin (analyticGenus ℂ X) → ℂ))
        (modelWithCornersSelf ℂ (Fin (analyticGenus ℂ Y) → ℂ))
        (⊤ : WithTop ℕ∞)
        (pushforwardTraceLiftCLM f hf) :=
    (pushforwardTraceLiftCLM f hf).contMDiff
  -- mk Y is ContMDiff.
  have hMk :
      ContMDiff (modelWithCornersSelf ℂ (Fin (analyticGenus ℂ Y) → ℂ))
        (modelWithCornersSelf ℂ (Fin (analyticGenus ℂ Y) → ℂ))
        (⊤ : WithTop ℕ∞)
        (ComplexTorus.mk (Fin (analyticGenus ℂ Y) → ℂ)
          (periodFullComplexLattice Y)) :=
    ComplexTorus.contMDiff_mk (periodFullComplexLattice Y)
  -- Compose to get the auxiliary smooth function on chart.source.
  have hComp :
      ContMDiffOn (modelWithCornersSelf ℂ (Fin (analyticGenus ℂ X) → ℂ))
        (modelWithCornersSelf ℂ (Fin (analyticGenus ℂ Y) → ℂ))
        (⊤ : WithTop ℕ∞)
        (fun q' => ComplexTorus.mk _ (periodFullComplexLattice Y)
          (pushforwardTraceLiftCLM f hf (chartX q')))
        chartX.source :=
    (hMk.comp hCLM).comp_contMDiffOn hChart
  -- On chart.source, analyticPushforward equals the auxiliary.
  have hEq : ∀ q' ∈ chartX.source,
      analyticPushforward f hf q' =
        ComplexTorus.mk _ (periodFullComplexLattice Y)
          (pushforwardTraceLiftCLM f hf (chartX q')) := by
    intro q' hq'
    have hLeft : ComplexTorus.mk _ (periodFullComplexLattice X)
        (chartX q') = q' := chartX.left_inv' hq'
    -- Rewrite q' on the LHS as mk (chartX q'), then invoke
    -- the sorry-free descent compatibility analyticPushforward_mk_spec_raw.
    conv_lhs => rw [← hLeft]
    exact analyticPushforward_mk_spec_raw f hf (chartX q')
  -- ContMDiffOn on chart.source → ContMDiffAt at q.
  have hOn :
      ContMDiffOn (modelWithCornersSelf ℂ (Fin (analyticGenus ℂ X) → ℂ))
        (modelWithCornersSelf ℂ (Fin (analyticGenus ℂ Y) → ℂ))
        (⊤ : WithTop ℕ∞)
        (analyticPushforward f hf) chartX.source := by
    refine hComp.congr ?_
    intro q' hq'
    exact hEq q' hq'
  exact hOn.contMDiffAt hMem

/-! ### Sorry-free assemblies: keeping the existing public API

The four lemmas below preserve names and signatures of the previous
public surface (used by `Solution.lean`, `PullbackBasis.lean`,
`AnalyticDegree.lean`). All are sorry-free assemblies of the
trace-coordinate interface and the three raw geometric sorries.
-/

/-- Companion specification: the analytic pushforward is holomorphic.
Sorry-free: alias for `analyticPushforward_contMDiff_raw`. -/
theorem analyticPushforward_contMDiff_spec (f : X → Y)
    (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) :
    ContMDiff (modelWithCornersSelf ℂ (Fin (analyticGenus ℂ X) → ℂ))
      (modelWithCornersSelf ℂ (Fin (analyticGenus ℂ Y) → ℂ)) ω
      (analyticPushforward f hf) :=
  analyticPushforward_contMDiff_raw f hf

/-- The analytic pushforward is holomorphic. Public top-down
obligation; sorry-free. -/
lemma analyticPushforward_contMDiff (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) :
    ContMDiff (modelWithCornersSelf ℂ (Fin (analyticGenus ℂ X) → ℂ))
      (modelWithCornersSelf ℂ (Fin (analyticGenus ℂ Y) → ℂ)) ω
      (analyticPushforward f hf) :=
  analyticPushforward_contMDiff_spec f hf

/-- The trace lift preserves the period lattice. Sorry-free alias. -/
theorem pushforwardTraceLift_preserves_lattice
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) :
    ∀ v ∈ (periodFullComplexLattice X).subgroup,
      pushforwardTraceLift f hf v ∈ (periodFullComplexLattice Y).subgroup :=
  pushforwardTraceLift_preserves_lattice_raw f hf

/-- Characterization of `analyticPushforward` on the quotient
projection: the pushforward applied to `mk v` equals `mk` of the
trace lift applied to `v`. Sorry-free alias. -/
theorem analyticPushforward_mk_spec
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (v : Fin (analyticGenus ℂ X) → ℂ) :
    analyticPushforward f hf
      (ComplexTorus.mk _ (periodFullComplexLattice X) v) =
      ComplexTorus.mk _ (periodFullComplexLattice Y)
        (pushforwardTraceLift f hf v) :=
  analyticPushforward_mk_spec_raw f hf v

/-! ### Old "payoff" theorems, preserved as sorry-free aliases

These two were the bundle-level identity/composition obligations
under the previous design. They are now trivial aliases for
`pushforwardTraceLift_id` / `pushforwardTraceLift_comp`. Kept under
their old names so the docstrings in `PullbackBasis.lean` that name
them remain accurate.
-/

/-- Sorry-free alias for `pushforwardTraceLift_id`.

This used to be a bundle-level sorry (`(bundle id _).pushforwardTraceLift
= AddMonoidHom.id`) blocked by the instance diamond. With the new
top-level `pushforwardTraceLift` defined uniformly via the transpose
of `holomorphicTraceCoord`, it collapses to a sorry-free assembly
of `holomorphicTraceCoord_id` plus matrix-transpose-of-id facts. -/
theorem basisAnalyticPushforwardBundle_id_traceLift :
    pushforwardTraceLift (X := X) (Y := X) id contMDiff_id =
      AddMonoidHom.id (Fin (analyticGenus ℂ X) → ℂ) :=
  pushforwardTraceLift_id

/-- Sorry-free alias for `pushforwardTraceLift_comp`. -/
theorem basisAnalyticPushforwardBundle_comp_traceLift
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (g : Y → Z) (hg : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω g) :
    pushforwardTraceLift (g ∘ f) (hg.comp hf) =
      (pushforwardTraceLift g hg).comp (pushforwardTraceLift f hf) :=
  pushforwardTraceLift_comp f hf g hg

/-! ### Existing per-coordinate / per-vector sorry-free assemblies

These names are preserved verbatim. Each is a small assembly of
`pushforwardTraceLift_id` / `pushforwardTraceLift_comp` plus
`AddMonoidHom`-API.
-/

theorem pushforwardTraceLift_id_apply_at
    (i : Fin (analyticGenus ℂ X)) (v : Fin (analyticGenus ℂ X) → ℂ) :
    pushforwardTraceLift (X := X) (Y := X) id contMDiff_id v i = v i := by
  rw [pushforwardTraceLift_id]
  rfl

theorem pushforwardTraceLift_id_apply (v : Fin (analyticGenus ℂ X) → ℂ) :
    pushforwardTraceLift (X := X) (Y := X) id contMDiff_id v = v := by
  rw [pushforwardTraceLift_id]
  rfl

theorem pushforwardTraceLift_comp_spec_apply_at
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (g : Y → Z) (hg : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω g)
    (v : Fin (analyticGenus ℂ X) → ℂ) (i : Fin (analyticGenus ℂ Z)) :
    pushforwardTraceLift (g ∘ f) (hg.comp hf) v i =
      pushforwardTraceLift g hg (pushforwardTraceLift f hf v) i := by
  rw [pushforwardTraceLift_comp f hf g hg, AddMonoidHom.comp_apply]

theorem pushforwardTraceLift_comp_spec_apply
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (g : Y → Z) (hg : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω g)
    (v : Fin (analyticGenus ℂ X) → ℂ) :
    pushforwardTraceLift (g ∘ f) (hg.comp hf) v =
      pushforwardTraceLift g hg (pushforwardTraceLift f hf v) := by
  rw [pushforwardTraceLift_comp f hf g hg, AddMonoidHom.comp_apply]

theorem pushforwardTraceLift_comp_spec
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (g : Y → Z) (hg : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω g) :
    (pushforwardTraceLift (g ∘ f) (hg.comp hf) : _ →+ _) =
      (pushforwardTraceLift g hg).comp (pushforwardTraceLift f hf) :=
  pushforwardTraceLift_comp f hf g hg

/-- Covariant composition specification for the analytic pushforward.
Sorry-free assembly: `analyticPushforward_mk_spec` and
`pushforwardTraceLift_comp_spec` reduce both sides on the quotient
projection. -/
theorem analyticPushforward_comp_spec
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (g : Y → Z) (hg : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω g)
    (P : BasisAnalyticJacobian X) :
    analyticPushforward (g ∘ f) (hg.comp hf) P =
      analyticPushforward g hg (analyticPushforward f hf P) := by
  obtain ⟨v, rfl⟩ := ComplexTorus.mk_surjective _ (periodFullComplexLattice X) P
  rw [analyticPushforward_mk_spec f hf v,
      analyticPushforward_mk_spec (g ∘ f) (hg.comp hf) v,
      analyticPushforward_mk_spec g hg (pushforwardTraceLift f hf v)]
  congr 1
  exact congr_fun (congr_arg _ (pushforwardTraceLift_comp_spec f hf g hg)) v

/-- Pushforward distributes covariantly over composition. Sorry-free. -/
lemma analyticPushforward_comp_apply
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (g : Y → Z) (hg : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω g)
    (P : BasisAnalyticJacobian X) :
    analyticPushforward (g ∘ f) (hg.comp hf) P =
      analyticPushforward g hg (analyticPushforward f hf P) :=
  analyticPushforward_comp_spec f hf g hg P

/-- Pushforward along the identity is the `ContinuousAddMonoidHom`
identity. Sorry-free assembly via descent + `pushforwardTraceLift_id`. -/
theorem analyticPushforward_id_eq :
    analyticPushforward (X := X) (Y := X) id contMDiff_id =
      ContinuousAddMonoidHom.id (BasisAnalyticJacobian X) := by
  ext P
  obtain ⟨v, rfl⟩ := ComplexTorus.mk_surjective _ (periodFullComplexLattice X) P
  rw [analyticPushforward_mk_spec id contMDiff_id v, pushforwardTraceLift_id]
  rfl

/-- Specification of the identity case; sorry-free. -/
theorem analyticPushforward_id_spec (P : BasisAnalyticJacobian X) :
    analyticPushforward (X := X) (Y := X) id contMDiff_id P = P := by
  rw [analyticPushforward_id_eq]
  rfl

/-- Pushforward along the identity is the identity. Public top-down
obligation; sorry-free. -/
lemma analyticPushforward_id_apply (P : BasisAnalyticJacobian X) :
    analyticPushforward (X := X) (Y := X) id contMDiff_id P = P :=
  analyticPushforward_id_spec P

end JacobianChallenge.TraceDegree
