import Jacobian.TraceDegree.PullbackBasis
import Jacobian.TraceDegree.PushforwardBasis
import Jacobian.HolomorphicForms.TraceSpec
import Jacobian.TraceDegree.PiecewiseC1Instance
import Jacobian.Periods.TrivializationContinuousLinearMapAt
import Jacobian.Blueprint.Sec02.BranchedDegreeFromHolomorphic

set_option linter.unusedSectionVars false

/-!
# Analytic degree and the trace–pullback identity

The degree of a holomorphic map between compact Riemann surfaces, in
its analytic incarnation, plus the trace–pullback identity that
underlies `Jacobian/Solution.lean`'s `pushforward_pullback` lemma.

Named obligations:

* `analyticDegree f hf` — the degree of `f` (concrete ℕ-valued
  definition: `0` if `f` is constant or if no compatible branched-cover
  datum exists; otherwise the `branchedDegree` of a Classically chosen
  compatible witness);
* `analyticPushforward_analyticPullback` — the trace–pullback
  identity, in basis-aligned form:
  `analyticPushforward (analyticPullback Q) = analyticDegree • Q`.

Bottom-up content: degree is the generic-fiber cardinality (with
ramification multiplicity); the trace–pullback identity is the
classical `tr_f (f* η) = deg(f) · η` for holomorphic 1-forms,
descended through the period quotient.
-/

namespace JacobianChallenge.TraceDegree

open scoped ContDiff Manifold
open JacobianChallenge.AbelJacobi JacobianChallenge.Periods
open JacobianChallenge.HolomorphicForms

variable {X : Type} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
  [StableChartAt ℂ X]
  [JacobianChallenge.HolomorphicForms.FiniteDimensionalHolomorphicOneForms ℂ X]
variable {Y : Type} [TopologicalSpace Y] [T2Space Y] [CompactSpace Y]
  [ConnectedSpace Y] [ChartedSpace ℂ Y]
  [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) Y]
  [StableChartAt ℂ Y]
  [JacobianChallenge.HolomorphicForms.FiniteDimensionalHolomorphicOneForms ℂ Y]

/-- **Concrete analytic degree.** For a smooth map `f : X → Y` of
compact Riemann surfaces, the degree is:

* `0` if `f` is constant;
* `branchedDegree hbc` for a Classically chosen `RamificationIndexCompatible`
  branched-cover datum `hbc`, if such a witness exists;
* `0` otherwise.

This is non-opaque: callers see the dispatch on constancy directly.
The Classical fall-back over `∃ hbc, hbc.RamificationIndexCompatible` is
*not* over the analytic trace/degree frontier — it is over the
existence of a branched-cover datum, which any concrete analytic
construction (e.g. `branchedCoverData_of_nonconstant_holomorphic`)
supplies directly. The existence-then-equality theorem
`analyticDegree_eq_canonical_branchedDegree` collapses the Classical
choice to the canonical compatible witness. -/
noncomputable def analyticDegree (f : X → Y)
    (_hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) : ℕ :=
  open Classical in
  if _hconst : ∃ y₀, ∀ x, f x = y₀ then 0
  else
    if hbc : ∃ hbc : BranchedCoverData X Y f,
        hbc.RamificationIndexCompatible then
      branchedDegree hbc.choose
    else 0

/-- **Analytic degree of constant maps.** Sorry-free: the new
`analyticDegree` definition takes the constant-branch directly. -/
@[simp]
theorem analyticDegree_constant (f : X → Y)
    (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) (hconst : ∃ y₀, ∀ x, f x = y₀) :
    analyticDegree f hf = 0 := by
  unfold analyticDegree
  simp [hconst]

/-- **Branched-degree-uniqueness for holomorphic maps.** Two
`RamificationIndexCompatible` branched-cover data on the same
holomorphic map have equal `branchedDegree`.

This is the load-bearing technical lemma making `analyticDegree`
well-defined independently of the Classical choice of witness: any
two compatible witnesses give the same branched degree, because their
`ramificationIndex` functions both equal `mapAnalyticOrderAt f` on the
(entire) holomorphic locus, and the finite-fiber `toFinset`s depend
only on the set. -/
theorem branchedDegree_eq_of_compatible
    {f : X → Y} (hHol : IsHolomorphic f)
    (h₁ h₂ : BranchedCoverData X Y f)
    (hc₁ : h₁.RamificationIndexCompatible)
    (hc₂ : h₂.RamificationIndexCompatible) :
    branchedDegree h₁ = branchedDegree h₂ := by
  classical
  -- Pick any base point on Y
  set y : Y := Classical.arbitrary Y
  rw [branchedDegree_eq_weightedFiberCard h₁ y,
      branchedDegree_eq_weightedFiberCard h₂ y]
  -- Both equal a sum over the finite fibre toFinset; the toFinset only
  -- depends on the underlying set, so the two toFinsets agree.
  unfold BranchedCoverData.weightedFiberCard
  have hfin_eq : (h₁.finite_fiber y).toFinset = (h₂.finite_fiber y).toFinset :=
    Set.Finite.toFinset_inj.mpr rfl
  rw [hfin_eq]
  refine Finset.sum_congr rfl ?_
  intro x _
  -- ramificationIndex x = mapAnalyticOrderAt f x on both sides (compatibility + holomorphicity).
  rw [hc₁ x (hHol.holomorphicAt x), hc₂ x (hHol.holomorphicAt x)]

/-- **Analytic degree equals branched degree, canonical form.** For a
nonconstant smooth map of compact Riemann surfaces, the analytic degree
agrees with the branched degree of **any** `RamificationIndexCompatible`
branched-cover datum on `f` (provided `f` is holomorphic, which is
automatic from smoothness via the kfold package).

Sorry-free: uses `branchedDegree_eq_of_compatible` to compare the
Classically chosen witness inside `analyticDegree` with the supplied one. -/
theorem analyticDegree_eq_canonical_branchedDegree (f : X → Y)
    (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (hHol : IsHolomorphic f)
    (hbc : BranchedCoverData X Y f)
    (hcompat : hbc.RamificationIndexCompatible)
    (hnonconst : ¬ ∃ y₀, ∀ x, f x = y₀) :
    analyticDegree f hf = branchedDegree hbc := by
  classical
  unfold analyticDegree
  simp only [dif_neg hnonconst]
  -- The existence witness is nonempty: hbc itself.
  have hex : ∃ hbc' : BranchedCoverData X Y f,
      hbc'.RamificationIndexCompatible := ⟨hbc, hcompat⟩
  simp only [dif_pos hex]
  -- Compare Classical.choose with hbc via branched-degree uniqueness.
  exact branchedDegree_eq_of_compatible hHol _ hbc hex.choose_spec hcompat

omit [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [IsManifold 𝓘(ℂ) ω X] [StableChartAt ℂ X]
  [T2Space Y] [CompactSpace Y] [IsManifold 𝓘(ℂ) ω Y] [StableChartAt ℂ Y] in
/-- **Analytic degree identity, explicit form (legacy wrapper).** The
equality between the analytic degree and a supplied branched-cover
degree, given the equation as a hypothesis. New callers should prefer
`analyticDegree_eq_canonical_branchedDegree`. -/
theorem analyticDegree_eq_branchedDegree (f : X → Y)
    (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (hbc : JacobianChallenge.HolomorphicForms.BranchedCoverData X Y f)
    (hdegree : analyticDegree f hf = JacobianChallenge.HolomorphicForms.branchedDegree hbc) :
    analyticDegree f hf =
      JacobianChallenge.HolomorphicForms.branchedDegree hbc := hdegree

/-- **The weighted-fiber conservation provider.** Sorry-free wrapper
around `hasWeightedFiberConservation_of_contMDiff` (which packages
the analytic theorem `weightedFiberConservation_of_contMDiff` from
`Jacobian/HolomorphicForms/HolomorphicMap.lean`).

Trace-degree consumers no longer carry a provider-local analytic gap;
the remaining analytic content lives where it belongs, in
`HolomorphicMap.lean`. -/
theorem hasWeightedFiberConservation_provider (f : X → Y)
    (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) :
    HasWeightedFiberConservation f :=
  hasWeightedFiberConservation_of_contMDiff hf

/-- **The narrow trace regularity provider.** Global trace of
holomorphic 1-forms agrees with the regular-value local trace formula.

Sorry-free assembly from the narrow analytic construction provider
`traceFormsConstructionData_provider`: the `map_zero` field is the
construction data's `map_zero_spec` applied to `rfl : (0 : _) = 0`;
the `apply_fun_regular` field unfolds `traceFormsBundled` to the
construction data's `traceForm` and invokes `regular_spec`. -/
noncomputable def traceFormsRegularSpec_provider (f : X → Y)
    (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) :
    TraceFormsRegularSpec f hf where
  map_zero := by
    change (traceFormsConstructionData_provider f hf 0).traceForm = 0
    exact (traceFormsConstructionData_provider f hf 0).map_zero_spec rfl
  apply_fun_regular := by
    intro hbc η y hy
    change (traceFormsConstructionData_provider f hf η).traceForm.toFun y = _
    exact (traceFormsConstructionData_provider f hf η).regular_spec hbc y hy

/-- **The narrow trace-pullback identity provider.** The form-level
identity `tr_f (f* η) = deg(f) · η` (Steps 3-5 of the analytic proof
outline: holomorphic extension across the branch locus).

Assembled here from four narrow inputs, the same shape as
`trace_pullback_identity_of_spec` in `TraceBundled.lean`:
* `traceFormsRegularSpec_provider` — regular-value trace formula;
* `hasLocalKfoldRamification_of_contMDiff` — local k-fold ramification;
* `hasWeightedFiberConservation_provider` — weighted-fiber conservation;
* `analyticDegree_eq_canonical_branchedDegree` — degree normalisation.

The mirror assembly `trace_pullback_identity_of_spec` in
`TraceBundled.lean` takes the same shape but with an explicit
`TraceFormsRegularSpec` boundary; here the trace spec is supplied via
the named provider so callers can use the identity uniformly with the
provider-based interface. -/
noncomputable def trace_pullback_provider (f : X → Y)
    (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (η : HolomorphicOneForm ℂ Y) :
    traceFormsBundled f hf (pullbackFormsBundled f hf η) =
      (analyticDegree f hf : ℂ) • η := by
  classical
  set htrace : TraceFormsRegularSpec f hf := traceFormsRegularSpec_provider f hf with htrace_def
  set hkfold : HasLocalKfoldRamification f := hasLocalKfoldRamification_of_contMDiff hf
    with hkfold_def
  set hw : HasWeightedFiberConservation f := hasWeightedFiberConservation_provider f hf
    with hw_def
  have hHol : IsHolomorphic f := isHolomorphic_of_contMDiff hf hkfold
  by_cases hconst : ∃ y₀, ∀ x, f x = y₀
  · -- Constant case: both sides are zero.
    have hpb_zero : pullbackFormsBundled f hf η = 0 := by
      apply ContMDiffSection.coe_inj
      funext x
      obtain ⟨y₀, hf_const⟩ := hconst
      have hf_eq : f = fun _ : X => y₀ := funext hf_const
      subst f
      simp [pullbackFormsBundled, pullbackFormsFunFiber, mfderiv_const]
    rw [hpb_zero, htrace.map_zero, analyticDegree_constant f hf hconst]
    apply ContMDiffSection.ext
    intro y
    simp
  · -- Nonconstant case: descend through the regular locus by the identity principle.
    set hbc := JacobianChallenge.Blueprint.branchedCoverData_of_nonconstant_holomorphic
      hHol hw hconst with hbc_def
    have hcompat : hbc.RamificationIndexCompatible :=
      JacobianChallenge.Blueprint.branchedCoverData_of_nonconstant_holomorphic_compatible
        hHol hw hconst
    have hdeg : analyticDegree f hf = branchedDegree hbc :=
      analyticDegree_eq_canonical_branchedDegree f hf hHol hbc hcompat hconst
    rw [hdeg]
    apply holomorphicOneForm_ext_on (regularLocus_dense hbc)
    intro y hy
    rw [branchedDegree_eq_weightedFiberCard hbc y,
        htrace.apply_fun_regular hbc (pullbackFormsBundled f hf η) y hy]
    exact trace_pullback_at_regular_value hbc hcompat hf hHol η y hy

/-- **Linear trace-pullback identity.** The trace of the pullback of a
holomorphic 1-form (both viewed as linear maps) is degree
multiplication.

Sorry-free corollary of `trace_pullback_provider`: applying it
pointwise to each form and packaging as a linear-map equation. -/
theorem traceFormsBundledLM_pullbackFormsBundledLM_eq_degree_smul
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) :
    (traceFormsBundledLM f hf).comp (pullbackFormsBundledLM X Y f hf) =
      (analyticDegree f hf : ℂ) • LinearMap.id := by
  apply LinearMap.ext
  intro η
  show traceFormsBundledLM f hf (pullbackFormsBundledLM X Y f hf η) =
    (analyticDegree f hf : ℂ) • η
  -- traceFormsBundledLM is the linear-map shim around traceFormsBundled;
  -- pullbackFormsBundledLM is the linear-map shim around pullbackFormsBundled.
  show traceFormsBundled f hf (pullbackFormsBundled f hf η) = _
  exact trace_pullback_provider f hf η

/-- **Matrix-level trace-pullback identity.** The composition of
trace-coord and pullback-coord matrices is `analyticDegree` times the
identity matrix.

Sorry-free assembly: convert
`traceFormsBundledLM_pullbackFormsBundledLM_eq_degree_smul` from
linear maps on `HolomorphicOneForm ℂ Y` to matrices via
`Module.Basis.equivFun`. -/
theorem traceFormsCoord_holomorphicTraceCoord_eq_degree_smul
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) :
    (traceFormsCoord f hf).comp (holomorphicTraceCoord f hf) =
      (analyticDegree f hf : ℂ) • LinearMap.id := by
  apply LinearMap.ext
  intro v
  show (traceFormsCoord f hf) (holomorphicTraceCoord f hf v) =
    (analyticDegree f hf : ℂ) • v
  -- Unfold the two coord maps:
  -- holomorphicTraceCoord v = basisX.equivFun (pullbackFormsBundledLM (basisY.equivFun.symm v))
  -- traceFormsCoord w = basisY.equivFun (traceFormsBundledLM (basisX.equivFun.symm w))
  -- So the composition applied at v is:
  -- basisY.equivFun (traceFormsBundledLM (basisX.equivFun.symm (basisX.equivFun (pullbackFormsBundledLM (basisY.equivFun.symm v)))))
  --   = basisY.equivFun (traceFormsBundledLM (pullbackFormsBundledLM (basisY.equivFun.symm v)))
  show (holomorphicOneFormFinBasis ℂ Y).equivFun
      (traceFormsBundledLM f hf
        ((holomorphicOneFormFinBasis ℂ X).equivFun.symm
          ((holomorphicOneFormFinBasis ℂ X).equivFun
            (pullbackFormsBundledLM X Y f hf
              ((holomorphicOneFormFinBasis ℂ Y).equivFun.symm v))))) =
    (analyticDegree f hf : ℂ) • v
  rw [LinearEquiv.symm_apply_apply]
  -- Now: basisY.equivFun (traceFormsBundledLM (pullbackFormsBundledLM (basisY.equivFun.symm v))) = degree • v
  have happ := LinearMap.congr_fun
    (traceFormsBundledLM_pullbackFormsBundledLM_eq_degree_smul f hf)
    ((holomorphicOneFormFinBasis ℂ Y).equivFun.symm v)
  show (holomorphicOneFormFinBasis ℂ Y).equivFun
      (traceFormsBundledLM f hf (pullbackFormsBundledLM X Y f hf
        ((holomorphicOneFormFinBasis ℂ Y).equivFun.symm v))) =
    (analyticDegree f hf : ℂ) • v
  rw [show traceFormsBundledLM f hf (pullbackFormsBundledLM X Y f hf
        ((holomorphicOneFormFinBasis ℂ Y).equivFun.symm v)) =
      (analyticDegree f hf : ℂ) •
        ((holomorphicOneFormFinBasis ℂ Y).equivFun.symm v) from by
    have := happ
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.smul_apply,
      LinearMap.id_apply] at this
    exact this]
  rw [map_smul, LinearEquiv.apply_symm_apply]

/-- **Corrected vector-level push-pull identity.** The composition
`pushforwardTraceLift ∘ traceDualPullbackLift` equals
`(analyticDegree : ℂ) • LinearMap.id` on the covering vector space
`Fin g_Y → ℂ`.

This is the **corrected** push-pull at the dual-coordinate level:
`pushforwardTraceLift = (pullback matrix)^T` and
`traceDualPullbackLift = (trace matrix)^T`, so their composition is
`((trace matrix) · (pullback matrix))^T`. By
`traceFormsCoord_holomorphicTraceCoord_eq_degree_smul`, the inner
matrix product is `(analyticDegree) · I`, whose transpose is itself.

The existing `analyticPullback` is built from
`pullbackTraceLiftCLM = holomorphicTraceCoord` (form-pullback matrix),
which is *not* the correct representative for Jacobian pullback on
dual coordinates. Once `analyticPullback` is rewired to use
`traceDualPullbackLift` instead (with a corrected transfer-cycle
naturality statement for the new lattice preservation), this
vector-level identity will descend to give
`analyticPushforward (analyticPullback Q) = analyticDegree • Q`.

Sorry-free assembly from
`traceFormsCoord_holomorphicTraceCoord_eq_degree_smul` plus matrix
transpose arithmetic. -/
theorem pushforwardTraceLift_traceDualPullbackLift_eq_degree_smul
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) :
    (pushforwardTraceLift f hf).comp
        (traceDualPullbackLift f hf).toAddMonoidHom =
      ((analyticDegree f hf : ℂ) • LinearMap.id (R := ℂ)
        (M := Fin (analyticGenus ℂ Y) → ℂ)).toAddMonoidHom := by
  refine AddMonoidHom.ext fun v => ?_
  show (Matrix.toLin'
        ((holomorphicTraceCoord f hf).toMatrix').transpose)
      ((Matrix.toLin' ((traceFormsCoord f hf).toMatrix').transpose) v) =
    (analyticDegree f hf : ℂ) • v
  -- Combine via toLin'_mul.
  set P := (holomorphicTraceCoord f hf).toMatrix' with hP_def
  set T := (traceFormsCoord f hf).toMatrix' with hT_def
  have hstep1 :
      (Matrix.toLin' P.transpose) ((Matrix.toLin' T.transpose) v) =
        (Matrix.toLin' (P.transpose * T.transpose)) v := by
    rw [← LinearMap.comp_apply, ← Matrix.toLin'_mul]
  rw [hstep1]
  -- Transpose of a product = reversed product of transposes.
  rw [show P.transpose * T.transpose = (T * P).transpose from
    (Matrix.transpose_mul T P).symm]
  -- T * P = (T ∘ P).toMatrix'
  have hPmul :
      T * P = ((traceFormsCoord f hf).comp (holomorphicTraceCoord f hf)).toMatrix' := by
    rw [hT_def, hP_def]
    exact (LinearMap.toMatrix'_comp _ _).symm
  rw [hPmul]
  -- Apply the matrix-level identity.
  rw [traceFormsCoord_holomorphicTraceCoord_eq_degree_smul f hf]
  -- Goal: Matrix.toLin' (((analyticDegree • LinearMap.id).toMatrix').transpose) v = degree • v.
  -- LinearMap.toMatrix' is a LinearEquiv; the smul commutes through both
  -- LinearMap.toMatrix' and Matrix.toLin'.
  rw [show ((analyticDegree f hf : ℂ) • LinearMap.id (R := ℂ)
        (M := Fin (analyticGenus ℂ Y) → ℂ)).toMatrix' =
      (analyticDegree f hf : ℂ) •
        (LinearMap.id (R := ℂ) (M := Fin (analyticGenus ℂ Y) → ℂ)).toMatrix' from by
    exact map_smul LinearMap.toMatrix' _ _]
  rw [LinearMap.toMatrix'_id]
  rw [Matrix.transpose_smul, Matrix.transpose_one]
  show (Matrix.toLin' ((analyticDegree f hf : ℂ) • (1 : Matrix _ _ ℂ))) v =
    (analyticDegree f hf : ℂ) • v
  rw [show Matrix.toLin' ((analyticDegree f hf : ℂ) • (1 : Matrix _ _ ℂ)) =
      (analyticDegree f hf : ℂ) • Matrix.toLin' (1 : Matrix _ _ ℂ) from by
    exact map_smul Matrix.toLin' _ _]
  rw [Matrix.toLin'_one]
  rfl

/-- **The narrow push-pull descent provider.** The basis-aligned
Jacobian push-pull identity, descended from the trace-pullback
identity on holomorphic 1-forms through the period quotient.

### Design status

The vector-level push-pull identity
`pushforwardTraceLift_traceDualPullbackLift_eq_degree_smul` is now
proved sorry-free using the **corrected** dual-coordinate pullback
`traceDualPullbackLift` (= transpose of the trace matrix). However,
the existing `analyticPullback` is built from
`pullbackTraceLiftCLM = holomorphicTraceCoord` (= the form-pullback
matrix), which is the wrong representative for Jacobian pullback on
the dual-quotient `BasisAnalyticJacobian`.

Closing `analyticPushPull_provider` against the existing
`analyticPullback` would require restating
`transferCycle_periodPairing_naturality` against
`traceDualPullbackLift` (the corrected representative) and re-wiring
`analyticPullback`'s `mapClm` to use that lattice preservation. This
is a cascading refactor (the existing functoriality lemmas
`analyticPullback_id`, `analyticPullback_comp` would need re-proof in
the new representation).

This narrow leaf therefore remains a `sorry`, but the **content** of
the push-pull identity is sorry-free at the corrected vector level
via `pushforwardTraceLift_traceDualPullbackLift_eq_degree_smul`. -/
noncomputable def analyticPushPull_provider (f : X → Y)
    [PiecewiseC1PathRegularity X] [PiecewiseC1PathRegularity Y]
    (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) (Q : BasisAnalyticJacobian Y) :
    analyticPushforward f hf (analyticPullback f hf Q) =
      (analyticDegree f hf) • Q := by
  sorry

/-- Bundled analytic trace/degree contract for a holomorphic map of compact
Riemann surfaces.

The fields are the mathematical laws needed by the public route theorems:
constant maps have degree zero (now a definitional fact), nonconstant
analytic degree agrees with the branched-cover degree of any compatible
witness (canonical theorem), the global trace agrees with the local
regular-fiber trace, trace after pullback is degree multiplication on
holomorphic forms, and the descended basis-aligned Jacobian maps satisfy
the corresponding push-pull identity. -/
structure AnalyticTraceDegreeSpec (f : X → Y)
    (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) where
  /-- Constant maps have analytic degree zero. -/
  degree_constant : (∃ y₀, ∀ x, f x = y₀) → analyticDegree f hf = 0
  /-- For nonconstant maps, analytic degree agrees with the constructed
  branched-cover degree under the standard local ramification and weighted
  fiber conservation hypotheses. -/
  degree_eq_branched :
    ∀ (hkfold : HasLocalKfoldRamification f) (hw : HasWeightedFiberConservation f)
      (hnonconst : ¬ ∃ y₀, ∀ x, f x = y₀),
      analyticDegree f hf =
        branchedDegree
          (JacobianChallenge.Blueprint.branchedCoverData_of_nonconstant_holomorphic
            (isHolomorphic_of_contMDiff hf hkfold) hw hnonconst)
  /-- The global trace form agrees with the regular-value local trace. -/
  trace_regular : TraceFormsRegularSpec f hf
  /-- Form-level trace-pullback identity. -/
  trace_pullback :
    ∀ η : HolomorphicOneForm ℂ Y,
      traceFormsBundled f hf (pullbackFormsBundled f hf η) =
        (analyticDegree f hf : ℂ) • η
  /-- Basis-aligned Jacobian push-pull identity. -/
  push_pull :
    ∀ [PiecewiseC1PathRegularity X] [PiecewiseC1PathRegularity Y]
      (Q : BasisAnalyticJacobian Y),
      analyticPushforward f hf (analyticPullback f hf Q) =
        (analyticDegree f hf) • Q

/-- **Assembled analytic trace/degree spec.** All the bundled fields
are now small named providers or sorry-free degree facts.

* `degree_constant` — sorry-free from `analyticDegree_constant`;
* `degree_eq_branched` — sorry-free from
  `analyticDegree_eq_canonical_branchedDegree` plus
  `branchedCoverData_of_nonconstant_holomorphic_compatible`;
* `trace_regular` — delegates to `traceFormsRegularSpec_provider`;
* `trace_pullback` — delegates to `trace_pullback_provider`;
* `push_pull` — delegates to `analyticPushPull_provider`.

The single monolithic frontier of the previous design is now decomposed
into exactly three narrow providers (`traceFormsRegularSpec_provider`,
`trace_pullback_provider`, `analyticPushPull_provider`). -/
noncomputable def analyticTraceDegreeSpec_frontier (f : X → Y)
    (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) :
    AnalyticTraceDegreeSpec f hf where
  degree_constant := analyticDegree_constant f hf
  degree_eq_branched := by
    intro hkfold hw hnonconst
    set hbc := JacobianChallenge.Blueprint.branchedCoverData_of_nonconstant_holomorphic
      (isHolomorphic_of_contMDiff hf hkfold) hw hnonconst with hbc_def
    have hcompat : hbc.RamificationIndexCompatible :=
      JacobianChallenge.Blueprint.branchedCoverData_of_nonconstant_holomorphic_compatible
        (isHolomorphic_of_contMDiff hf hkfold) hw hnonconst
    exact analyticDegree_eq_canonical_branchedDegree f hf
      (isHolomorphic_of_contMDiff hf hkfold) hbc hcompat hnonconst
  trace_regular := traceFormsRegularSpec_provider f hf
  trace_pullback := trace_pullback_provider f hf
  push_pull := fun Q => analyticPushPull_provider f hf Q

/-- Companion specification (anti-hack obligation): the trace-pullback
identity in basis-aligned form. This remains an explicit frontier; it
is not hidden as a fake field of the basis pullback bundle. -/
theorem analyticPushforward_analyticPullback_spec (f : X → Y)
    [PiecewiseC1PathRegularity X] [PiecewiseC1PathRegularity Y]
    (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) (Q : BasisAnalyticJacobian Y) :
    analyticPushforward f hf (analyticPullback f hf Q) =
      (analyticDegree f hf) • Q :=
  analyticPushPull_provider f hf Q

/- The trace–pullback identity, in basis-aligned form: pushforward
of pullback equals degree-multiplication on `BasisAnalyticJacobian Y`.

Top-down obligation. Bottom-up: descend the classical trace–pullback
identity `tr_f (f* η) = deg(f) · η` (on holomorphic 1-forms) through
the period quotient.

### Decomposition (post-refactor)

`analyticPushforward_analyticPullback` is delegated to
`analyticPushPull_provider`. The form-level identity is
`trace_pullback_provider`. Trace regularity is
`traceFormsRegularSpec_provider`. Degree facts
(`analyticDegree_constant`, `analyticDegree_eq_canonical_branchedDegree`)
are sorry-free.

### Dependency graph

```
analyticPushforward_analyticPullback
  └── analyticPushPull_provider                        (narrow sorry)
        ↑ descended from
        trace_pullback_provider                        (sorry-free)
              ↑ assembled from
              traceFormsRegularSpec_provider           (narrow sorry)
              analyticDegree_eq_canonical_branchedDegree (sorry-free)
              identity-principle on holomorphic 1-forms (sorry-free)
``` -/
/-- Compatibility wrapper using the named push-pull frontier. -/
lemma analyticPushforward_analyticPullback (f : X → Y)
    [PiecewiseC1PathRegularity X] [PiecewiseC1PathRegularity Y]
    (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) (Q : BasisAnalyticJacobian Y) :
    analyticPushforward f hf (analyticPullback f hf Q) =
      (analyticDegree f hf) • Q :=
  analyticPushforward_analyticPullback_spec f hf Q


end JacobianChallenge.TraceDegree
