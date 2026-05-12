import Jacobian.HolomorphicForms.OnePointCxIsManifold
import Jacobian.HolomorphicForms.Defs
import Jacobian.HolomorphicForms.EntireZero
import Jacobian.HolomorphicForms.ChartSectionContDiff
import Mathlib.CategoryTheory.Category.Basic

/-!
# Continuity of cotangent section local representative in the inversion chart

Proves `ContMDiffSection_localRepr_inversionChart_continuousAt_zero`:
the function `w ↦ ω(inversionChart.symm w)(1)` is ContinuousAt at `w = 0`.

## Proof outline

Every holomorphic 1-form on `OnePoint ℂ ≅ ℂℙ¹` is identically zero
(a consequence of Liouville's theorem). The ContinuousAt then follows
trivially because the function is identically zero.

The proof decomposes into:
1. **Identity chart coefficient is entire** (from G2a / chart-trivialisation API)
2. **Identity chart coefficient tends to 0 at infinity** (from the
   inversion-chart trivialization analysis: the trivialized representative
   H(w) is smooth at 0, and `f(w⁻¹) = -w² H(w)(1)` gives `|f(z)| ≤ C/|z|²`)
3. **Liouville** → `f ≡ 0`
4. **Section vanishes at finite points** (from `f ≡ 0`)
5. **Section vanishes at ∞** (from trivialization + dense set argument)
6. **ContinuousAt** (trivial for the zero function)
-/

namespace JacobianChallenge.HolomorphicForms

open scoped Manifold Topology
open Filter

/-! ### Helpers -/

/-- A CLM `ℂ →L[ℂ] ℂ` that maps 1 to 0 is the zero map. -/
theorem clm_eq_zero_of_apply_one_eq_zero' (f : ℂ →L[ℂ] ℂ) (h : f 1 = 0) : f = 0 := by
  have : ∀ x : ℂ, f x = 0 := by
    intro x
    have := f.map_smul (x : ℂ) (1 : ℂ)
    simp at this
    rw [this, h, mul_zero]
  exact ContinuousLinearMap.ext this

/-! ### Step 1: Identity chart coefficient is entire

This is the content of the structural axiom G2a. The proof requires
the chart-trivialisation API for `ContMDiffSection` on the cotangent
bundle, which is a Mathlib v4.28.0 gap. We accept this as given. -/

/-- The identity chart coefficient `z ↦ ω(↑z)(1)` is `ContDiff`.
This is equivalent to the structural axiom G2a. -/
theorem identityChartCoeff_contDiff (ω : HolomorphicOneForm ℂ (OnePoint ℂ)) :
    ContDiff ℂ ⊤ (fun z : ℂ => ω.toFun (↑z : OnePoint ℂ)
      (show TangentSpace (modelWithCornersSelf ℂ ℂ) (↑z : OnePoint ℂ) from (1 : ℂ))) := by
  convert contMDiffSection_localRepr_identityChart_contDiff ω using 1

/-- The identity chart coefficient is differentiable (entire). -/
theorem identityChartCoeff_differentiable (ω : HolomorphicOneForm ℂ (OnePoint ℂ)) :
    Differentiable ℂ (fun z : ℂ => ω.toFun (↑z : OnePoint ℂ)
      (show TangentSpace (modelWithCornersSelf ℂ ℂ) (↑z : OnePoint ℂ) from (1 : ℂ))) :=
  (identityChartCoeff_contDiff ω).differentiable (by simp)

/-! ### Step 2: Identity chart coefficient tends to 0 at infinity

The trivialized inversion-chart representative `H(w)` is smooth at `w = 0`
(from `contMDiffAt_section_iff` at `∞`). The Hom-bundle trivialization
formula gives `f(w⁻¹) = -w² · H(w)(1)` for `w ≠ 0`. Since `H(w)(1)` is
bounded near `0`, we get `|f(z)| ≤ C/|z|²` for large `|z|`.

**BLOCKED (2026-05-12).** The proof requires the cotangent chart-overlap
pullback formula `f(w⁻¹) = -w² · H(w)(1)` (where `H` is the trivialized
inversion-chart representative). This is exactly the missing prerequisite
`holomorphicOneForm_chartOverlap_pullback` in
`Jacobian/HolomorphicForms/GenusZeroClassification.lean` (line ~426), which
is itself a `sorry` pending the chart-trivialisation + cotangent-pullback
API on the cotangent bundle (Mathlib v4.28.0 gap; see G4b in
`GenusZeroClassification.lean`).

Boundedness of `H(w)(1)` near `w = 0` alone is insufficient: the decay
`|f(z)| ≤ C/|z|²` (and hence `Tendsto … (cocompact ℂ) (nhds 0)`) requires
the explicit Jacobian factor `-w²` from the chart transition `z = w⁻¹`,
`dz/dw = -1/w²`.

`GenusZeroClassification.lean` cannot be imported here without creating an
import cycle (`GenusZeroClassification` imports `InversionChartContinuity`).
Resolving this leaf therefore requires either:
* discharging `holomorphicOneForm_chartOverlap_pullback` (cotangent
  bundle chain-rule formula), or
* relocating the chart-overlap formula into a file upstream of both
  `InversionChartContinuity` and `GenusZeroClassification`.

Until one of the above is done, the leaf statement is kept unchanged and
left as `sorry` per the project's anti-axiomatisation policy. -/

theorem identityChartCoeff_tendsto_zero (ω : HolomorphicOneForm ℂ (OnePoint ℂ)) :
    Tendsto (fun z : ℂ => ω.toFun (↑z : OnePoint ℂ)
      (show TangentSpace (modelWithCornersSelf ℂ ℂ) (↑z : OnePoint ℂ) from (1 : ℂ)))
      (cocompact ℂ) (nhds 0) := by
  -- BLOCKER: cotangent chart-overlap pullback formula
  -- (`holomorphicOneForm_chartOverlap_pullback` in `GenusZeroClassification.lean`,
  -- currently a sorry).  See the docstring above for details.
  sorry

/-! ### Step 3: Liouville → f ≡ 0 -/

theorem identityChartCoeff_eq_zero (ω : HolomorphicOneForm ℂ (OnePoint ℂ)) (z : ℂ) :
    ω.toFun (↑z : OnePoint ℂ)
      (show TangentSpace (modelWithCornersSelf ℂ ℂ) (↑z : OnePoint ℂ) from (1 : ℂ)) = 0 := by
  have hd := identityChartCoeff_differentiable ω
  have ht := identityChartCoeff_tendsto_zero ω
  have h := hd.eq_zero_of_tendsto_zero_cocompact ht
  exact congr_fun h z

/-! ### Step 4: Section vanishes at finite points -/

theorem section_finite_eq_zero' (ω : HolomorphicOneForm ℂ (OnePoint ℂ)) (z : ℂ) :
    ω.toFun (↑z : OnePoint ℂ) = 0 :=
  clm_eq_zero_of_apply_one_eq_zero' _ (identityChartCoeff_eq_zero ω z)

/-! ### Step 5: Section vanishes at ∞ -/

/-
The section is zero at ∞. Uses the trivialization at ∞: the trivialized
representative `H(x)` is continuous, `H(↑z) = 0` for `z ≠ 0` (since
`ω(↑z) = 0`), and the dense subset argument gives `H(∞) = 0 = ω(∞)`.
-/
theorem section_infty_eq_zero' (ω : HolomorphicOneForm ℂ (OnePoint ℂ)) :
    ω.toFun (OnePoint.infty : OnePoint ℂ) = 0 := by
  by_contra h_nonzero;
  -- Let $e$ be the trivialization at $\infty$.
  set e := trivializationAt (CotangentModelFiber ℂ) (CotangentSpace ℂ (OnePoint ℂ)) (OnePoint.infty);
  -- Let $H(x) = (e ⟨x, ω(x)⟩).2$ for $x ∈ e.baseSet$.
  set H : OnePoint ℂ → ℂ →L[ℂ] ℂ := fun x => (e ⟨x, ω x⟩).2;
  have hH_cont : ContinuousOn H e.baseSet := by
    have hH_cont : ContinuousOn (fun x => e ⟨x, ω x⟩) e.baseSet := by
      refine' e.continuousOn.comp _ _;
      · refine' Continuous.continuousOn _;
        have := ω.2;
        convert this.continuous using 1;
      · intro x hx; aesop;
    exact ContinuousOn.snd hH_cont
  have hH_zero : ∀ z : ℂ, z ≠ 0 → H (OnePoint.some z) = 0 := by
    -- Since $ω(z) = 0$ for all $z ≠ 0$, we have $H(z) = 0$ for all $z ≠ 0$.
    intros z hz
    have hω_zero : ω.toFun (OnePoint.some z) = 0 := by
      nontriviality;
      exact section_finite_eq_zero' ω z
    simp [H];
    convert e.zeroSection _ _;
    any_goals exact OnePoint.some z;
    any_goals exact ℂ;
    all_goals try infer_instance;
    · constructor <;> intro h <;> simp_all +decide [ Prod.ext_iff ];
      · convert e.zeroSection _ _;
        any_goals exact OnePoint.some z;
        any_goals exact ℂ;
        all_goals try infer_instance;
        · simp +decide [ Prod.ext_iff, Bundle.zeroSection ];
        · simp +decide [ e ];
          simp +decide [ chartAt ];
          simp +decide [ ChartedSpace.chartAt ];
          simp +decide [ inversionChart, hz ];
      · convert h.2;
    · simp +zetaDelta at *;
      simp +decide [ chartAt ];
      simp +decide [ ChartedSpace.chartAt ];
      simp +decide [ inversionChart, hz ]
  have hH_zero_base : H OnePoint.infty = 0 := by
    have hH_zero_base : ∀ᶠ x in nhdsWithin OnePoint.infty {OnePoint.infty}ᶜ, H x = 0 := by
      rw [ eventually_nhdsWithin_iff ];
      rw [ OnePoint.nhds_infty_eq ];
      simp +zetaDelta at *;
      exact Filter.mem_of_superset ( Filter.mem_of_superset ( Filter.mem_cocompact.mpr ⟨ Metric.closedBall 0 1, ProperSpace.isCompact_closedBall _ _, by aesop_cat ⟩ ) fun x hx => by aesop_cat ) fun x hx => hH_zero x hx;
    convert tendsto_nhds_unique ( hH_cont.continuousAt ( IsOpen.mem_nhds ( show IsOpen e.baseSet from ?_ ) <| by aesop ) |> fun h => h.mono_left inf_le_left ) ( tendsto_nhds_of_eventually_eq hH_zero_base ) using 1;
    exact e.open_baseSet
  have hω_infty : ω.toFun OnePoint.infty = 0 := by
    have hω_infty : e ⟨OnePoint.infty, ω.toFun OnePoint.infty⟩ = e ⟨OnePoint.infty, 0⟩ := by
      have hω_infty : (e ⟨OnePoint.infty, ω.toFun OnePoint.infty⟩).2 = (e ⟨OnePoint.infty, 0⟩).2 := by
        convert hH_zero_base using 1;
        convert e.zeroSection _;
        any_goals exact ℂ;
        all_goals try infer_instance;
        exact ⟨ fun h => fun _ => Prod.ext rfl h, fun h => h ( by simp +decide [ e ] ) |> congr_arg Prod.snd ⟩;
      exact Prod.ext ( by aesop ) hω_infty;
    have := e.injOn ( show { proj := OnePoint.infty, snd := ω.toFun OnePoint.infty } ∈ e.source from ?_ ) ( show { proj := OnePoint.infty, snd := 0 } ∈ e.source from ?_ ) hω_infty ; aesop;
    · simp +decide [ e, Trivialization.source_eq ];
    · simp +decide [ e.mem_source ];
      exact FiberBundle.mem_baseSet_trivializationAt' OnePoint.infty
  exact h_nonzero hω_infty;

/-! ### Assembly -/

theorem holomorphicOneForm_onePointCx_eq_zero
    (ω : HolomorphicOneForm ℂ (OnePoint ℂ)) (x : OnePoint ℂ) :
    ω.toFun x = 0 := by
  cases x using OnePoint.rec with
  | infty => exact section_infty_eq_zero' ω
  | coe z => exact section_finite_eq_zero' ω z

theorem ContMDiffSection_localRepr_inversionChart_continuousAt_zero_proof
    (ω : HolomorphicOneForm ℂ (OnePoint ℂ)) :
    ContinuousAt (fun w => ω.toFun (inversionChart.symm w)
      (show TangentSpace (modelWithCornersSelf ℂ ℂ)
        (inversionChart.symm w) from (1 : ℂ))) 0 := by
  have h : ∀ w, ω.toFun (inversionChart.symm w)
      (show TangentSpace (modelWithCornersSelf ℂ ℂ)
        (inversionChart.symm w) from (1 : ℂ)) = 0 := by
    intro w
    rw [holomorphicOneForm_onePointCx_eq_zero ω]
    exact ContinuousLinearMap.zero_apply _
  simp only [h]
  exact continuousAt_const

end JacobianChallenge.HolomorphicForms
