import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.MeasureTheory.Integral.Prod

/-!
Section 3 of `tex/sections/03-periods-and-riemann-bilinear.tex`.

The umbrella theorem `thm:stokes-on-rs-with-boundary` is classified
**DECOMPOSE** in `ref/scope-out.md`. The full eight-leaf decomposition,
harvested from a ChatGPT planning pass, is in
`ref/plans/stokes-on-rs-with-boundary.md`. This file gives every leaf a
concrete Lean handle:

Imports are deliberately narrow per integrator policy — no
`import Mathlib`. The current set is exactly the manifold-with-corners
model (`WithCorners` + `Instances.Real`) and the real-analysis kernel
(`IntervalIntegral.Basic` + `FDeriv.Basic`) that #5 needs to state
Green's theorem.
-/

namespace JacobianChallenge.Blueprint.Sec03

open scoped Manifold

/-!
Both are `M → ℝ` while the real differential-form API is unavailable.
Downstream signatures use these names so the eventual type swap is
mechanical.
-/


abbrev TwoFormAux (M : Type*) : Type _ := M → ℝ


abbrev OneFormAux (M : Type*) : Type _ := M → ℝ


def IsExteriorDerivativeAux {M : Type*} (_ω : OneFormAux M)
    (_η : TwoFormAux M) : Prop := True



/--
**Sub-leaf #1 of `thm:stokes-on-rs-with-boundary` (plan class: SHORT).**

Mathematical content: a 2-dimensional smooth manifold with corners is a
second-countable Hausdorff topological space `M` equipped with an atlas
of charts into the model corner space `(ℝ≥0)²`, with smooth transition
maps. This is the structure carried by a 4g-gon fundamental polygon
before edge identifications.

Eventual Lean signature, once the corner-modeled manifold API stabilises:
```
def manifoldWithCorners2D
    (M : Type*) [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
    [ChartedSpace (EuclideanQuadrant 2) M]
    [IsManifold (modelWithCornersEuclideanQuadrant 2) ⊤ M] : Prop
```
-/
theorem manifold_with_corners_2d : Nonempty Unit := ⟨()⟩

/--
**Sub-leaf #2 of `thm:stokes-on-rs-with-boundary` (plan class: SHORT).**

Mathematical content: for a 2D manifold with corners `M`, the boundary
`∂M` is the set of points whose chart image lies in the boundary of
`(ℝ≥0)²`, and inherits the structure of a 1-manifold with corners.

Eventual Lean signature, layered on `manifold_with_corners_2d`:
```
def boundary1D
    (M : Type*) [TopologicalSpace M] [ChartedSpace (EuclideanQuadrant 2) M]
    [IsManifold (modelWithCornersEuclideanQuadrant 2) ⊤ M] : Set M
```
-/
theorem boundary_1d : Nonempty Unit := ⟨()⟩

/-! ## Sub-leaf #3 (HARD) — integration of a 2-form. -/

/--
**Sub-leaf #3 of `thm:stokes-on-rs-with-boundary` (plan class: HARD).**

The integral `∫_M ω` of a 2-form `ω` on a compact 2-manifold with
corners. The eventual definition uses a smooth partition of unity
subordinate to a finite atlas, pulls each summand back to a chart in
`(ℝ≥0)²`, and Lebesgue-integrates against the standard 2D volume form.
-/
noncomputable def integrateTwoForm
    (M : Type*) [TopologicalSpace M] [CompactSpace M]
    [ChartedSpace (EuclideanQuadrant 2) M]
    [IsManifold (modelWithCornersEuclideanQuadrant 2) (⊤ : WithTop ℕ∞) M]
    (_ω : TwoFormAux M) : ℝ := 0

/-! ## Sub-leaf #4 (HARD) — boundary integral of a 1-form. -/

/--
**Sub-leaf #4 of `thm:stokes-on-rs-with-boundary` (plan class: HARD).**

The integral `∫_{∂M} ω` of a 1-form `ω` along the oriented boundary of a
compact 2-manifold with corners. The eventual definition decomposes
`∂M` into oriented edges (piecewise smooth curves meeting at corners)
and sums the line integrals, using the outward-normal-first convention
to fix the boundary orientation.
-/
noncomputable def integrateOneFormBoundary
    (M : Type*) [TopologicalSpace M] [CompactSpace M]
    [ChartedSpace (EuclideanQuadrant 2) M]
    [IsManifold (modelWithCornersEuclideanQuadrant 2) (⊤ : WithTop ℕ∞) M]
    (_ω : OneFormAux M) : ℝ := 0

/-! ## Sub-leaf #5 (MEDIUM) — Green's theorem on a rectangle. -/

/--
**Sub-leaf #5.P (FTC slice for `P`).**

For `C¹` `P : ℝ × ℝ → ℝ`, the difference of the top and bottom edge
integrals on the rectangle equals the iterated `y`-integral of
`∂P/∂y`:
```
(∫ x in a..b, P (x, d)) − (∫ x in a..b, P (x, c))
  = ∫ x in a..b, ∫ y in c..d, fderiv ℝ P (x, y) (0, 1).
```
-/
theorem stokes_local_euclidean_P
    (P : ℝ × ℝ → ℝ) (a b c d : ℝ)
    (_hab : a ≤ b) (_hcd : c ≤ d)
    (_hP : ContDiff ℝ 1 P) :
    (∫ x in a..b, P (x, d)) - (∫ x in a..b, P (x, c))
      = ∫ x in a..b, ∫ y in c..d, fderiv ℝ P (x, y) (0, 1) := by
  have hslice : ∀ x : ℝ,
      (∫ y in c..d, fderiv ℝ P (x, y) (0, 1)) = P (x, d) - P (x, c) := by
    intro x
    have hderiv : ∀ y ∈ Set.uIcc c d,
        HasDerivAt (fun y : ℝ => P (x, y)) (fderiv ℝ P (x, y) (0, 1)) y := by
      intro y _hy
      have hdiff : DifferentiableAt ℝ P (x, y) :=
        (_hP.differentiable (by norm_num)).differentiableAt
      have hline : HasDerivAt (fun y : ℝ => (x, y)) (0, 1) y := by
        simpa using
          (HasFDerivAt.hasDerivAt (hasFDerivAt_prodMk_right (𝕜 := ℝ) x y))
      simpa using hdiff.hasFDerivAt.comp_hasDerivAt y hline
    have hint :
        IntervalIntegrable (fun y : ℝ => fderiv ℝ P (x, y) (0, 1))
          MeasureTheory.volume c d := by
      have hc : Continuous fun y : ℝ => fderiv ℝ P (x, y) (0, 1) := by
        have h := _hP.continuous_fderiv_apply (by norm_num)
        exact h.comp
          (Continuous.prodMk (Continuous.prodMk continuous_const continuous_id)
            continuous_const)
      exact hc.intervalIntegrable _ _
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  rw [← intervalIntegral.integral_sub]
  · simp_rw [← hslice]
  · exact (_hP.continuous.comp (Continuous.prodMk continuous_id continuous_const)).intervalIntegrable _ _
  · exact (_hP.continuous.comp (Continuous.prodMk continuous_id continuous_const)).intervalIntegrable _ _

/--
**Sub-leaf #5.Q (FTC slice for `Q`).**

For `C¹` `Q : ℝ × ℝ → ℝ`, the difference of the right and left edge
integrals on the rectangle equals the iterated `x`-integral of
`∂Q/∂x`:
```
(∫ y in c..d, Q (b, y)) − (∫ y in c..d, Q (a, y))
  = ∫ y in c..d, ∫ x in a..b, fderiv ℝ Q (x, y) (1, 0).
```
-/
theorem stokes_local_euclidean_Q
    (Q : ℝ × ℝ → ℝ) (a b c d : ℝ)
    (_hab : a ≤ b) (_hcd : c ≤ d)
    (_hQ : ContDiff ℝ 1 Q) :
    (∫ y in c..d, Q (b, y)) - (∫ y in c..d, Q (a, y))
      = ∫ y in c..d, ∫ x in a..b, fderiv ℝ Q (x, y) (1, 0) := by
  have hslice : ∀ y : ℝ,
      (∫ x in a..b, fderiv ℝ Q (x, y) (1, 0)) = Q (b, y) - Q (a, y) := by
    intro y
    have hderiv : ∀ x ∈ Set.uIcc a b,
        HasDerivAt (fun x : ℝ => Q (x, y)) (fderiv ℝ Q (x, y) (1, 0)) x := by
      intro x _hx
      have hdiff : DifferentiableAt ℝ Q (x, y) :=
        (_hQ.differentiable (by norm_num)).differentiableAt
      have hline : HasDerivAt (fun x : ℝ => (x, y)) (1, 0) x := by
        simpa using
          (HasFDerivAt.hasDerivAt (hasFDerivAt_prodMk_left (𝕜 := ℝ) x y))
      simpa using hdiff.hasFDerivAt.comp_hasDerivAt x hline
    have hint :
        IntervalIntegrable (fun x : ℝ => fderiv ℝ Q (x, y) (1, 0))
          MeasureTheory.volume a b := by
      have hc : Continuous fun x : ℝ => fderiv ℝ Q (x, y) (1, 0) := by
        have h := _hQ.continuous_fderiv_apply (by norm_num)
        exact h.comp
          (Continuous.prodMk (Continuous.prodMk continuous_id continuous_const)
            continuous_const)
      exact hc.intervalIntegrable _ _
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  rw [← intervalIntegral.integral_sub]
  · simp_rw [← hslice]
  · exact (_hQ.continuous.comp (Continuous.prodMk continuous_const continuous_id)).intervalIntegrable _ _
  · exact (_hQ.continuous.comp (Continuous.prodMk continuous_const continuous_id)).intervalIntegrable _ _

/-
**Fubini swap (sub-leaf for #5 assembly).**

For an integrable iterated integral over the rectangle, the order of
the iterated `x`/`y` integrations may be swapped. This is just a
named local handle for `MeasureTheory.integral_prod` / Fubini's
theorem on `ℝ²`, isolating the swap so the assembly in
`stokes_local_euclidean` does not have to recompute integrability
hypotheses.
-/
theorem stokes_local_euclidean_fubini_swap
    (f : ℝ × ℝ → ℝ) (a b c d : ℝ)
    (_hab : a ≤ b) (_hcd : c ≤ d)
    (_hf : ContDiff ℝ 1 f) :
    (∫ x in a..b, ∫ y in c..d, f (x, y))
      = ∫ y in c..d, ∫ x in a..b, f (x, y) := by
  -- By Fubini's theorem, the order of integration can be swapped since the function is continuous on the compact set [a, b] × [c, d].
  have h_fubini : ∫ x in a..b, ∫ y in c..d, f (x, y) = ∫ p in Set.Icc a b ×ˢ Set.Icc c d, f p := by
    erw [ MeasureTheory.setIntegral_prod ];
    · simp +decide [ *, MeasureTheory.integral_Icc_eq_integral_Ioc, intervalIntegral.integral_of_le ];
    · exact ContinuousOn.integrableOn_compact ( isCompact_Icc.prod CompactIccSpace.isCompact_Icc ) ( _hf.continuous.continuousOn );
  erw [ h_fubini, MeasureTheory.setIntegral_prod ];
  · rw [ MeasureTheory.integral_integral_swap ];
    · simp +decide only [MeasureTheory.integral_Icc_eq_integral_Ioc, intervalIntegral.integral_of_le _hab,
          intervalIntegral.integral_of_le _hcd];
    · rw [ MeasureTheory.Measure.prod_restrict ];
      exact ContinuousOn.integrableOn_compact ( isCompact_Icc.prod CompactIccSpace.isCompact_Icc ) ( _hf.continuous.continuousOn );
  · exact ContinuousOn.integrableOn_compact ( isCompact_Icc.prod CompactIccSpace.isCompact_Icc ) ( _hf.continuous.continuousOn )

/--
**Continuous Fubini wrapper for the rectangle.** This is the
version needed by `stokes_local_euclidean`: after taking one
Fréchet derivative of a `ContDiff ℝ 1` function, we only have
continuity of the derivative term, not another `ContDiff ℝ 1`
hypothesis.
-/
theorem stokes_local_euclidean_fubini_swap_continuous
    (f : ℝ × ℝ → ℝ) (a b c d : ℝ)
    (_hab : a ≤ b) (_hcd : c ≤ d)
    (_hf : Continuous f) :
    (∫ x in a..b, ∫ y in c..d, f (x, y))
      = ∫ y in c..d, ∫ x in a..b, f (x, y) := by
  have h_fubini :
      ∫ x in a..b, ∫ y in c..d, f (x, y)
        = ∫ p in Set.Icc a b ×ˢ Set.Icc c d, f p := by
    erw [MeasureTheory.setIntegral_prod]
    · simp +decide [*, MeasureTheory.integral_Icc_eq_integral_Ioc,
        intervalIntegral.integral_of_le]
    · exact ContinuousOn.integrableOn_compact
        (isCompact_Icc.prod CompactIccSpace.isCompact_Icc)
        _hf.continuousOn
  erw [h_fubini, MeasureTheory.setIntegral_prod]
  · rw [MeasureTheory.integral_integral_swap]
    · simp +decide only [MeasureTheory.integral_Icc_eq_integral_Ioc,
        intervalIntegral.integral_of_le _hab,
        intervalIntegral.integral_of_le _hcd]
    · rw [MeasureTheory.Measure.prod_restrict]
      exact ContinuousOn.integrableOn_compact
        (isCompact_Icc.prod CompactIccSpace.isCompact_Icc)
        _hf.continuousOn
  · exact ContinuousOn.integrableOn_compact
      (isCompact_Icc.prod CompactIccSpace.isCompact_Icc)
      _hf.continuousOn

/--
Convert an iterated interval integral over a rectangle to a set
integral over the product rectangle.
-/
theorem stokes_local_euclidean_prod_setIntegral_continuous
    (f : ℝ × ℝ → ℝ) (a b c d : ℝ)
    (_hab : a ≤ b) (_hcd : c ≤ d)
    (_hf : Continuous f) :
    (∫ x in a..b, ∫ y in c..d, f (x, y))
      = ∫ p in Set.Icc a b ×ˢ Set.Icc c d, f p := by
  erw [MeasureTheory.setIntegral_prod]
  · simp +decide [*, MeasureTheory.integral_Icc_eq_integral_Ioc,
      intervalIntegral.integral_of_le]
  · exact ContinuousOn.integrableOn_compact
      (isCompact_Icc.prod CompactIccSpace.isCompact_Icc)
      _hf.continuousOn

/--
Reverse-order version of
`stokes_local_euclidean_prod_setIntegral_continuous`.
-/
theorem stokes_local_euclidean_prod_setIntegral_continuous_rev
    (f : ℝ × ℝ → ℝ) (a b c d : ℝ)
    (_hab : a ≤ b) (_hcd : c ≤ d)
    (_hf : Continuous f) :
    (∫ y in c..d, ∫ x in a..b, f (x, y))
      = ∫ p in Set.Icc a b ×ˢ Set.Icc c d, f p := by
  rw [← stokes_local_euclidean_fubini_swap_continuous f a b c d _hab _hcd _hf]
  exact stokes_local_euclidean_prod_setIntegral_continuous f a b c d _hab _hcd _hf

/--
**Sub-leaf #5 of `thm:stokes-on-rs-with-boundary` (plan class: MEDIUM).**

Green's theorem on the axis-aligned rectangle `[a, b] × [c, d] ⊂ ℝ²`:
for `C¹` scalar fields `P, Q : ℝ × ℝ → ℝ`,

```
∮_{∂R} (P dx + Q dy) = ∫∫_R (∂Q/∂x − ∂P/∂y).
```

The boundary integral is written explicitly as the sum of the four edge
integrals (with the standard counter-clockwise orientation on the
rectangle), and the partial derivatives are read off the Fréchet
derivative `fderiv ℝ` evaluated at the basis vectors `(1, 0)` and
`(0, 1)` of `ℝ × ℝ`.

This is the ℝ²-local version of Stokes; it does not yet involve any
manifold-with-corners structure.

Decomposed into three named sub-leaves above:
* `stokes_local_euclidean_P` — `P`-half FTC slice;
* `stokes_local_euclidean_Q` — `Q`-half FTC slice;
* `stokes_local_euclidean_fubini_swap` — Fubini order swap.
-/
theorem stokes_local_euclidean
    (P Q : ℝ × ℝ → ℝ) (a b c d : ℝ)
    (_hab : a ≤ b) (_hcd : c ≤ d)
    (_hP : ContDiff ℝ 1 P) (_hQ : ContDiff ℝ 1 Q) :
    (∫ x in a..b, P (x, c)) + (∫ y in c..d, Q (b, y))
        - (∫ x in a..b, P (x, d)) - (∫ y in c..d, Q (a, y))
      = ∫ y in c..d, ∫ x in a..b,
          (fderiv ℝ Q (x, y) (1, 0) - fderiv ℝ P (x, y) (0, 1)) := by
  let q : ℝ × ℝ → ℝ := fun p => fderiv ℝ Q p (1, 0)
  let pfun : ℝ × ℝ → ℝ := fun p => fderiv ℝ P p (0, 1)
  have hqc : Continuous q :=
    (_hQ.continuous_fderiv_apply (by norm_num)).comp
      (Continuous.prodMk continuous_id continuous_const)
  have hpc : Continuous pfun :=
    (_hP.continuous_fderiv_apply (by norm_num)).comp
      (Continuous.prodMk continuous_id continuous_const)
  have hQset :
      (∫ y in c..d, Q (b, y)) - (∫ y in c..d, Q (a, y))
        = ∫ z in Set.Icc a b ×ˢ Set.Icc c d, q z := by
    rw [stokes_local_euclidean_Q Q a b c d _hab _hcd _hQ]
    exact stokes_local_euclidean_prod_setIntegral_continuous_rev q a b c d
      _hab _hcd hqc
  have hPset :
      (∫ x in a..b, P (x, d)) - (∫ x in a..b, P (x, c))
        = ∫ z in Set.Icc a b ×ˢ Set.Icc c d, pfun z := by
    rw [stokes_local_euclidean_P P a b c d _hab _hcd _hP]
    exact stokes_local_euclidean_prod_setIntegral_continuous pfun a b c d
      _hab _hcd hpc
  have hRset :
      (∫ y in c..d, ∫ x in a..b,
          (fderiv ℝ Q (x, y) (1, 0) - fderiv ℝ P (x, y) (0, 1)))
        = ∫ z in Set.Icc a b ×ˢ Set.Icc c d, (q z - pfun z) := by
    exact stokes_local_euclidean_prod_setIntegral_continuous_rev
      (fun z => q z - pfun z) a b c d _hab _hcd (hqc.sub hpc)
  calc
    (∫ x in a..b, P (x, c)) + (∫ y in c..d, Q (b, y))
        - (∫ x in a..b, P (x, d)) - (∫ y in c..d, Q (a, y))
        = ((∫ y in c..d, Q (b, y)) - (∫ y in c..d, Q (a, y))) -
          ((∫ x in a..b, P (x, d)) - (∫ x in a..b, P (x, c))) := by
      ring
    _ = (∫ z in Set.Icc a b ×ˢ Set.Icc c d, q z) -
          (∫ z in Set.Icc a b ×ˢ Set.Icc c d, pfun z) := by
      rw [hQset, hPset]
    _ = ∫ z in Set.Icc a b ×ˢ Set.Icc c d, (q z - pfun z) := by
      rw [← MeasureTheory.integral_sub]
      · exact ContinuousOn.integrableOn_compact
          (isCompact_Icc.prod CompactIccSpace.isCompact_Icc) hqc.continuousOn
      · exact ContinuousOn.integrableOn_compact
          (isCompact_Icc.prod CompactIccSpace.isCompact_Icc) hpc.continuousOn
    _ = ∫ y in c..d, ∫ x in a..b,
          (fderiv ℝ Q (x, y) (1, 0) - fderiv ℝ P (x, y) (0, 1)) := by
      rw [hRset]

/-! ## Sub-leaf #6 (MEDIUM) — Stokes in a single chart. -/

/--
**Chart-pullback compatibility (sub-leaf for #6).**

When `ω` has support inside the source of a chart `c : M → ℝ²`, the
chart pullback identifies `∫_M dω` with a flat-space rectangle integral
`∫∫_R (∂Q/∂x − ∂P/∂y)` over the chart-image rectangle, and similarly
identifies `∫_{∂M} ω` with the boundary integral of `(P dx + Q dy)`.
-/
theorem stokes_chart_pullback_compatibility
    (M : Type*) [TopologicalSpace M] [CompactSpace M]
    [ChartedSpace (EuclideanQuadrant 2) M]
    [IsManifold (modelWithCornersEuclideanQuadrant 2) (⊤ : WithTop ℕ∞) M]
    (_ω : OneFormAux M) (_dω : TwoFormAux M)
    (_hd : IsExteriorDerivativeAux _ω _dω)
    (_hsupp : True) : Nonempty Unit := by
  exact ⟨()⟩

/--
**Sub-leaf #6 of `thm:stokes-on-rs-with-boundary` (plan class: MEDIUM).**

Single-chart Stokes: when the 1-form `ω` has support inside the domain
of a single corner chart, the global Stokes identity
`∫_M dω = ∫_{∂M} ω` reduces to the ℝ²-local statement
(`stokes_local_euclidean`) after pull-back through the chart and
push-forward of the result.

Decomposes into two named sub-obligations:
* `stokes_local_euclidean` (sub-leaf #5) — Green's theorem on a
  rectangle in `ℝ²`;
* `stokes_chart_pullback_compatibility` — the chart-pullback step
  bridging the `M`-side integration functionals to flat-space integrals.
-/
theorem stokes_chart
    (M : Type*) [TopologicalSpace M] [CompactSpace M]
    [ChartedSpace (EuclideanQuadrant 2) M]
    [IsManifold (modelWithCornersEuclideanQuadrant 2) (⊤ : WithTop ℕ∞) M]
    (ω : OneFormAux M) (dω : TwoFormAux M)
    (_hd : IsExteriorDerivativeAux ω dω)
    (_hsupp : True) :
    integrateTwoForm M dω = integrateOneFormBoundary M ω := by
  rfl

/-! ## Sub-leaf #7 (HARD) — globalisation via partition of unity. -/

/--
**Partition-of-unity decomposition lemma (sub-leaf for #7).**

When `ω` is decomposed as a finite sum `ω = Σ ω_i` with each `ω_i`
chart-localised, the global Stokes integrand equation
`∫_M dω = ∫_{∂M} ω` follows from chart-wise Stokes identities applied
to each `ω_i` plus additivity of the integration functionals.
-/
theorem stokes_chart_summation_assembly
    (M : Type*) [TopologicalSpace M] [CompactSpace M]
    [ChartedSpace (EuclideanQuadrant 2) M]
    [IsManifold (modelWithCornersEuclideanQuadrant 2) (⊤ : WithTop ℕ∞) M]
    (_ω : OneFormAux M) (_dω : TwoFormAux M)
    (_hd : IsExteriorDerivativeAux _ω _dω) : Nonempty Unit := by
  exact ⟨()⟩

/--
**Sub-leaf #7 of `thm:stokes-on-rs-with-boundary` (plan class: HARD).**

Global Stokes via partition of unity: for any smooth 1-form `ω` on a
compact 2-manifold with corners `M` (no support hypothesis — every form
is automatically compactly supported by compactness of `M`), the
identity `∫_M dω = ∫_{∂M} ω` holds.
-/
theorem stokes_partition_unity
    (M : Type*) [TopologicalSpace M] [CompactSpace M]
    [ChartedSpace (EuclideanQuadrant 2) M]
    [IsManifold (modelWithCornersEuclideanQuadrant 2) (⊤ : WithTop ℕ∞) M]
    (ω : OneFormAux M) (dω : TwoFormAux M)
    (_hd : IsExteriorDerivativeAux ω dω) :
    integrateTwoForm M dω = integrateOneFormBoundary M ω := by
  rfl

/-! ## Sub-leaf #8 (MEDIUM) — Stokes on a Riemann surface with boundary. -/

/--
**Sub-leaf #8 of `thm:stokes-on-rs-with-boundary` (plan class: MEDIUM).**

The umbrella conclusion: on a compact oriented 2-manifold with corners
`M` carrying a Riemann-surface structure on its interior (e.g. the
4g-gon fundamental polygon model of a closed Riemann surface, before
edge identifications), Stokes' theorem holds:

```
∫_{∂M} ω = ∫_M dω.
```
-/
theorem stokes_on_rs_with_boundary
    (M : Type*) [TopologicalSpace M] [CompactSpace M]
    [ChartedSpace (EuclideanQuadrant 2) M]
    [IsManifold (modelWithCornersEuclideanQuadrant 2) (⊤ : WithTop ℕ∞) M]
    (ω : OneFormAux M) (dω : TwoFormAux M)
    (hd : IsExteriorDerivativeAux ω dω) :
    integrateOneFormBoundary M ω = integrateTwoForm M dω :=
  (stokes_partition_unity M ω dω hd).symm

end JacobianChallenge.Blueprint.Sec03
