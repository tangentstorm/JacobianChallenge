import Jacobian.ComplexTorus.MkSmooth
import Jacobian.ComplexTorus.Neg
import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace

/-!
# Smoothness of negation on the complex torus

Queue B sibling. `Neg.neg : quotient V Λ → quotient V Λ` is `ContMDiff ℂ ω`.

Strategy: at any `q : V/Λ`, work in the chart at `q`. On the chart's
source, the function `q' ↦ -q'` equals
`mk ∘ Neg.neg ∘ chart.toFun`, which is a composition of three smooth
maps:

* `chart.toFun = localSection` is `ContMDiffOn` on the chart source
  (Mathlib `contMDiffOn_chart`).
* `Neg.neg : V → V` is `ContDiff` (linear), hence `ContMDiff`.
* `mk : V → V/Λ` is `ContMDiff` (the previous tick's `contMDiff_mk`).

The equality on the chart source uses `mk_neg` and the chart's
left-inverse `chart.symm.toFun ∘ chart.toFun = id` (= `mk_localSection`).
-/

namespace JacobianChallenge.ComplexTorus

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]

/-- Negation `q ↦ -q` on the complex torus is `ContMDiff ℂ ω`. -/
theorem contMDiff_quotient_neg (Λ : FullComplexLattice V) :
    ContMDiff (modelWithCornersSelf ℂ V) (modelWithCornersSelf ℂ V)
      (⊤ : WithTop ℕ∞) (fun q : quotient V Λ => -q) := by
  intro q
  set chart := chartAt V q with chart_def
  have hsrc : q ∈ chart.source := mem_chart_source V q
  have hOpen : IsOpen chart.source := chart.open_source
  have hMem : chart.source ∈ nhds q := hOpen.mem_nhds hsrc
  -- chart.toFun is ContMDiffOn on chart.source.
  have hChart : ContMDiffOn (modelWithCornersSelf ℂ V)
      (modelWithCornersSelf ℂ V) (⊤ : WithTop ℕ∞) chart chart.source :=
    contMDiffOn_chart
  -- Neg.neg : V → V is ContMDiff.
  have hNegV : ContMDiff (modelWithCornersSelf ℂ V) (modelWithCornersSelf ℂ V)
      (⊤ : WithTop ℕ∞) (Neg.neg : V → V) :=
    (contDiff_neg.contMDiff)
  -- mk : V → V/Λ is ContMDiff.
  have hMk : ContMDiff (modelWithCornersSelf ℂ V) (modelWithCornersSelf ℂ V)
      (⊤ : WithTop ℕ∞) (mk V Λ) := contMDiff_mk Λ
  -- Compose: mk ∘ Neg.neg ∘ chart is ContMDiffOn on chart.source.
  have hComp : ContMDiffOn (modelWithCornersSelf ℂ V)
      (modelWithCornersSelf ℂ V) (⊤ : WithTop ℕ∞)
      ((mk V Λ) ∘ (Neg.neg : V → V) ∘ chart) chart.source :=
    hMk.comp_contMDiffOn (hNegV.comp_contMDiffOn hChart)
  -- On chart.source, mk(-(chart q')) = -q'.
  have hEq : ∀ q' ∈ chart.source,
      ((mk V Λ) ∘ (Neg.neg : V → V) ∘ chart) q' = -q' := by
    intro q' hq'
    have hmk : mk V Λ (chart q') = q' := chart.left_inv' hq'
    show mk V Λ (-(chart q')) = -q'
    rw [mk_neg, hmk]
  -- ContMDiffOn (· -·) on chart.source via `congr`.
  have hNegOn : ContMDiffOn (modelWithCornersSelf ℂ V)
      (modelWithCornersSelf ℂ V) (⊤ : WithTop ℕ∞)
      (fun q' : quotient V Λ => -q') chart.source := by
    refine hComp.congr ?_
    intro q' hq'
    exact (hEq q' hq').symm
  exact hNegOn.contMDiffAt hMem

end JacobianChallenge.ComplexTorus
