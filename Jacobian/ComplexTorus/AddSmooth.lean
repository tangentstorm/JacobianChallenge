import Jacobian.ComplexTorus.MkSmooth
import Jacobian.ComplexTorus.Add
import Mathlib.Geometry.Manifold.Algebra.Monoid
import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Geometry.Manifold.ContMDiff.Constructions

/-!
# Smoothness of addition on the complex torus

Queue B sibling. `(p1, p2) ↦ p1 + p2 : V/Λ × V/Λ → V/Λ` is
`ContMDiff ℂ ω` for the product manifold structure.

Strategy: at any `(q1, q2)`, work in the product chart
`chartAt q1 ×ₚ chartAt q2`. On the product chart's source, the
function `(q1', q2') ↦ q1' + q2'` equals
`mk ∘ (· + ·) ∘ (chart1.toFun × chart2.toFun)`, a composition of
three smooth maps:

* The product map `(chart1, chart2) : V/Λ × V/Λ → V × V` is
  `ContMDiffOn` on the product chart source (each factor is a
  chart).
* `(· + ·) : V × V → V` is `ContDiff` (continuous linear).
* `mk : V → V/Λ` is `ContMDiff` (`contMDiff_mk`).

The equality on the source uses `mk_add` and the chart left-inverse.
-/

namespace JacobianChallenge.ComplexTorus

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]

/-- Addition `(q1, q2) ↦ q1 + q2` on the complex torus is `ContMDiff ℂ ω`. -/
theorem contMDiff_quotient_add (Λ : FullComplexLattice V) :
    ContMDiff ((modelWithCornersSelf ℂ V).prod (modelWithCornersSelf ℂ V))
      (modelWithCornersSelf ℂ V) (⊤ : WithTop ℕ∞)
      (fun p : quotient V Λ × quotient V Λ => p.1 + p.2) := by
  intro p
  obtain ⟨q1, q2⟩ := p
  set chart1 := chartAt V q1 with chart1_def
  set chart2 := chartAt V q2 with chart2_def
  have hsrc1 : q1 ∈ chart1.source := mem_chart_source V q1
  have hsrc2 : q2 ∈ chart2.source := mem_chart_source V q2
  set s : Set (quotient V Λ × quotient V Λ) :=
    chart1.source ×ˢ chart2.source with s_def
  have hOpen : IsOpen s := chart1.open_source.prod chart2.open_source
  have hMem : s ∈ nhds (q1, q2) := hOpen.mem_nhds ⟨hsrc1, hsrc2⟩
  -- chart1 and chart2 are ContMDiffOn on their sources.
  have hChart1 : ContMDiffOn (modelWithCornersSelf ℂ V)
      (modelWithCornersSelf ℂ V) (⊤ : WithTop ℕ∞) chart1 chart1.source :=
    contMDiffOn_chart
  have hChart2 : ContMDiffOn (modelWithCornersSelf ℂ V)
      (modelWithCornersSelf ℂ V) (⊤ : WithTop ℕ∞) chart2 chart2.source :=
    contMDiffOn_chart
  -- Project + chart on each factor.
  have hProj1 : ContMDiff ((modelWithCornersSelf ℂ V).prod
      (modelWithCornersSelf ℂ V)) (modelWithCornersSelf ℂ V)
      (⊤ : WithTop ℕ∞)
      (Prod.fst : quotient V Λ × quotient V Λ → quotient V Λ) :=
    contMDiff_fst
  have hProj2 : ContMDiff ((modelWithCornersSelf ℂ V).prod
      (modelWithCornersSelf ℂ V)) (modelWithCornersSelf ℂ V)
      (⊤ : WithTop ℕ∞)
      (Prod.snd : quotient V Λ × quotient V Λ → quotient V Λ) :=
    contMDiff_snd
  -- chart1 ∘ fst is ContMDiffOn s = chart1.source ×ˢ chart2.source.
  have hChart1Fst : ContMDiffOn ((modelWithCornersSelf ℂ V).prod
      (modelWithCornersSelf ℂ V)) (modelWithCornersSelf ℂ V)
      (⊤ : WithTop ℕ∞)
      (fun p : quotient V Λ × quotient V Λ => chart1 p.1) s := by
    refine hChart1.comp hProj1.contMDiffOn ?_
    rintro ⟨q1', q2'⟩ ⟨h1, _⟩; exact h1
  have hChart2Snd : ContMDiffOn ((modelWithCornersSelf ℂ V).prod
      (modelWithCornersSelf ℂ V)) (modelWithCornersSelf ℂ V)
      (⊤ : WithTop ℕ∞)
      (fun p : quotient V Λ × quotient V Λ => chart2 p.2) s := by
    refine hChart2.comp hProj2.contMDiffOn ?_
    rintro ⟨q1', q2'⟩ ⟨_, h2⟩; exact h2
  -- Sum in V is ContMDiff.
  have hAddV : ContMDiffOn ((modelWithCornersSelf ℂ V).prod
      (modelWithCornersSelf ℂ V)) (modelWithCornersSelf ℂ V)
      (⊤ : WithTop ℕ∞)
      (fun p : quotient V Λ × quotient V Λ => chart1 p.1 + chart2 p.2) s :=
    hChart1Fst.add hChart2Snd
  -- mk : V → V/Λ is ContMDiff; compose.
  have hMk : ContMDiff (modelWithCornersSelf ℂ V) (modelWithCornersSelf ℂ V)
      (⊤ : WithTop ℕ∞) (mk V Λ) := contMDiff_mk Λ
  have hComp : ContMDiffOn ((modelWithCornersSelf ℂ V).prod
      (modelWithCornersSelf ℂ V)) (modelWithCornersSelf ℂ V)
      (⊤ : WithTop ℕ∞)
      (fun p : quotient V Λ × quotient V Λ =>
        mk V Λ (chart1 p.1 + chart2 p.2)) s :=
    hMk.comp_contMDiffOn hAddV
  -- On s, the composition equals (·.1 + ·.2).
  have hEq : ∀ p ∈ s,
      mk V Λ (chart1 p.1 + chart2 p.2) = p.1 + p.2 := by
    rintro ⟨q1', q2'⟩ ⟨h1, h2⟩
    have hm1 : mk V Λ (chart1 q1') = q1' := chart1.left_inv' h1
    have hm2 : mk V Λ (chart2 q2') = q2' := chart2.left_inv' h2
    rw [mk_add, hm1, hm2]
  have hAddOn : ContMDiffOn ((modelWithCornersSelf ℂ V).prod
      (modelWithCornersSelf ℂ V)) (modelWithCornersSelf ℂ V)
      (⊤ : WithTop ℕ∞)
      (fun p : quotient V Λ × quotient V Λ => p.1 + p.2) s := by
    refine hComp.congr ?_
    intro p hp
    exact (hEq p hp).symm
  exact hAddOn.contMDiffAt hMem

end JacobianChallenge.ComplexTorus
