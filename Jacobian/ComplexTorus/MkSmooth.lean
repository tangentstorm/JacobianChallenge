import Jacobian.ComplexTorus.Add
import Jacobian.ComplexTorus.Mk
import Jacobian.ComplexTorus.MkSmoothOnChartTarget
import Jacobian.ComplexTorus.TransitionSubMem
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace

/-!
# Smoothness of the quotient projection `mk : V → V ⧸ Λ.subgroup`

Queue B sibling. Combines `contMDiffOn_chartAt_symm` with the
`Λ`-translation invariance of `mk` to prove `ContMDiff (mk V Λ)`.

Strategy at each `x : V`:

* `q := mk x`. The chart at `q` has its representative
  `x' := (chartAt V q) q ∈ Metric.ball (surjInv q) (δ/4)` and
  satisfies `mk x' = q = mk x`, so `g := x' - x ∈ Λ.subgroup`
  (`localSection_sub_mem_subgroup`).
* `mk` is `ContMDiffOn` on the chart target (which is open and
  contains `x'`), so `ContMDiffAt mk x'`.
* The affine translation `T y := y + g` is smooth and
  `T x = x'`, so `ContMDiffAt (mk ∘ T) x = ContMDiffAt mk (T x)`.
* `mk (y + g) = mk y + mk g = mk y` since `g ∈ Λ.subgroup` is in
  the kernel of `mk`. Hence `mk = mk ∘ T`, so `ContMDiffAt mk x`.
-/

namespace JacobianChallenge.ComplexTorus

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]

/-- The quotient projection `mk V Λ : V → V ⧸ Λ.subgroup` is
`ContMDiff ℂ ω` (analytic as a map between manifolds). -/
theorem contMDiff_mk (Λ : FullComplexLattice V) :
    ContMDiff (modelWithCornersSelf ℂ V) (modelWithCornersSelf ℂ V)
      (⊤ : WithTop ℕ∞) (mk V Λ : V → quotient V Λ) := by
  intro x
  set q : quotient V Λ := mk V Λ x with q_def
  -- Get the chart-target representative x' = chart.toFun q ∈ chart.target.
  have hsrc : q ∈ (chartAt V q).source := mem_chart_source V q
  set x' : V := (chartAt V q).toFun q with x'_def
  have hx'_target : x' ∈ (chartAt V q).target :=
    (chartAt V q).map_source' hsrc
  have hmkx' : mk V Λ x' = q := (chartAt V q).left_inv' hsrc
  -- mk is ContMDiffOn on chart.target, so ContMDiffAt at x'.
  have hmk_on_target : ContMDiffOn (modelWithCornersSelf ℂ V)
      (modelWithCornersSelf ℂ V) (⊤ : WithTop ℕ∞)
      (chartAt V q).symm (chartAt V q).target :=
    contMDiffOn_chartAt_symm Λ q
  have hopen : IsOpen (chartAt V q).target := (chartAt V q).open_target
  have hmk_at_x' : ContMDiffAt (modelWithCornersSelf ℂ V)
      (modelWithCornersSelf ℂ V) (⊤ : WithTop ℕ∞)
      (chartAt V q).symm x' :=
    hmk_on_target.contMDiffAt (hopen.mem_nhds hx'_target)
  -- Translation T y := y + (x' - x) is ContMDiff (smooth affine).
  set g : V := x' - x with g_def
  have hT : ContMDiff (modelWithCornersSelf ℂ V) (modelWithCornersSelf ℂ V)
      (⊤ : WithTop ℕ∞) (fun y : V => y + g) :=
    (contDiff_id.add contDiff_const).contMDiff
  -- ContMDiffAt of (chartAt V q).symm ∘ (· + g) at x.
  have hcomp : ContMDiffAt (modelWithCornersSelf ℂ V)
      (modelWithCornersSelf ℂ V) (⊤ : WithTop ℕ∞)
      ((chartAt V q).symm ∘ (fun y : V => y + g)) x := by
    have hTx : (fun y : V => y + g) x = x' := by simp [g_def]
    exact hmk_at_x'.comp_of_eq (hT.contMDiffAt) hTx
  -- (chartAt V q).symm ∘ (· + g) and mk V Λ agree on a nbhd of x:
  -- we'll show they actually agree as a function, but Lean's chart .symm is
  -- not literally `mk` (it's an OpenPartialHomeomorph whose toFun is mk).
  -- We use ContMDiffAt.congr_of_eventuallyEq with a true everywhere-eq.
  -- First: g ∈ Λ.subgroup, since mk x' = mk x.
  have hg_mem : g ∈ Λ.subgroup := by
    -- mk x = mk x' ⟹ -x + x' ∈ Λ.subgroup via mk_eq_iff. Then -x + x' = x' - x = g.
    have hmk_eq : mk V Λ x = mk V Λ x' := hmkx'.symm
    have h1 : -x + x' ∈ Λ.subgroup := (mk_eq_iff Λ).mp hmk_eq
    have h2 : -x + x' = g := by rw [g_def, neg_add_eq_sub, sub_eq_neg_add, add_comm]
    rw [← h2]; exact h1
  -- Now: mk(y + g) = mk y + mk g = mk y (since g ∈ Λ.subgroup ⟹ mk g = 0).
  have hmk_g : mk V Λ g = 0 := (mk_eq_zero_iff Λ).mpr hg_mem
  have hmk_eq_fun : (fun y : V => mk V Λ (y + g)) = mk V Λ := by
    funext y
    rw [mk_add, hmk_g, add_zero]
  -- And on chart.target, (chart V q).symm = mk via OpenPartialHomeomorph coercion.
  -- That equality is by definition of chartAtBall (.invFun = mk V Λ).
  have hsymm_eq : ((chartAt V q).symm : V → quotient V Λ) = mk V Λ := rfl
  -- Combine to convert hcomp into ContMDiffAt mk x.
  rw [hsymm_eq] at hcomp
  -- Now hcomp : ContMDiffAt _ _ ⊤ (mk V Λ ∘ (· + g)) x
  -- And mk V Λ ∘ (· + g) = mk V Λ as functions (by hmk_eq_fun).
  have heq : (mk V Λ : V → quotient V Λ) ∘ (fun y : V => y + g)
           = (mk V Λ : V → quotient V Λ) := hmk_eq_fun
  rw [← heq]
  exact hcomp

end JacobianChallenge.ComplexTorus
