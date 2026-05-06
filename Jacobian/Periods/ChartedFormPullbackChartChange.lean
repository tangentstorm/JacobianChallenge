import Jacobian.Periods.ChartedFormPullback
import Mathlib.Geometry.Manifold.MFDeriv.Atlas

/-!
# Chart-pullback of a 1-form transforms by chain rule under chart change

**Phase 4a (Lemma A) of the path-integral well-definedness chain.**

For two charts `c_p`, `c_q : OpenPartialHomeomorph X E` taken from the
atlas of a `[IsManifold ⊤]` complex manifold, and a manifold point
`x ∈ c_p.source ∩ c_q.source`, the chart-pullback `chartedFormPullback c_p ω`
evaluated at `c_p x` equals the chart-pullback `chartedFormPullback c_q ω`
evaluated at `c_q x`, *post-composed with the manifold derivative of the
chart transition* `ψ := c_q ∘ c_p.symm`.

This is the genuine chain-rule identity that makes the chart-corrected
path integral chart-independent.

The proof: locally on the open set `c_p.target ∩ c_p.symm⁻¹' c_q.source`,
we have `c_p.symm = c_q.symm ∘ ψ` (since `c_q.symm ∘ c_q = id` on `c_q.source`).
Hence by `Filter.EventuallyEq.mfderiv_eq` plus the chain rule `mfderiv_comp`,
`mfderiv c_p.symm (c_p x) = (mfderiv c_q.symm (c_q x)).comp (mfderiv ψ (c_p x))`.
Substituting into the definitions of `chartedFormPullback` finishes the proof.
-/

namespace JacobianChallenge.Periods

open JacobianChallenge.HolomorphicForms Set

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {X : Type*} [TopologicalSpace X] [ChartedSpace E X]
  [IsManifold (modelWithCornersSelf ℂ E) (⊤ : WithTop ℕ∞) X]

/-- The chart transition `c_q ∘ c_p.symm` is mdifferentiable at `c_p x`
when both charts are taken from the atlas and `x` lies in both sources. -/
theorem chartTransition_mdifferentiableAt
    (p q : X) (x : X)
    (hp : x ∈ (chartAt E p).source) (hq : x ∈ (chartAt E q).source) :
    MDifferentiableAt (modelWithCornersSelf ℂ E) (modelWithCornersSelf ℂ E)
      ((chartAt E q : X → E) ∘ ((chartAt E p).symm : E → X))
      ((chartAt E p) x) := by
  have hcp_mdiff : (chartAt E p : OpenPartialHomeomorph X E).MDifferentiable
      (modelWithCornersSelf ℂ E) (modelWithCornersSelf ℂ E) :=
    mdifferentiable_of_mem_atlas (chart_mem_atlas E p)
  have hcq_mdiff : (chartAt E q : OpenPartialHomeomorph X E).MDifferentiable
      (modelWithCornersSelf ℂ E) (modelWithCornersSelf ℂ E) :=
    mdifferentiable_of_mem_atlas (chart_mem_atlas E q)
  have h_cp_symm : MDifferentiableAt (modelWithCornersSelf ℂ E)
      (modelWithCornersSelf ℂ E) (chartAt E p).symm ((chartAt E p) x) :=
    hcp_mdiff.mdifferentiableAt_symm ((chartAt E p).map_source hp)
  have h_cq : MDifferentiableAt (modelWithCornersSelf ℂ E)
      (modelWithCornersSelf ℂ E) (chartAt E q) ((chartAt E p).symm ((chartAt E p) x)) := by
    rw [(chartAt E p).left_inv hp]
    exact hcq_mdiff.mdifferentiableAt hq
  exact h_cq.comp _ h_cp_symm

/-- The chart-pullback of a holomorphic 1-form transforms by chain rule
under chart change.

For two charts `chartAt E p`, `chartAt E q` on a complex manifold `X`,
and `x ∈ (chartAt E p).source ∩ (chartAt E q).source`,
the chart-pullback at `chartAt E p x` applied to a tangent vector `v`
equals the chart-pullback at `chartAt E q x` applied to the
chart-transition derivative `mfderiv (chartAt E q ∘ (chartAt E p).symm) (chartAt E p x) v`.

This is the **central identity** behind chart-independence of the
chart-corrected path integral: pointwise the integrand transforms
exactly as the chain rule for `mfderiv` predicts. -/
theorem chartedFormPullback_chart_change_apply
    (p q : X) (ω : HolomorphicOneForm E X) (x : X) (v : E)
    (hp : x ∈ (chartAt E p).source) (hq : x ∈ (chartAt E q).source) :
    chartedFormPullback (chartAt E p) ω ((chartAt E p) x) v =
      chartedFormPullback (chartAt E q) ω ((chartAt E q) x)
        ((mfderiv (modelWithCornersSelf ℂ E) (modelWithCornersSelf ℂ E)
            ((chartAt E q : X → E) ∘ ((chartAt E p).symm : E → X)))
          ((chartAt E p) x) v) := by
  -- Notation
  set c_p : OpenPartialHomeomorph X E := chartAt E p with hc_p
  set c_q : OpenPartialHomeomorph X E := chartAt E q with hc_q
  set ψ : E → E := (c_q : X → E) ∘ (c_p.symm : E → X) with hψ_def
  -- Key targets / atlas membership / differentiability:
  have hcp_x_target : c_p x ∈ c_p.target := c_p.map_source hp
  have hcq_x_target : c_q x ∈ c_q.target := c_q.map_source hq
  have hcp_mdiff : c_p.MDifferentiable
      (modelWithCornersSelf ℂ E) (modelWithCornersSelf ℂ E) :=
    mdifferentiable_of_mem_atlas (chart_mem_atlas E p)
  have hcq_mdiff : c_q.MDifferentiable
      (modelWithCornersSelf ℂ E) (modelWithCornersSelf ℂ E) :=
    mdifferentiable_of_mem_atlas (chart_mem_atlas E q)
  have h_cp_symm_at : MDifferentiableAt
      (modelWithCornersSelf ℂ E) (modelWithCornersSelf ℂ E) c_p.symm (c_p x) :=
    hcp_mdiff.mdifferentiableAt_symm hcp_x_target
  have h_cq_symm_at : MDifferentiableAt
      (modelWithCornersSelf ℂ E) (modelWithCornersSelf ℂ E) c_q.symm (c_q x) :=
    hcq_mdiff.mdifferentiableAt_symm hcq_x_target
  have h_cq_at : MDifferentiableAt
      (modelWithCornersSelf ℂ E) (modelWithCornersSelf ℂ E) c_q (c_p.symm (c_p x)) := by
    rw [c_p.left_inv hp]
    exact hcq_mdiff.mdifferentiableAt hq
  have h_ψ_at : MDifferentiableAt
      (modelWithCornersSelf ℂ E) (modelWithCornersSelf ℂ E) ψ (c_p x) :=
    h_cq_at.comp _ h_cp_symm_at
  -- ψ (c_p x) = c_q x:
  have hψ_at_cpx : ψ (c_p x) = c_q x := by
    show c_q (c_p.symm (c_p x)) = c_q x
    rw [c_p.left_inv hp]
  -- Locally c_p.symm = c_q.symm ∘ ψ on the open set c_p.target ∩ c_p.symm⁻¹' c_q.source:
  have hopen : IsOpen (c_p.target ∩ c_p.symm ⁻¹' c_q.source) :=
    c_p.continuousOn_symm.isOpen_inter_preimage c_p.open_target c_q.open_source
  have hmem : c_p x ∈ c_p.target ∩ c_p.symm ⁻¹' c_q.source := by
    refine ⟨hcp_x_target, ?_⟩
    show c_p.symm (c_p x) ∈ c_q.source
    rw [c_p.left_inv hp]
    exact hq
  have hψ_symm_eq : c_p.symm =ᶠ[nhds (c_p x)] (c_q.symm ∘ ψ) := by
    refine Filter.eventually_of_mem (hopen.mem_nhds hmem) ?_
    intro e he
    show c_p.symm e = c_q.symm (c_q (c_p.symm e))
    rw [c_q.left_inv he.2]
  -- Apply chain rule to mfderiv c_p.symm via the EventuallyEq:
  have h_mfderiv_eq :
      mfderiv (modelWithCornersSelf ℂ E) (modelWithCornersSelf ℂ E) c_p.symm (c_p x) =
        (mfderiv (modelWithCornersSelf ℂ E) (modelWithCornersSelf ℂ E) c_q.symm (ψ (c_p x))).comp
          (mfderiv (modelWithCornersSelf ℂ E) (modelWithCornersSelf ℂ E) ψ (c_p x)) := by
    rw [hψ_symm_eq.mfderiv_eq]
    refine mfderiv_comp_of_eq (y := ψ (c_p x)) ?_ h_ψ_at rfl
    rw [hψ_at_cpx]
    exact h_cq_symm_at
  -- Now unfold both sides of the goal:
  show ω.toFun (c_p.symm (c_p x))
        ((mfderiv (modelWithCornersSelf ℂ E) (modelWithCornersSelf ℂ E) c_p.symm (c_p x)) v) =
      ω.toFun (c_q.symm (c_q x))
        ((mfderiv (modelWithCornersSelf ℂ E) (modelWithCornersSelf ℂ E) c_q.symm (c_q x))
          ((mfderiv (modelWithCornersSelf ℂ E) (modelWithCornersSelf ℂ E) ψ (c_p x)) v))
  rw [c_p.left_inv hp, c_q.left_inv hq]
  congr 1
  rw [h_mfderiv_eq, hψ_at_cpx]
  rfl

end JacobianChallenge.Periods
