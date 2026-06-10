import Jacobian.HolomorphicForms.OnePointCxIsManifold

/-!
# Stage marked topological control data (Perron engine A1)

Blueprint node: `lem:stage-marked-topological-control-data`
(tex §14 Perron engine skeleton, subtree A1 of
`docs/perron-engine-phase1.md`).

The Perron engine uses the input homeomorphism `e : X ≃ₜ OnePoint ℂ` only to
choose **topological control data**: the two marked source points
corresponding to `0` and `∞`, a base normalization point away from them, and
separated chart neighborhoods around all three points.  This file packages
that data (`GenusZeroStageMarkedData`) and provides it from any such
homeomorphism on a `T2Space` (`genusZeroStageMarkedData_nonempty`).

Nothing here asserts that `e` is holomorphic; this is bookkeeping for the
later analytic stage construction (exhaustion domains, dipole boundary data),
which consumes these fields.
-/

namespace JacobianChallenge.HolomorphicForms

/--
Marked topological control data for the Perron stage construction on a
genus-zero surface presented by a homeomorphism `e : X ≃ₜ OnePoint ℂ`:

* `P0`, `Pinf` — the marked source points corresponding to `0` and `∞`;
* `base` — a normalization point away from both;
* `U0`, `Uinf`, `Ubase` — pairwise disjoint open neighborhoods of the three
  points, each contained in the source of that point's preferred chart.

Purely topological: no holomorphy of `e` is recorded or implied.
-/
structure GenusZeroStageMarkedData
    (X : Type*) [TopologicalSpace X] [ChartedSpace ℂ X]
    (e : X ≃ₜ OnePoint ℂ) where
  /-- The marked source point corresponding to `0`. -/
  P0 : X
  /-- The marked source point corresponding to `∞`. -/
  Pinf : X
  /-- The base normalization point. -/
  base : X
  /-- `P0` maps to `0`. -/
  e_P0 : e P0 = ((0 : ℂ) : OnePoint ℂ)
  /-- `Pinf` maps to `∞`. -/
  e_Pinf : e Pinf = OnePoint.infty
  /-- The base point avoids the zero-marked point. -/
  base_ne_P0 : base ≠ P0
  /-- The base point avoids the infinity-marked point. -/
  base_ne_Pinf : base ≠ Pinf
  /-- Neighborhood of `P0`. -/
  U0 : Set X
  /-- Neighborhood of `Pinf`. -/
  Uinf : Set X
  /-- Neighborhood of `base`. -/
  Ubase : Set X
  isOpen_U0 : IsOpen U0
  isOpen_Uinf : IsOpen Uinf
  isOpen_Ubase : IsOpen Ubase
  mem_U0 : P0 ∈ U0
  mem_Uinf : Pinf ∈ Uinf
  mem_Ubase : base ∈ Ubase
  /-- The neighborhood of `P0` sits inside `P0`'s chart source. -/
  U0_subset_chart : U0 ⊆ (chartAt ℂ P0).source
  /-- The neighborhood of `Pinf` sits inside `Pinf`'s chart source. -/
  Uinf_subset_chart : Uinf ⊆ (chartAt ℂ Pinf).source
  /-- The neighborhood of `base` sits inside `base`'s chart source. -/
  Ubase_subset_chart : Ubase ⊆ (chartAt ℂ base).source
  disjoint_U0_Uinf : Disjoint U0 Uinf
  disjoint_U0_Ubase : Disjoint U0 Ubase
  disjoint_Uinf_Ubase : Disjoint Uinf Ubase

namespace GenusZeroStageMarkedData

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
variable {e : X ≃ₜ OnePoint ℂ}

/-- The two marked points are distinct: they map to `0` and `∞`. -/
theorem P0_ne_Pinf (d : GenusZeroStageMarkedData X e) : d.P0 ≠ d.Pinf := by
  intro h
  apply OnePoint.coe_ne_infty (0 : ℂ)
  rw [← d.e_P0, ← d.e_Pinf, h]

/-- All three marked points are pairwise distinct. -/
theorem pairwise_ne (d : GenusZeroStageMarkedData X e) :
    d.P0 ≠ d.Pinf ∧ d.base ≠ d.P0 ∧ d.base ≠ d.Pinf :=
  ⟨d.P0_ne_Pinf, d.base_ne_P0, d.base_ne_Pinf⟩

end GenusZeroStageMarkedData

/--
**Provider (blueprint node `lem:stage-marked-topological-control-data`).**
Any homeomorphism `e : X ≃ₜ OnePoint ℂ` on a Hausdorff charted space yields
stage marked topological control data: take `P0 := e.symm 0`,
`Pinf := e.symm ∞`, `base := e.symm 1`, and shrink pairwise `T2` separations
into the three chart sources.
-/
theorem genusZeroStageMarkedData_nonempty
    (X : Type*) [TopologicalSpace X] [T2Space X] [ChartedSpace ℂ X]
    (e : X ≃ₜ OnePoint ℂ) :
    Nonempty (GenusZeroStageMarkedData X e) := by
  set P0 : X := e.symm ((0 : ℂ) : OnePoint ℂ) with hP0
  set Pinf : X := e.symm OnePoint.infty with hPinf
  set base : X := e.symm ((1 : ℂ) : OnePoint ℂ) with hbase
  have h01 : P0 ≠ Pinf := by
    intro h
    exact OnePoint.coe_ne_infty (0 : ℂ) (e.symm.injective h)
  have hb0 : base ≠ P0 := by
    intro h
    exact one_ne_zero (OnePoint.coe_eq_coe.mp (e.symm.injective h))
  have hbinf : base ≠ Pinf := by
    intro h
    exact OnePoint.coe_ne_infty (1 : ℂ) (e.symm.injective h)
  obtain ⟨A, B, hA, hB, hP0A, hPinfB, hAB⟩ := t2_separation h01
  obtain ⟨C, D, hC, hD, hbaseC, hP0D, hCD⟩ := t2_separation hb0
  obtain ⟨E, F, hE, hF, hbaseE, hPinfF, hEF⟩ := t2_separation hbinf
  refine ⟨{
    P0 := P0
    Pinf := Pinf
    base := base
    e_P0 := e.apply_symm_apply _
    e_Pinf := e.apply_symm_apply _
    base_ne_P0 := hb0
    base_ne_Pinf := hbinf
    U0 := A ∩ D ∩ (chartAt ℂ P0).source
    Uinf := B ∩ F ∩ (chartAt ℂ Pinf).source
    Ubase := C ∩ E ∩ (chartAt ℂ base).source
    isOpen_U0 := (hA.inter hD).inter (chartAt ℂ P0).open_source
    isOpen_Uinf := (hB.inter hF).inter (chartAt ℂ Pinf).open_source
    isOpen_Ubase := (hC.inter hE).inter (chartAt ℂ base).open_source
    mem_U0 := ⟨⟨hP0A, hP0D⟩, mem_chart_source ℂ P0⟩
    mem_Uinf := ⟨⟨hPinfB, hPinfF⟩, mem_chart_source ℂ Pinf⟩
    mem_Ubase := ⟨⟨hbaseC, hbaseE⟩, mem_chart_source ℂ base⟩
    U0_subset_chart := Set.inter_subset_right
    Uinf_subset_chart := Set.inter_subset_right
    Ubase_subset_chart := Set.inter_subset_right
    disjoint_U0_Uinf :=
      hAB.mono (fun x hx => hx.1.1) (fun x hx => hx.1.1)
    disjoint_U0_Ubase :=
      hCD.symm.mono (fun x hx => hx.1.2) (fun x hx => hx.1.1)
    disjoint_Uinf_Ubase :=
      hEF.symm.mono (fun x hx => hx.1.2) (fun x hx => hx.1.2) }⟩

end JacobianChallenge.HolomorphicForms
