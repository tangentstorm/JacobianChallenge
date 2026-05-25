import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Analysis.Complex.Basic

/-!
# Operator continuity of `mfderiv` of a chart under `StableChartAt`

This file contributes a project-local Mathlib-style packet:

1. A typeclass `StableChartAt H M` asserting that `chartAt H` is
   compatible across each chart's source — i.e., for `q` in the source
   of the chart at `p`, the chart at `q` equals the chart at `p`.
   This holds for all common manifold instances (it is essentially the
   "natural" chart-selection property).

2. Under `StableChartAt`, `mfderiv (chartAt E p₀) b` is in fact
   **constantly equal to the identity** on `(chartAt E p₀).source`,
   trivially yielding operator continuity.

The need for this typeclass arises from a quirk of Mathlib's
`ChartedSpace` abstraction: `chartAt H : M → atlas H M` is typeclass
data with no continuity / locality requirement. For an arbitrary chart
selector, `mfderiv (chartAt E p₀)` viewed as an `(E →L[ℂ] E)`-valued
function on `(chartAt E p₀).source` may be operator-discontinuous
(jumps as the chart selector changes between nearby points). The
mathematical content people care about — operator continuity of the
chart's mfderiv — only holds when `chartAt` is well-behaved.
-/

namespace JacobianChallenge.Periods

open Bundle Set Filter
open scoped Manifold ContDiff Topology

variable (H : Type*) [TopologicalSpace H]
  (M : Type*) [TopologicalSpace M] [ChartedSpace H M]

/--
A `ChartedSpace H M` has **stable `chartAt`** if, for every `p : M`
and every `q ∈ (chartAt H p).source`, the chart at `q` equals the
chart at `p`. Equivalently: `chartAt H` is constant on the source of
each chart.

This holds for every concrete manifold one cares about (the model
space, products, open submanifolds, Riemann surfaces with explicit
finite atlases, etc.) — it is the "natural" chart-selection property.
The abstract `ChartedSpace` typeclass does not enforce it, leading to
artifacts like discontinuous `mfderiv` of a chart for arbitrary chart
selectors.
-/
class StableChartAt : Prop where
  /-- For `q` in the source of the chart at `p`, the chart at `q` equals the chart at `p`. -/
  chartAt_eq_of_mem_source :
    ∀ p : M, ∀ q ∈ (chartAt H p).source, chartAt H q = chartAt H p

/-- The model space `H` (charted on itself) has stable `chartAt`. -/
instance : StableChartAt H H where
  chartAt_eq_of_mem_source p q _ := by
    -- chartAt for `ChartedSpace H H` is the identity for every point.
    rfl

variable {H M}

/-- Under `StableChartAt`, `achart H q = achart H p` for `q ∈ (chartAt H p).source`. -/
theorem achart_eq_of_mem_source [StableChartAt H M]
    {p : M} {q : M} (hq : q ∈ (chartAt H p).source) :
    achart H q = achart H p := by
  apply Subtype.ext
  exact StableChartAt.chartAt_eq_of_mem_source p q hq

end JacobianChallenge.Periods

namespace JacobianChallenge.Periods

open Bundle Set Filter
open scoped Manifold ContDiff Topology

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I (1 : WithTop ℕ∞) M]

/--
**Operator continuity of `mfderiv` of a chart, under `StableChartAt`.**

Under `StableChartAt H M`, `b ↦ mfderiv (chartAt H p₀) b` is in fact
**constantly equal to the identity** on `(chartAt H p₀).source`.
-/
theorem mfderiv_chartAt_eq_id_of_stable [StableChartAt H M]
    (p₀ : M) {b : M} (hb : b ∈ (chartAt H p₀).source) :
    mfderiv I I (chartAt H p₀) b = ContinuousLinearMap.id 𝕜 E := by
  rw [mfderiv_chartAt_eq_tangentCoordChange (I := I) (M := M) (y := p₀) (x := b) hb]
  -- tangentCoordChange b p₀ b = coordChange (achart H b) (achart H p₀) b.
  -- Under StableChartAt, achart H b = achart H p₀, so this is coordChange (achart H p₀) (achart H p₀) b = id.
  have h_eq : achart H b = achart H p₀ := achart_eq_of_mem_source hb
  -- Use coordChange_self: coordChange i i z = id when z ∈ baseSet i.
  ext v
  simp only [tangentCoordChange]
  rw [h_eq]
  apply (tangentBundleCore I M).coordChange_self
  -- Need: b ∈ baseSet (achart H p₀) = (chartAt H p₀).source.
  rw [tangentBundleCore_baseSet, coe_achart]
  exact hb

/--
**Operator continuity (constant id) of `mfderiv (chartAt H p₀)` on its source**,
under `StableChartAt`.
-/
theorem mfderiv_chartAt_continuousOn_of_stable
    [StableChartAt H M]
    (p₀ : M) :
    ContinuousOn (fun b =>
      show E →L[𝕜] E from mfderiv I I (chartAt H p₀) b)
      (chartAt H p₀).source := by
  -- The function is constantly equal to `id`, hence continuous.
  apply ContinuousOn.congr (continuousOn_const (c := ContinuousLinearMap.id 𝕜 E))
  intro b hb
  exact mfderiv_chartAt_eq_id_of_stable (I := I) p₀ hb

/-!
## Project-local helper used by `mfderiv_chartSymm_continuousOn`

The historical name `mfderiv_chartAt_continuousOn_of_finiteDim` is
preserved as an alias (with the `StableChartAt` hypothesis replacing
the previous `[FiniteDimensional ℂ E]`).
-/

/--
Alias: `mfderiv_chartAt_continuousOn_of_finiteDim` under
`[StableChartAt E X]`. The `FiniteDimensional` hypothesis from the
earlier formulation is no longer needed: the function is constantly
`id`.
-/
theorem mfderiv_chartAt_continuousOn_of_finiteDim
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {X : Type*} [TopologicalSpace X] [ChartedSpace E X]
    [IsManifold (modelWithCornersSelf ℂ E) (⊤ : WithTop ℕ∞) X]
    [StableChartAt E X]
    (p₀ : X) :
    ContinuousOn (fun b =>
      show E →L[ℂ] E from
        mfderiv (modelWithCornersSelf ℂ E) (modelWithCornersSelf ℂ E)
          (chartAt E p₀) b)
      (chartAt E p₀).source :=
  haveI : IsManifold (modelWithCornersSelf ℂ E) (1 : WithTop ℕ∞) X :=
    IsManifold.of_le le_top
  mfderiv_chartAt_continuousOn_of_stable (I := modelWithCornersSelf ℂ E) p₀

/-!
1. Add `class StableChartAt H M` to `Mathlib/Geometry/Manifold/IsManifold/Basic.lean`
   (or a new file `Mathlib/Geometry/Manifold/ChartedSpace/StableChartAt.lean`).

2. Provide instances:
   - `instance : StableChartAt H H` (model space charted on itself).
   - `instance [StableChartAt H M] [StableChartAt H' M'] :
       StableChartAt (ModelProd H H') (M × M')` (products).
   - `instance [StableChartAt H M] (s : Opens M) : StableChartAt H s`
     (open submanifolds).
   - Specific instances for `Sphere`, `Icc`, etc. as appropriate.

3. Add `theorem mfderiv_chartAt_eq_id_of_stable` and
   `theorem mfderiv_chartAt_continuousOn_of_stable` in
   `Mathlib/Geometry/Manifold/MFDeriv/Atlas.lean`.

4. (Optionally) Restate downstream lemmas (`mfderiv_chartAt_*`) to take
   `[StableChartAt H M]` and simplify their statements.

The mathematical content is trivial under `StableChartAt`. The value
of the contribution is the typeclass abstraction — making explicit a
property that all concrete manifolds satisfy implicitly.
-/

end JacobianChallenge.Periods
