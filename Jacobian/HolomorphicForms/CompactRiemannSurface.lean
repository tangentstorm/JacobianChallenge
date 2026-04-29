import Jacobian.HolomorphicForms.FiniteDimensional
import Jacobian.HolomorphicForms.SectionMetric
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Finite-dimensionality on a compact connected Riemann surface

The classical result that the space of holomorphic 1-forms on a compact
connected Riemann surface is finite-dimensional. This module is the named
obligation pointed to by the top-down refinement of `Solution.genus`.

## Refinement strategy (Aristotle survey 72ac3a75 / `73f2a96`)

The classical argument is the analytic Riesz / Montel route:

1. **Topology of uniform convergence on compacts.** Equip the section
   space `HolomorphicOneForm ℂ X` with a Banach-space structure realising
   the topology of uniform convergence on compact sets (on a compact
   base, this is just the sup-norm topology).
2. **Montel for holomorphic sections.** A uniformly bounded family of
   holomorphic 1-forms has a uniformly convergent subsequence;
   equivalently, the closed unit ball of that Banach space is compact.
3. **Riesz finite-dimensionality.** A locally compact normed `ℂ`-vector
   space is finite-dimensional (`FiniteDimensional.of_locallyCompactSpace`).

This module encodes (1)–(3) as three named theorem-`sorry` obligations,
and discharges `compactRiemannSurface_finiteDimensionalHolomorphicOneForms`
by assembly: it extracts the data from (1), uses (2)/(3') to derive local
compactness, then closes with Riesz.

The three obligations are independently Aristotle-shaped:

* (a) `holomorphicOneForm_normedSpace_uniformOnCompact` — Banach-space
  data on `HolomorphicOneForm ℂ X` constructed *atop the existing*
  `ContMDiffSection`-derived `AddCommGroup` and `Module ℂ`. Pure
  typeclass-data construction (Mathlib needs a topology on
  `ContMDiffSection`; tracked separately via packet `b782c387`).
* (b) `holomorphicOneForm_montel` — given any such Banach data, the
  closed unit ball is compact (chartwise Cauchy estimates plus
  Arzelà–Ascoli on the compact base).
* (c) `holomorphicOneForm_locallyCompact_of_compactRiemannSurface` —
  combining (a) and (b), the space is locally compact as a topological
  space; this is the direct precondition of
  `FiniteDimensional.of_locallyCompactSpace`.
-/

namespace JacobianChallenge.HolomorphicForms

open scoped Manifold

/-- Bundle of typeclass data witnessing a Banach-space structure on
`HolomorphicOneForm ℂ X` whose topology is the topology of uniform
convergence on compact sets, **built atop the existing
`ContMDiffSection`-derived `AddCommGroup` and `Module ℂ` instances**.

Carrying only the *extra* data (`Norm`, `MetricSpace`, the bridging
axioms, completeness) ensures that when the assembly `letI`-binds the
resulting `NormedAddCommGroup` and `NormedSpace ℂ`, their `toAddCommGroup`
/ `toModule` projections are *definitionally* the existing instances —
no propositional transport needed when feeding the result back to
`FiniteDimensionalHolomorphicOneForms`.

Used as a packed return value for the "step (a)" obligation. -/
structure HolomorphicOneFormBanachData
    (X : Type*) [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X] where
  /-- The norm function on the section space. -/
  toNorm : Norm (HolomorphicOneForm ℂ X)
  /-- The metric-space structure realising the uniform-on-compacts
  topology. -/
  toMetricSpace : MetricSpace (HolomorphicOneForm ℂ X)
  /-- The metric is induced by the norm via the existing additive
  structure. -/
  dist_eq : ∀ x y : HolomorphicOneForm ℂ X,
    @dist _ toMetricSpace.toDist x y = toNorm.norm (x - y)
  /-- The norm satisfies the `NormedSpace` scalar bound over the existing
  `Module ℂ` structure. -/
  norm_smul_le : ∀ (c : ℂ) (x : HolomorphicOneForm ℂ X),
    toNorm.norm (c • x) ≤ ‖c‖ * toNorm.norm x
  /-- The chosen norm makes the section space a Banach space (complete
  in the metric-induced uniformity). -/
  complete :
    @CompleteSpace (HolomorphicOneForm ℂ X)
      toMetricSpace.toUniformSpace
  /-- Pointwise upper bound: the fiber norm of `σ.1 x` is at most
  the global norm of `σ`.  This connects the abstract norm to
  pointwise section evaluation; without it, an arbitrary Banach
  norm need not make the closed unit ball compact (so
  `holomorphicOneForm_montel` is not provable from
  `toNorm`/`toMetricSpace`/`complete` alone).

  Recorded as Blocker 5 in `plan.md` Phase 2; surfaced by Aristotle
  Montel survey `5dfd5106`.  No constructor breaks adding this field
  because `holomorphicOneForm_normedSpace_uniformOnCompact` is itself
  still a sorry — the eventual sup-norm construction satisfies this
  bound trivially. -/
  norm_le : ∀ (σ : HolomorphicOneForm ℂ X) (x : X),
    ‖σ.1 x‖ ≤ toNorm.norm σ

namespace HolomorphicOneFormBanachData

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
  (B : HolomorphicOneFormBanachData X)

/-- Recover the full `NormedAddCommGroup` from the bundle, sharing the
existing `AddCommGroup` instance by construction. Marked `abbrev` so
that `letI`-binding unfolds and exposes `toAddCommGroup =
ContMDiffSection.instAddCommGroup` definitionally. -/
abbrev toNormedAddCommGroup : NormedAddCommGroup (HolomorphicOneForm ℂ X) where
  norm := B.toNorm.norm
  toAddCommGroup := ContMDiffSection.instAddCommGroup
  toMetricSpace := B.toMetricSpace
  dist_eq := B.dist_eq

/-- Recover the full `NormedSpace ℂ` from the bundle, sharing the
existing `Module ℂ` instance by construction. Marked `abbrev` so that
`letI`-binding unfolds and exposes `toModule =
ContMDiffSection.instModule` definitionally. -/
noncomputable abbrev toNormedSpace :
    letI := B.toNormedAddCommGroup
    NormedSpace ℂ (HolomorphicOneForm ℂ X) :=
  letI := B.toNormedAddCommGroup
  { toModule := ContMDiffSection.instModule
    norm_smul_le := B.norm_smul_le }

end HolomorphicOneFormBanachData

/-! ### Prerequisites for Step (a) — TOPDOWN split (integrated from Aristotle 58eb31f0)

Step 5 of the 5-step Banach-data plan in
`SectionTopologyConstructionRecon.lean` is now sorry-free *assembly*;
the genuine sorries are concentrated in two named prerequisites:

1. `holomorphicOneForm_fiberNorm_continuous` — fiberwise norm
   continuity (genuine analysis; for `E = ℂ` reduces to continuity of
   `x ↦ |(σ x) 1|` via `ℂ →L[ℂ] ℂ ≃ₗᵢ[ℂ] ℂ`).
2. `holomorphicOneForm_supNorm_completeSpace` — completeness in the
   sup-norm metric (Step 4, awaiting `SectionComplete.lean` /
   in-flight `8585f085`).

Net: 1 monolithic sorry on `_normedSpace_uniformOnCompact` is replaced
by 2 named sub-obligations + a sorry-free assembly. -/

section SupNormAssembly

open SectionFiberNorm SectionSupNorm SectionMetric

/-- **Prerequisite 1 (sorry).** Fiberwise norm of a holomorphic 1-form is
continuous.

For the `E = ℂ` specialisation the fibers `CotangentSpace ℂ X x` are
`ℂ →L[ℂ] ℂ ≃ₗᵢ[ℂ] ℂ`, so `‖σ x‖ = |(σ x) 1|`. Since `σ` is smooth
(hence continuous into the total space) and evaluation at `1` is a
continuous linear map, `x ↦ |(σ x) 1|` is continuous. -/
theorem holomorphicOneForm_fiberNorm_continuous
    (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (σ : HolomorphicOneForm ℂ X) :
    Continuous (ContMDiffSection.fiberNorm σ) := by sorry

/-- Package the fiberwise-norm-continuity into the `hcompat` form
used by `SectionSupNorm` and `SectionMetric`. -/
theorem holomorphicOneForm_hcompat
    (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X] :
    ∀ (σ : HolomorphicOneForm ℂ X),
      Continuous (ContMDiffSection.fiberNorm σ) :=
  holomorphicOneForm_fiberNorm_continuous X

/-- The `MetricSpace` on `HolomorphicOneForm ℂ X` induced by the
sup-norm distance `dist σ τ = ⨆ x, ‖(σ - τ) x‖`. Constructed from
the individual axioms proved in `SectionMetric.lean`. -/
noncomputable def holomorphicOneForm_metricSpace
    (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X] :
    MetricSpace (HolomorphicOneForm ℂ X) :=
  let hc := holomorphicOneForm_hcompat X
  { dist := SectionMetric.dist
    dist_self := SectionMetric.dist_self
    dist_comm := SectionMetric.dist_comm hc
    dist_triangle := SectionMetric.dist_triangle hc
    eq_of_dist_eq_zero := fun h => by
      by_cases hne : Nonempty X
      · exact SectionMetric.eq_of_dist_eq_zero hc h
      · rw [not_nonempty_iff] at hne
        exact ContMDiffSection.ext fun x => (hne.false x).elim
    toUniformSpace := UniformSpace.ofDist SectionMetric.dist
      SectionMetric.dist_self (SectionMetric.dist_comm hc)
      (SectionMetric.dist_triangle hc)
    toBornology := Bornology.ofDist SectionMetric.dist
      (SectionMetric.dist_comm hc) (SectionMetric.dist_triangle hc) }

/-- **Prerequisite 2 (sorry — awaiting `SectionComplete.lean` / `8585f085`).**
Completeness of the sup-norm metric on `HolomorphicOneForm ℂ X`.
Wire `SectionComplete.holomorphicOneForm_supNorm_completeSpace` here
when `8585f085` lands. -/
theorem holomorphicOneForm_supNorm_completeSpace
    (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X] :
    @CompleteSpace (HolomorphicOneForm ℂ X)
      (holomorphicOneForm_metricSpace X).toUniformSpace := by sorry

end SupNormAssembly

/-! ### Step (a): Banach structure of uniform-on-compact topology -/

/-- **(a) Topology of uniform convergence on compacts.**
On a compact 1-dimensional complex manifold, the space of holomorphic
1-forms admits a Banach-space structure realising the topology of uniform
convergence on compact sets, built atop the existing `ContMDiffSection`
additive / ℂ-module structure. (On a compact base this is the sup-norm
topology.)

**Step 5 assembly** (sorry-free): packages Steps 1–4 into the
`HolomorphicOneFormBanachData` structure using `supNorm`,
`holomorphicOneForm_metricSpace`, the Step 2 / Step 3 axioms, and
the two prerequisite sorries above. -/
theorem holomorphicOneForm_normedSpace_uniformOnCompact
    (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X] :
    Nonempty (HolomorphicOneFormBanachData X) :=
  let hc := holomorphicOneForm_hcompat X
  ⟨{ toNorm := ⟨SectionSupNorm.supNorm⟩
     toMetricSpace := holomorphicOneForm_metricSpace X
     dist_eq := fun _ _ => rfl
     norm_smul_le := SectionSupNorm.supNorm_smul_le hc
     complete := holomorphicOneForm_supNorm_completeSpace X
     norm_le := fun σ x =>
       le_ciSup (SectionSupNorm.bddAbove_range_norm hc σ) x }⟩

/-! ### Step (b): Montel — bounded sequences are relatively compact -/

/-! **(b) Montel's theorem for holomorphic 1-forms.**
For any Banach realisation of `HolomorphicOneForm ℂ X` whose topology is
uniform convergence on compact sets, the closed unit ball is compact.
Equivalently (in a metric space): every uniformly bounded sequence of
holomorphic 1-forms has a uniformly convergent subsequence.

Bottom-up content: chartwise Cauchy estimates on the disc give an
equicontinuity bound, then Arzelà–Ascoli on the compact base extracts
a convergent subsequence; closedness of holomorphicity under uniform
limits keeps the limit in `HolomorphicOneForm`.

### Blocker analysis for `holomorphicOneForm_montel`

**Goal.** Given `B : HolomorphicOneFormBanachData X` carrying a
Banach-space structure on `HolomorphicOneForm ℂ X`, show that the
closed unit ball `Metric.closedBall (0 : HolomorphicOneForm ℂ X) 1`
is compact in `B`'s metric topology. This is the analytic core of
the Montel-then-Riesz route to finite-dimensionality of `H⁰(X, Ω¹)`.

#### Step-by-step mathematical proof outline

1. **Finite chart cover.** `X` is compact, so extract a finite atlas
   `{(Uᵢ, φᵢ)}_{i=1}^{N}` where each `Uᵢ` is precompact and each
   chart `φᵢ : Uᵢ → ℂ` maps onto an open disc `D(cᵢ, Rᵢ)`. Choose
   a slightly smaller disc `D(cᵢ, rᵢ)` (with `rᵢ < Rᵢ`) whose
   preimage still covers `X`.

2. **Chartwise representation.** A holomorphic 1-form `σ` pulls back
   on chart `(Uᵢ, φᵢ)` to `fᵢ(z) dz` where `fᵢ : D(cᵢ, Rᵢ) → ℂ`
   is holomorphic. The norm bound `‖σ‖_B ≤ 1` implies a pointwise
   bound `|fᵢ(z)| ≤ Mᵢ` on the full disc `D(cᵢ, Rᵢ)` for some
   constant `Mᵢ` depending on `B` and the chart.

3. **Cauchy estimates ⇒ equicontinuity.** On the smaller disc
   `D(cᵢ, rᵢ)`, the Cauchy integral formula for the derivative gives
   `|fᵢ'(z)| ≤ Mᵢ / (Rᵢ - rᵢ)` for all `z ∈ D(cᵢ, rᵢ)`. This
   makes the family `{fᵢ : σ ∈ closedBall 0 1}` Lipschitz (hence
   equicontinuous) on `D(cᵢ, rᵢ)` with a *uniform* Lipschitz
   constant independent of `σ`.

4. **Arzelà–Ascoli on each chart.** The family is equicontinuous and
   pointwise bounded on the compact set `closedBall cᵢ rᵢ`, so
   Arzelà–Ascoli extracts a uniformly convergent subsequence on
   `closedBall cᵢ rᵢ`.

5. **Diagonal argument across charts.** There are finitely many
   charts (`N`). Starting from any sequence in `closedBall 0 1`,
   apply step 4 on chart `U₁` to get a subsequence, then on `U₂` to
   get a sub-subsequence, etc. After `N` extractions the final
   subsequence converges uniformly on every chart, hence uniformly on
   all of `X` (the `Uᵢ` cover `X`).

6. **Limit stays holomorphic.** Uniform limits of holomorphic
   functions are holomorphic (Weierstrass), so the limit is again a
   holomorphic 1-form.

7. **Sequential compactness ⇒ compactness.** In a metric space (which
   `B.toMetricSpace` provides), sequential compactness and compactness
   coincide. Combined with the closed-ball being closed, this yields
   `IsCompact (closedBall 0 1)`.

#### Mathlib lemma status (v4.28.0)

| Concept needed | Mathlib name / status | Notes |
|---|---|---|
| Compact space admits finite open subcover | `IsCompact.elim_finite_subcover` | ✅ Available. Gives the finite chart extraction (step 1). |
| `CompactSpace X ↔ isCompact_univ` | `isCompact_univ` | ✅ Available. |
| Cauchy integral formula on a disc | `DiffContOnCl.circleIntegral_sub_inv_smul` | ✅ Available. Yields `f(w) = (2πi)⁻¹ ∮ f(z)/(z-w) dz` for `f` differentiable on `closedBall c R`, `w ∈ ball c R`. |
| Norm bound on circle integral | `circleIntegral.norm_integral_le_of_norm_le_const` | ✅ Available. `‖∮ f‖ ≤ 2π R C` when `‖f‖ ≤ C` on `sphere c R`. |
| Differentiable on disc has power series | `DiffContOnCl.hasFPowerSeriesOnBall` | ✅ Available. Converts differentiability to `HasFPowerSeriesOnBall` using `cauchyPowerSeries`. |
| Cauchy estimates on iterated derivatives | **DOES NOT EXIST** directly | Mathlib has `cauchyPowerSeries_apply` for coefficient representation, but no ready-made `‖f'(z)‖ ≤ M/r` Cauchy estimate for the *first* derivative on a smaller disc. Must be composed from `circleIntegral_sub_inv_smul` + `norm_integral_le_of_norm_le_const` + algebra. |
| Montel's theorem for holomorphic functions on a domain in ℂ | **DOES NOT EXIST** | No `MontelSpace` instance for spaces of holomorphic functions. `MontelSpace` is a bare class definition with no instances at all in Mathlib v4.28.0. |
| Normal families / locally uniformly bounded ⇒ relatively compact | **DOES NOT EXIST** | No Lean formalisation of the normal-families theorem for holomorphic functions. |
| Arzelà–Ascoli (compact closure from equicontinuity) | `ArzelaAscoli.isCompact_closure_of_isClosedEmbedding` | ✅ Available. Given `(∀ K ∈ 𝔖, IsCompact K)`, a closed embedding into `UniformOnFun`, equicontinuity on each `K`, and pointwise-compact orbits, concludes `IsCompact (closure s)`. Requires the function space topology to be `UniformOnFun`. |
| `Equicontinuous` / `EquicontinuousOn` | `Equicontinuous`, `EquicontinuousOn` | ✅ Available as definitions plus basic API (composition, monotonicity, continuity). |
| Lipschitz ⇒ equicontinuous | **No direct `LipschitzOnWith.equicontinuousOn`** | Must be composed manually: `LipschitzOnWith` gives `dist (f x) (f y) ≤ K * dist x y`, which is easily wrapped into `EquicontinuousOn`. |
| Uniform limit of holomorphic functions is holomorphic | **DOES NOT EXIST** | No Weierstrass convergence theorem for holomorphic functions in Mathlib. `TendstoUniformlyOn.differentiableOn` does not exist. The project would need to prove this from `HasFPowerSeriesOnBall` + uniform convergence of power series. |
| Sequential compactness ↔ compactness in metric spaces | `UniformSpace.isCompact_iff_isSeqCompact` (for `FirstCountableTopology`) | ✅ Available. Metric spaces are first-countable, so `IsSeqCompact ↔ IsCompact`. |
| `Metric.closedBall` is closed | `Metric.isClosed_ball` | ✅ Available. |
| `ContMDiffSection` has `TopologicalSpace` | **DOES NOT EXIST** | Mathlib provides `AddCommGroup` and `Module` on `ContMDiffSection` but no topology. The `B : HolomorphicOneFormBanachData X` parameter fills this gap by carrying a `MetricSpace` instance. |
| `ContMDiffSection` has `NormedAddCommGroup` / `NormedSpace` | **DOES NOT EXIST** | Same gap; filled by `B`. |
| Chartwise evaluation of `ContMDiffSection` | **Very limited** | `ContMDiffSection` has a coercion `σ.1 x` returning a point in the fiber `V x`. There is no API for extracting the chart-coordinate representation `fᵢ : ℂ → ℂ` from a section and no concept of "pullback to a chart". |
| `HolomorphicOneForm ℂ X` definition | Project-internal (`Jacobian/HolomorphicForms/Defs.lean`) | Defined as `ContMDiffSection 𝓘(ℂ) ℂ ⊤ (CotangentBundle ℂ X)` or similar; an abbreviation for smooth sections of the cotangent bundle. |
| `CotangentBundle` / `CotangentSpace` | `Mathlib.Geometry.Manifold.CotangentBundle` (partial) | `CotangentSpace` exists as the dual of `TangentSpace`. `CotangentBundle` exists as a type alias but has limited API — no trivialisation, no bundle charts, no `VectorBundle` instance in the cotangent case. |
| `MontelSpace` class | `MontelSpace` in `Mathlib.Analysis.LocallyConvex.Montel` | ✅ Class exists: `IsClosed s → IsVonNBounded 𝕜 s → IsCompact s`. **No instances** registered in Mathlib v4.28.0 — not even for finite-dimensional spaces. |
| Finite-dimensional ⇒ closed bounded sets compact (Heine-Borel) | `Metric.isCompact_of_isClosed_isBounded` (requires `ProperSpace`) | ✅ Available for `ProperSpace`. Finite-dimensional normed spaces are `ProperSpace` via `FiniteDimensional.properSpace`. But our space is *infinite-dimensional a priori* — this is precisely what we are trying to prove. |
| `FiniteDimensional.of_isCompact_closedBall` | `FiniteDimensional.of_isCompact_closedBall` | ✅ Available. The *converse* direction: compact ball ⇒ finite-dimensional. Used downstream (step c + Riesz), not in this lemma. |

#### Key blockers

**Blocker 1 (deepest): no Montel / normal-families theorem in
Mathlib.**

Mathlib v4.28.0 has no theorem stating that uniformly bounded
holomorphic functions on a domain in ℂ form a relatively compact family.
The `MontelSpace` class exists but has **zero instances**. In particular
there is no:
- `MontelSpace ℂ (ℂ →ᵇ ℂ)` or any function-space instance,
- proof that bounded holomorphic families are equicontinuous,
- normal families theorem for holomorphic maps.

This is the mathematical heart of the argument and must be built from
more primitive ingredients (Cauchy formula + Arzelà–Ascoli).

**Blocker 2: no Cauchy first-derivative estimate lemma.**

The classical `|f'(z)| ≤ M/r` for `|f| ≤ M` on a disc of radius `r`
around `z` is not directly available. The raw ingredients exist:
- `DiffContOnCl.circleIntegral_sub_inv_smul` (Cauchy formula),
- `circleIntegral.norm_integral_le_of_norm_le_const` (integral bound),

but they must be combined with the derivative-via-integral formula
`f'(w) = (2πi)⁻¹ ∮ f(z)/(z-w)² dz` (which also **does not exist** as
a named lemma — one would need to differentiate the Cauchy integral
under the integral sign, or use `DiffContOnCl.hasFPowerSeriesOnBall`
to obtain the derivative from the power series).

**Blocker 3: no Weierstrass convergence theorem.**

The statement "uniform limit of holomorphic functions is holomorphic"
is absent from Mathlib. This is needed (step 6) to show the extracted
convergent subsequence lands in `HolomorphicOneForm` rather than just
in `C(X, CotangentBundle)`. Provable from Morera's theorem (also
absent) or from the power-series representation, but requires
non-trivial work.

**Blocker 4: chartwise section evaluation API.**

`ContMDiffSection` (and therefore `HolomorphicOneForm`) lacks API for
extracting the chart-coordinate representation of a section. Steps 2–4
require converting a global section `σ : HolomorphicOneForm ℂ X`
restricted to a chart domain `Uᵢ` into a holomorphic function
`fᵢ : D(cᵢ, Rᵢ) → ℂ`. This needs:
- `CotangentBundle` trivialisation over charts (partially available
  via `TangentBundle` trivialisations + dualisation, but no direct
  API),
- a lemma that smooth-section restriction to a chart domain composed
  with the trivialisation yields a holomorphic function on the chart
  image.

This is not deep mathematically but involves substantial API plumbing.

**Blocker 5 (structural): `B` is abstract data, not a concrete norm.**

The statement is parameterised by an *arbitrary*
`B : HolomorphicOneFormBanachData X`. The proof needs to relate `B`'s
norm to pointwise evaluation of sections — specifically, `‖σ‖_B ≤ 1`
must imply pointwise bounds on chart representatives. If `B`'s norm
is defined as the sup-norm `‖σ‖ = ⨆ₓ ‖σ(x)‖` (as expected for a
compact base), this implication is immediate. But `B` carries no axiom
relating its norm to pointwise values — `HolomorphicOneFormBanachData`
only records `dist_eq` (dist from norm), `norm_smul_le` (scalar
multiplication bound), and `complete` (Banach).

Consequence: the lemma as stated — for an *arbitrary* `B` — is
**false in general**. An arbitrary Banach-space norm on
`HolomorphicOneForm ℂ X` need not make the closed unit ball compact
(e.g., take any infinite-dimensional-looking norm). The intended
meaning is that the *specific* Banach data produced by
`holomorphicOneForm_normedSpace_uniformOnCompact` satisfies Montel;
but the current signature abstracts over `B`.

This is a *statement-level design issue*, not a Mathlib gap. Two
resolution options:
- **(5a)** Add a field to `HolomorphicOneFormBanachData` axiomatising
  the norm–pointwise relationship, e.g.
  `norm_le_iff : B.toNorm.norm σ ≤ C ↔ ∀ x, ‖σ.1 x‖ ≤ C`.
  Then `holomorphicOneForm_montel` becomes provable from chartwise
  Cauchy + Arzelà–Ascoli.
- **(5b)** Replace `holomorphicOneForm_montel` with a version that
  takes the *specific* `B` produced by step (a), or bundle the Montel
  property into `HolomorphicOneFormBanachData` itself.

#### Recommended resolution path

1. **Fix the statement (Blocker 5).** Add to
   `HolomorphicOneFormBanachData` a field connecting the norm to
   pointwise evaluation:
   ```
   norm_eq_iSup : ∀ σ : HolomorphicOneForm ℂ X,
     toNorm.norm σ = ⨆ (x : X), ‖σ.1 x‖
   ```
   or at minimum a one-sided bound
   `∀ σ x, ‖σ.1 x‖ ≤ toNorm.norm σ`.

2. **Build chartwise Cauchy estimate (Blockers 1–2).** New lemma:
   ```
   theorem cauchy_deriv_bound {R r M : ℝ} (hR : 0 < R) (hr : r < R)
       {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f (Metric.ball c R))
       (hM : ∀ z ∈ Metric.closedBall c R, ‖f z‖ ≤ M) :
       ∀ z ∈ Metric.closedBall c r, ‖deriv f z‖ ≤ M / (R - r)
   ```
   Proved from `DiffContOnCl.circleIntegral_sub_inv_smul`,
   differentiating the Cauchy kernel, and
   `circleIntegral.norm_integral_le_of_norm_le_const`.

3. **Build equicontinuity wrapper.** From step 2, derive:
   ```
   theorem bounded_holomorphic_equicontinuousOn {M : ℝ}
       (hF : ∀ i, DifferentiableOn ℂ (F i) (Metric.ball c R))
       (hM : ∀ i z, z ∈ Metric.closedBall c R → ‖F i z‖ ≤ M) :
       EquicontinuousOn (fun i => F i ∘ Subtype.val)
         (Metric.closedBall c r)   -- for any r < R
   ```

4. **Apply Arzelà–Ascoli (available).** Use
   `ArzelaAscoli.isCompact_closure_of_isClosedEmbedding` with the
   equicontinuity from step 3 and the pointwise compactness (each
   orbit `{fᵢ(z) : i ∈ s}` is bounded in `ℂ` hence precompact).

5. **Build Weierstrass convergence (Blocker 3).** New lemma:
   ```
   theorem DifferentiableOn.tendsto_uniformlyOn_of_differentiableOn
       {F : ℕ → ℂ → ℂ} {f : ℂ → ℂ}
       (hF : ∀ n, DifferentiableOn ℂ (F n) U)
       (hconv : TendstoUniformlyOn F f Filter.atTop U) :
       DifferentiableOn ℂ f U
   ```
   Provable via Morera's theorem (also absent; requires
   `circleIntegral.eq_zero` for the limit ⇒ holomorphic step), or
   via power-series coefficient convergence using
   `DiffContOnCl.hasFPowerSeriesOnBall`.

6. **Diagonal extraction + assembly.** Compose steps 1–5 across
   the finite chart cover, using the finite-intersection diagonal
   argument. This is a standard combinatorial argument that Lean can
   handle via `Finset.induction`.

#### Dependency graph

```text
holomorphicOneForm_montel
├── [Blocker 5] HolomorphicOneFormBanachData.norm_eq_iSup (or norm_le)
│   └── (statement-level fix to HolomorphicOneFormBanachData)
├── [step 1] IsCompact.elim_finite_subcover  ← Mathlib ✅
├── [Blocker 4] chartwise_section_eval
│   ├── CotangentBundle trivialisation API  ← partial in Mathlib
│   └── ContMDiffSection chart-restriction  ← DOES NOT EXIST
├── [Blocker 2] cauchy_deriv_bound
│   ├── DiffContOnCl.circleIntegral_sub_inv_smul  ← Mathlib ✅
│   ├── circleIntegral.norm_integral_le_of_norm_le_const  ← Mathlib ✅
│   └── derivative-via-integral formula  ← must compose
├── [step 3] bounded_holomorphic_equicontinuousOn
│   └── cauchy_deriv_bound + LipschitzOnWith wrapping
├── [step 4] ArzelaAscoli.isCompact_closure_of_isClosedEmbedding  ← Mathlib ✅
├── [Blocker 3] weierstrass_convergence
│   ├── Morera's theorem  ← DOES NOT EXIST
│   └── OR: power-series coefficient convergence
│       └── DiffContOnCl.hasFPowerSeriesOnBall  ← Mathlib ✅
├── [step 6] diagonal extraction (Finset.induction)  ← routine
└── [step 7] isCompact_iff_isSeqCompact  ← Mathlib ✅
```

#### Effort estimate

- **Cauchy derivative estimate** (Blocker 2): ~100–200 lines, moderate.
  Building block is the differentiated Cauchy kernel formula.
- **Equicontinuity wrapper** (step 3): ~50 lines, straightforward
  given Blocker 2.
- **Weierstrass convergence** (Blocker 3): ~150–300 lines, significant.
  Either Morera route or power-series-coefficient route requires
  substantial work.
- **Chartwise section evaluation** (Blocker 4): ~200–400 lines,
  significant API plumbing involving `CotangentBundle` trivialisations.
- **Statement fix** (Blocker 5): ~10 lines, mechanical.
- **Assembly** (steps 1, 4, 6, 7): ~100 lines, routine once
  ingredients are in place.

**Total new infrastructure: ~600–1100 lines across 3–5 new modules.**

#### Conclusion

The sorry is retained. The five blockers above — especially the
absence of Montel / normal-families / Weierstrass convergence and the
chartwise section evaluation API — make discharge infeasible without
substantial bottom-up infrastructure work. The statement itself
(Blocker 5) also needs a minor fix to connect `B`'s abstract norm to
pointwise section values. -/
/-! #### Sub-obligations of `holomorphicOneForm_montel`

The Montel statement is split into two named obligations that
correspond to the mathematical content of the proof:

* `holomorphicOneForm_montel_subseq_tendsto` — every sequence in the
  closed unit ball admits a subsequence converging (in `B`'s metric
  topology) to *some* element of `HolomorphicOneForm ℂ X`.  This is
  the analytic core: chartwise Cauchy estimates ⇒ equicontinuity ⇒
  Arzelà–Ascoli for a uniformly convergent subsequence; Weierstrass
  closure gives the limit's holomorphicity.
* `holomorphicOneForm_montel_norm_le_of_tendsto_of_norm_le` — if a
  sequence of sections with `‖σₙ‖ ≤ 1` converges to `σ` in `B`'s
  topology, then `‖σ‖ ≤ 1`.  (Closed-ball-is-closed wiring on the
  norm-induced metric, fully discharged below.)

`holomorphicOneForm_montel` then assembles these into sequential
compactness of the closed unit ball, and concludes via
`IsSeqCompact.isCompact` (metric ⇒ pseudometrizable ⇒
Bolzano–Weierstrass).
-/

/-- **Subsequence extraction (Montel core).** Every sequence in the
closed unit ball of `B` admits a subsequence converging in `B`'s
metric topology.

This is the analytic heart of Montel.  Discharging it requires:
1. chartwise Cauchy first-derivative estimates on holomorphic 1-forms
   (Blocker 2 of the parent docstring),
2. uniform Lipschitz / equicontinuity on each chart,
3. Arzelà–Ascoli on the compact base (`arzela_ascoli₁` /
   `arzela_ascoli` from
   `Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli`) plus a
   diagonal extraction across the finite chart cover, and
4. Weierstrass closure (uniform limit of holomorphic = holomorphic;
   Blocker 3) to keep the limit inside `HolomorphicOneForm ℂ X`.

The limit `a` is *unconstrained* by this lemma; the norm bound
`‖a‖_B ≤ 1` is established separately by
`holomorphicOneForm_montel_norm_le_of_tendsto_of_norm_le`.

Bottom-up content: this is the substantive Mathlib-gap-laden
lemma.  Discharging it requires the chartwise-section evaluation
API (Blocker 4) and the Cauchy/Weierstrass infrastructure
(Blockers 2–3) listed in the parent docstring.  See
`Jacobian/HolomorphicForms/SectionTopologyConstructionRecon.lean`
for the recon.

##### TOPDOWN refinement (subagent a7b046e5b69cfb1ea)

The parent obligation factors into two strictly smaller pieces:

* `holomorphicOneForm_montel_subseq_isCauchy` — analytic core
  (sorry): given `‖σ n‖ ≤ 1`, extract a strictly monotone `φ` such
  that `σ ∘ φ` is Cauchy in `B`'s metric. Absorbs all five Mathlib-
  gap blockers (Cauchy first-derivative estimate, equicontinuity,
  Arzelà–Ascoli, Weierstrass closure, chartwise eval API).
* `HolomorphicOneFormBanachData.cauchySeq_tendsto` — sorry-free
  Banach-completeness wrapper: `cauchySeq_tendsto_of_complete` with
  `B.complete` supplying the `CompleteSpace`.

The parent below is then a 3-line assembly of these two pieces. -/
theorem holomorphicOneForm_montel_subseq_isCauchy
    (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (B : HolomorphicOneFormBanachData X)
    (σ : ℕ → HolomorphicOneForm ℂ X)
    (_hσ : ∀ n, B.toNorm.norm (σ n) ≤ 1) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      @CauchySeq (HolomorphicOneForm ℂ X) ℕ
        B.toMetricSpace.toUniformSpace _ (σ ∘ φ) := by
  sorry

namespace HolomorphicOneFormBanachData

/-- **Completeness wrapper.** A Cauchy sequence in `B`'s metric
admits a limit, by `B.complete : CompleteSpace _` plus
`cauchySeq_tendsto_of_complete`. Sorry-free. -/
theorem cauchySeq_tendsto
    {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (B : HolomorphicOneFormBanachData X)
    {τ : ℕ → HolomorphicOneForm ℂ X}
    (hτ : @CauchySeq (HolomorphicOneForm ℂ X) ℕ
      B.toMetricSpace.toUniformSpace _ τ) :
    ∃ a : HolomorphicOneForm ℂ X,
      @Filter.Tendsto ℕ (HolomorphicOneForm ℂ X) τ Filter.atTop
        (@nhds (HolomorphicOneForm ℂ X)
          B.toMetricSpace.toUniformSpace.toTopologicalSpace a) := by
  letI : MetricSpace (HolomorphicOneForm ℂ X) := B.toMetricSpace
  haveI : CompleteSpace (HolomorphicOneForm ℂ X) := B.complete
  exact cauchySeq_tendsto_of_complete hτ

end HolomorphicOneFormBanachData

/-- Subsequence extraction (Montel core), public face. Now a 3-line
assembly of `holomorphicOneForm_montel_subseq_isCauchy` and
`HolomorphicOneFormBanachData.cauchySeq_tendsto`. -/
theorem holomorphicOneForm_montel_subseq_tendsto
    (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (B : HolomorphicOneFormBanachData X)
    (σ : ℕ → HolomorphicOneForm ℂ X)
    (hσ : ∀ n, B.toNorm.norm (σ n) ≤ 1) :
    ∃ (a : HolomorphicOneForm ℂ X) (φ : ℕ → ℕ), StrictMono φ ∧
      @Filter.Tendsto ℕ (HolomorphicOneForm ℂ X) (σ ∘ φ) Filter.atTop
        (@nhds (HolomorphicOneForm ℂ X)
          B.toMetricSpace.toUniformSpace.toTopologicalSpace a) := by
  obtain ⟨φ, hφ_mono, hφ_cauchy⟩ :=
    holomorphicOneForm_montel_subseq_isCauchy X B σ hσ
  obtain ⟨a, ha⟩ := B.cauchySeq_tendsto hφ_cauchy
  exact ⟨a, φ, hφ_mono, ha⟩

/-- **Norm bound preserved under metric convergence.** If a sequence of
sections has `B.toNorm.norm (σₙ) ≤ 1` and converges to `a` in `B`'s
metric topology, then `B.toNorm.norm a ≤ 1`.

In any normed space, the closed ball is closed in the norm-induced
metric topology — Mathlib's `Metric.isClosed_closedBall` applied to
`B.toNormedAddCommGroup`.  This obligation is fully discharged below
and is *not* a sorry. -/
theorem holomorphicOneForm_montel_norm_le_of_tendsto_of_norm_le
    (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (B : HolomorphicOneFormBanachData X)
    (σ : ℕ → HolomorphicOneForm ℂ X) (a : HolomorphicOneForm ℂ X)
    (hσ : ∀ n, B.toNorm.norm (σ n) ≤ 1)
    (hlim : @Filter.Tendsto ℕ (HolomorphicOneForm ℂ X) σ Filter.atTop
      (@nhds (HolomorphicOneForm ℂ X)
        B.toMetricSpace.toUniformSpace.toTopologicalSpace a)) :
    B.toNorm.norm a ≤ 1 := by
  letI : NormedAddCommGroup (HolomorphicOneForm ℂ X) := B.toNormedAddCommGroup
  have hball : ∀ n, σ n ∈ Metric.closedBall (0 : HolomorphicOneForm ℂ X) 1 := by
    intro n
    have h := hσ n
    show dist (σ n) (0 : HolomorphicOneForm ℂ X) ≤ 1
    simpa [dist_zero_right] using h
  have hclosed : IsClosed (Metric.closedBall (0 : HolomorphicOneForm ℂ X) 1) :=
    Metric.isClosed_closedBall
  have ha_mem : a ∈ Metric.closedBall (0 : HolomorphicOneForm ℂ X) 1 :=
    hclosed.mem_of_tendsto hlim (Filter.Eventually.of_forall hball)
  have hd : dist a (0 : HolomorphicOneForm ℂ X) ≤ 1 := ha_mem
  simpa [dist_zero_right] using hd

theorem holomorphicOneForm_montel
    (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (B : HolomorphicOneFormBanachData X) :
    @IsCompact (HolomorphicOneForm ℂ X)
      B.toMetricSpace.toUniformSpace.toTopologicalSpace
      (@Metric.closedBall (HolomorphicOneForm ℂ X)
        B.toMetricSpace.toPseudoMetricSpace 0 1) := by
  -- Round of top-down refinement: split this monolithic Montel sorry
  -- into two strictly smaller named obligations
  -- (`holomorphicOneForm_montel_subseq_tendsto` and
  -- `holomorphicOneForm_montel_norm_le_of_tendsto_of_norm_le`).  The
  -- assembly here reduces compactness in `B`'s metric topology to
  -- sequential compactness, then combines the two sub-obligations.
  letI : NormedAddCommGroup (HolomorphicOneForm ℂ X) := B.toNormedAddCommGroup
  refine IsSeqCompact.isCompact ?_
  intro σ hσ
  have hσ_norm : ∀ n, B.toNorm.norm (σ n) ≤ 1 := by
    intro n
    have hd : dist (σ n) (0 : HolomorphicOneForm ℂ X) ≤ 1 := hσ n
    simpa [dist_zero_right] using hd
  obtain ⟨a, φ, hφ_mono, hφ_tendsto⟩ :=
    holomorphicOneForm_montel_subseq_tendsto X B σ hσ_norm
  refine ⟨a, ?_, φ, hφ_mono, hφ_tendsto⟩
  have ha_norm : B.toNorm.norm a ≤ 1 :=
    holomorphicOneForm_montel_norm_le_of_tendsto_of_norm_le X B
      (σ ∘ φ) a (fun n => hσ_norm (φ n)) hφ_tendsto
  show dist a (0 : HolomorphicOneForm ℂ X) ≤ 1
  simpa [dist_zero_right] using ha_norm

/-! ### Step (c): assembly — local compactness from (a) + (b) -/

/-- **(c) Local compactness of the section space.**
Combining the Banach structure from
`holomorphicOneForm_normedSpace_uniformOnCompact` with the Montel
compactness statement `holomorphicOneForm_montel`, the section space is
locally compact. This is the direct hypothesis of Riesz's theorem
(`FiniteDimensional.of_locallyCompactSpace`).

Bottom-up content: in a normed space, compactness of a closed ball of
positive radius around `0` is equivalent to local compactness of the
whole space. The Mathlib lemma
`IsCompact.locallyCompactSpace_of_mem_nhds` (or the direct
`exists_isCompact_closedBall` ↔ `LocallyCompactSpace` route) gives the
bridge. The proof of this obligation should be a short combinator over
`holomorphicOneForm_montel B`. -/
theorem holomorphicOneForm_locallyCompact_of_compactRiemannSurface
    (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (B : HolomorphicOneFormBanachData X) :
    @LocallyCompactSpace (HolomorphicOneForm ℂ X)
      B.toMetricSpace.toUniformSpace.toTopologicalSpace := by
  letI : NormedAddCommGroup (HolomorphicOneForm ℂ X) := B.toNormedAddCommGroup
  letI : NormedSpace ℂ (HolomorphicOneForm ℂ X) := B.toNormedSpace
  have hCompact := holomorphicOneForm_montel X B
  have : WeaklyLocallyCompactSpace (HolomorphicOneForm ℂ X) := by
    constructor
    intro x
    refine ⟨Metric.closedBall x 1, ?_, Metric.closedBall_mem_nhds x one_pos⟩
    have heq : Metric.closedBall x 1 = (· + x) '' Metric.closedBall (0 : HolomorphicOneForm ℂ X) 1 := by
      ext y
      simp [Metric.mem_closedBall, dist_comm]
    rw [heq]
    exact hCompact.image (continuous_add_right x)
  exact WeaklyLocallyCompactSpace.locallyCompactSpace

/-! ### Final assembly: Riesz finite-dimensionality -/

/-- On a compact connected Riemann surface (a compact connected
1-dimensional complex manifold), the space of holomorphic 1-forms is
finite-dimensional.

Top-down obligation: pointed to by `Jacobian/Solution.lean` for the
`genus` declaration.

Assembly:
1. Extract a Banach realisation `B` from
   `holomorphicOneForm_normedSpace_uniformOnCompact`.
2. `letI`-bind the `NormedAddCommGroup` and `NormedSpace ℂ` from `B`
   (their `toAddCommGroup` / `toModule` projections are by construction
   the existing `ContMDiffSection`-derived instances).
3. Obtain `LocallyCompactSpace` for `B`'s topology from
   `holomorphicOneForm_locallyCompact_of_compactRiemannSurface` (whose
   bottom-up proof in turn uses `holomorphicOneForm_montel`).
4. Apply Riesz (`FiniteDimensional.of_locallyCompactSpace ℂ`) to
   conclude `FiniteDimensional ℂ (HolomorphicOneForm ℂ X)`, which is
   exactly the field `Module.Finite ℂ (HolomorphicOneForm ℂ X)` of
   `FiniteDimensionalHolomorphicOneForms`. -/
noncomputable instance compactRiemannSurface_finiteDimensionalHolomorphicOneForms
    (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X] :
    FiniteDimensionalHolomorphicOneForms ℂ X := by
  obtain ⟨B⟩ := holomorphicOneForm_normedSpace_uniformOnCompact X
  letI : NormedAddCommGroup (HolomorphicOneForm ℂ X) := B.toNormedAddCommGroup
  letI : NormedSpace ℂ (HolomorphicOneForm ℂ X) := B.toNormedSpace
  letI : LocallyCompactSpace (HolomorphicOneForm ℂ X) :=
    holomorphicOneForm_locallyCompact_of_compactRiemannSurface X B
  refine ⟨?_⟩
  have : FiniteDimensional ℂ (HolomorphicOneForm ℂ X) :=
    FiniteDimensional.of_locallyCompactSpace ℂ
  infer_instance

end JacobianChallenge.HolomorphicForms
