import Jacobian.HolomorphicForms.FiniteDimensional
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

/-! ### Step (a): Banach structure of uniform-on-compact topology -/

/-- **(a) Topology of uniform convergence on compacts.**
On a compact 1-dimensional complex manifold, the space of holomorphic
1-forms admits a Banach-space structure realising the topology of uniform
convergence on compact sets, built atop the existing `ContMDiffSection`
additive / ℂ-module structure. (On a compact base this is the sup-norm
topology.)

Bottom-up content: a topology on `ContMDiffSection` plus completeness
under uniform convergence. Mathlib v4.28.0 has neither; see
`Jacobian/HolomorphicForms/SectionTopologyRecon.lean` for the on-going
recon of the API surface required (Aristotle packet `b782c387`). -/
theorem holomorphicOneForm_normedSpace_uniformOnCompact
    (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X] :
    Nonempty (HolomorphicOneFormBanachData X) := sorry

/-! ### Step (b): Montel — bounded sequences are relatively compact -/

/-- **(b) Montel's theorem for holomorphic 1-forms.**
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
theorem holomorphicOneForm_montel
    (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (B : HolomorphicOneFormBanachData X) :
    @IsCompact (HolomorphicOneForm ℂ X)
      B.toMetricSpace.toUniformSpace.toTopologicalSpace
      (@Metric.closedBall (HolomorphicOneForm ℂ X)
        B.toMetricSpace.toPseudoMetricSpace 0 1) := sorry

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
      B.toMetricSpace.toUniformSpace.toTopologicalSpace := sorry

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
