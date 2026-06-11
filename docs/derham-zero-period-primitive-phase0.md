# Phase 0: pricing the zero-period primitive-existence provider (#242)

> Tracking #242 (`deRhamComparisonMap1_zero_period_primitiveExists_provider`,
> `Jacobian/HolomorphicForms/DeRhamComparisonMap.lean:1099`, sorry at `:1108`).
> Prose-only pricing of the classical path-integration argument: a closed
> 1-form whose periods all vanish admits a global primitive. Companion to
> jc7's `docs/perron-b4-conjugate-phase0.md` (period-killing for harmonic
> conjugates on the Perron side; landed upstream at `68bb3afc` and read in
> full — the shared-machinery comparison is §5). Every declaration cited
> below was verified in this checkout (project tree and
> `.lake/packages/mathlib/`, pin v4.31.0-rc1), including after rebasing
> onto `fc68ca87` (the `b1b8e6a1` stub-deletion pass did not move any
> line cited here).

## Executive Conclusion

**The provider, as stated on the current substrate, is not provable — by
design.** `deRhamComparisonMap1` is not an integration map: it is the
projection onto a *free* period payload (`DeRhamComparisonMap.lean:49`,
`toFun ω := (ω : SmoothDiffForm 1 X).2`), and `exteriorDerivative := 0`
(`SmoothDifferentialForm.lean:68-73`). Unwinding (§1): the hypothesis
`hω` kills only the payload component; the conclusion forces the *whole*
form — including its genuinely-real `HolomorphicOneForm` coefficient pair —
to be zero. The provider is therefore equivalent to "every smooth 1-form
with zero stored payload has zero coefficient part," which is classically
false (a complex torus with `ω = (dz, 0-payload)` is a counter-model). The
provider's own docstring concedes this (`DeRhamComparisonMap.lean:1093-1098`:
"this provider is true only when `ω = 0` … becomes true once
`exteriorDerivative` is given real chartwise content").

**So #242 is a substrate debt, not a proof debt.** No amount of
path-integration argument discharges the sorry as written; conversely, any
Lean closure of the sorry on the current substrate would be a red flag, not
progress. The honest price has two stages:

- **Stage S (prerequisite, frontier-moving, owner-gated):** give
  `exteriorDerivative` real content and make "period" mean an actual
  integral. The cheapest honest design (the *discrepancy differential*, §3)
  keeps the product carrier and is medium-sized as a statement change, but
  it consumes the one genuinely hard analytic object: a chain-level
  integration of 1-forms with the Stokes kills-boundary property. Today
  every avatar of that object in the tree is a zero-map or `Nonempty Unit`
  stub (§2b) — including `periodPairing` itself
  (`PeriodFunctional.lean:109-112`, `let I := 0`).
- **Stage A (the classical argument, multi-commit but standard):** basepoint
  path integral, well-definedness from vanishing periods, chart-local
  smoothness, `dθ = ω`. The chart-local analytic core is **already in the
  pinned Mathlib**: `Mathlib/MeasureTheory/Integral/CurveIntegral/Poincare.lean`
  (convex Poincaré lemma + C²-homotopy invariance of `curveIntegral`) — a
  substantial asset the repo's `Periods` layer predates.

**Worst sub-step, both stages:** the chain-level integration + Stokes
kills-boundary leaf (Blueprint Sec03 sub-leaves A.2/C). jc7's landed B4
pricing rejected its own integral route over exactly the Mathlib gaps
priced here and dodged into a covering-space engine — a dodge **not
available to #242**, whose statement *is* about integration periods (§5).
The two documents corroborate each other's Mathlib negatives and share the
constant-difference / germ-covering machinery as Stage A infrastructure;
the Stokes engine is #242's alone.

## 1. What the statement actually says (checkout-verified)

The target (`DeRhamComparisonMap.lean:1099-1108`):

```lean
theorem deRhamComparisonMap1_zero_period_primitiveExists_provider
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [JacobianChallenge.Periods.StableChartAt ℂ X]
    (ω : ClosedForm 1 X) (hω : deRhamComparisonMap1 X ω = 0) :
    ∃ θ : SmoothDiffForm 0 X,
      exteriorDerivative 0 X θ = (ω : SmoothDiffForm 1 X) := by sorry
```

The definition chain, fully unwound:

- `SmoothDiffForm n X = SmoothDiffFormCoeff n X × SmoothDiffFormPeriodPayload n X`
  (`SmoothDifferentialForm.lean:47-56`), where
  - `SmoothDiffFormCoeff n X = Fin n.succ → HolomorphicOneForm ℂ X` (`:36-39`),
    and `HolomorphicOneForm ℂ X` is **real**: `ContMDiff`-analytic sections of
    the cotangent bundle (`HolomorphicForms/Defs.lean:23-30`);
  - `SmoothDiffFormPeriodPayload n X = IntegralOneCycle X →ₗ[ℤ] ℂ` (`:31-33`)
    — a **free** component, *not* constrained to be the integrals of the
    coefficient part;
  - `IntegralOneCycle X` is **real**: degree-1 singular homology `H₁(X, ℤ)`
    via Mathlib's `singularHomologyFunctor` (`Periods/IntegralOneCycle.lean:31-34`).
- `exteriorDerivative n X := 0` (`SmoothDifferentialForm.lean:68-73`); hence
  `ClosedForm n X = ker 0 = ⊤` (`:84-89`, every form is closed) and
  `ExactForm n X = range 0 = ⊥` (`:92-97`, only `0` is exact).
- `deRhamComparisonMap1 X ω = (ω : SmoothDiffForm 1 X).2`
  (`DeRhamComparisonMap.lean:43-55`) — projection onto the stored payload.
  **No integration occurs anywhere in the hypothesis.**

So, writing `ω = ((α₀, α₁), φ)`:

- `hω` says exactly `φ = 0` — the *stored functional* on `H₁(X, ℤ)` is zero.
  It says nothing about `α₀, α₁`.
- The goal says `∃ θ, 0 = ω`, i.e. `α₀ = α₁ = 0 ∧ φ = 0`.

The gap between the two is the real `ContMDiff` coefficient pair, which the
hypothesis does not touch. The provider is thus equivalent to: *for every
`X` carrying these instances, every holomorphic-coefficient pair is zero* —
false in any classical model containing a complex torus with its translation
atlas (which satisfies `StableChartAt`, `TrivializationContinuousLinearMapAt.lean:52`,
since its transitions are translations). It is unprovable short of
inconsistency; the in-file docstring (`:1093-1098`) already says so.

Two sound sorry-free pieces survive unconditionally and stay the consumers
of any future honest proof:

- `deRhamComparisonMap1_zero_period_primitiveExists_exact_assembly`
  (`DeRhamComparisonMap.lean:1115-1125`): a primitive *is* a witness of
  exactness (`ExactForm 0 X = range (exteriorDerivative 0 X)`), independent
  of what `d` is.
- `DeRhamComparisonMap1Spec.primitive_exists` (`:82-95`) names the provider
  shape as a record field, so downstream consumption is already decoupled.

## 2. Substrate survey

### 2a. Real machinery (green, reusable as-is)

- **Chart-level path integrals.** `pathIntegralInChart`
  (`Periods/PathIntegralChart.lean:27-35`) is
  `curveIntegral (chartedForm c ω) γ` over Mathlib's `curveIntegral`
  (`Mathlib/MeasureTheory/Integral/CurveIntegral/Basic.lean:123`).
  Multi-chart version `pathIntegralViaCoverWith`
  (`Periods/PathIntegralViaCover.lean:41-65`) sums
  `pathIntegralViaChartCorrect` over an explicit `Fin n`-partition with a
  chart-cover witness. The `Periods/` directory has 225 files, 215
  sorry-free; the `PathIntegralViaChartCorrect*` algebra family
  (concatenation additivity, `symm`, `neg`, scalar action) and the
  reparametrisation identity `curveIntegral_subpath_of_le`
  (`Periods/CurveIntegralSubpath.lean:102-188`) are proved.
- **Homotopy machinery.** The prism chain homotopy is fully proved
  (`Periods/PrismChainHomotopy.lean`, sorry-free), with
  `singularH1_iso_of_homotopyEquiv_via_prism`
  (`Periods/SingularH1Homotopy.lean:221-227`).
- **Cycle-class plumbing.** `singularH1ClassOfCycle` and
  `singularH1ClassOfCycle_eq_of_boundary` (`Periods/Hurewicz.lean:522, :536`)
  map chain-level cycles to `H₁` classes; the path↔simplex bridge
  `simplex_to_path` exists (`Blueprint/Sec03/PeriodHomologyInvariance.lean:123`).
  (`Hurewicz.lean`'s 4 sorries concern the cellular–singular comparison;
  this argument does not need them.)
- **Green's theorem leaves.** `stokes_local_euclidean_P` / `_Q`
  (`Blueprint/Sec03/StokesOnRSWithBoundary.lean:128, :173`) are real, proved
  FTC slices of Green's theorem on a rectangle, with the Fubini-swap
  lemmas (`:217, :243`).

### 2b. The zero-stub period circle (consumable as hypotheses only)

Every place where "period of a form" should be an integral is currently a
zero-map or vacuous stub. The Phase 0 anti-cheat point: **none of these may
be cited as proved facts** in any Stage A execution.

- `deRhamComparisonMap1` — payload projection, §1.
- `periodPairing` / `periodPairingComplex`
  (`Periods/PeriodFunctional.lean:98-149`) — homology descent of the chain
  integration `let I := 0` (`:109-112`). Sorry-free but integrates nothing.
  `period_homology_invariance` (`:168-175`) is `congrArg` over the `H₁`
  typing, as its docstring honestly states.
- `chain_integration_kills_boundary`
  (`Blueprint/Sec03/PeriodHomologyInvariance.lean:467-482`) — witness is
  literally `⟨0, fun s η => by simp⟩`, with an in-file comment promising the
  real Stokes route "when A.2 is upgraded." Its consumers
  `chainIntegral_kills_boundary_of_closed` (`:490`) and
  `period_homology_invariance_descent` (`:520-527`) are sorry-free *because*
  they inherit the zero witness.
- `Nonempty Unit` placeholder leaves (vacuously true, zero content): the
  cover-independence statement `pathIntegralViaCover_partition_independent`
  (`PeriodHomologyInvariance.lean:148` — the file itself calls it "the
  deepest piece of the multi-chart machinery"), `exists_pathChartCover`
  (`:132`), all four closedness lemmas in
  `Blueprint/Sec03/HolomorphicFormIsClosed.lean` (`:59, :75, :90, :103`,
  including `holomorphic_form_is_closed`), and 4 umbrella statements in
  `StokesOnRSWithBoundary.lean`.
- **A documented correctness gap below everything:** `chartedForm`
  (`Periods/ChartedForm.lean:42-49`) drops the `D(c.symm)` transition factor
  (header note `:15-29`): the chart-local integrand is the genuine pullback
  only when chart transitions are translations. Every chart-level integral
  above inherits this; the file marks the fix as queued.

### 2c. Mathlib at the pin (verified in `.lake/packages/mathlib/`)

- `Mathlib/MeasureTheory/Integral/CurveIntegral/Basic.lean` — `curveIntegral`
  (`:123`), `curveIntegral_refl` (`:172`), `curveIntegral_trans` (`:274`),
  and FTC-at-the-source `HasFDerivWithinAt.curveIntegral_segment_source'`
  (`:507`).
- `Mathlib/MeasureTheory/Integral/CurveIntegral/Poincare.lean` — **the big
  asset.** Convex Poincaré lemma: a closed 1-form (symmetric `fderiv`) on an
  open convex set admits a primitive,
  `exists_forall_hasFDerivAt_of_fderiv_symmetric` (`:380`); for `𝕜 = ℝ, ℂ`
  and differentiable `f`, `exists_forall_hasDerivWithinAt` (`:397`) gives a
  primitive of `f` on a convex set. Homotopy invariance of `curveIntegral`
  under C² homotopies (`:230, :255, :273`). The module header states the
  simply-connected generalisation is future work — it is **not** at the pin.
- `Mathlib/Analysis/Complex/HasPrimitives.lean` — `IsExactOn` (`:115`).
- `Mathlib/Analysis/Calculus/ParametricIntegral.lean` — differentiation
  under the integral sign (present; useful for A5 variants).
- `Mathlib/Topology/Connected/LocPathConnected.lean` —
  `pathConnectedSpace_iff_connectedSpace` for `LocPathConnectedSpace`; and
  `ChartedSpace.locPathConnectedSpace`
  (`Mathlib/Geometry/Manifold/ChartedSpace.lean:268`) gives
  `LocPathConnectedSpace X` for free from `ChartedSpace ℂ X` — so A1 below
  is nearly free.
- `Mathlib/Topology/Homotopy/Lifting.lean` — `monodromy_theorem` (`:152`),
  `IsLocalHomeomorph.existsUnique_continuousMap_lifts` (`:169`),
  `IsCoveringMap.existsUnique_continuousMap_lifts` (`:421`). The complete
  covering/monodromy engine jc7's B4 builds on; relevant here only as the
  fallback Stage A route (§5).
- `Mathlib/AlgebraicTopology/FundamentalGroupoid/SimplyConnected.lean` —
  present, but the homology route below does not need it.
- Negative results: no manifold-level Poincaré lemma, no simply-connected
  curve-integral independence, no singular-chain ↔ curve-integral bridge,
  no Hurewicz theorem (`H₁ ≅ π₁ᵃᵇ`). jc7's B4 survey independently
  confirmed the first two negatives plus the C⁰-vs-C² homotopy gap in
  `Poincare.lean`'s invariance theorems, and located the upstream WIP
  (Mathlib PR #24019) for the simply-connected Poincaré lemma.

## 3. Stage S — making the statement true (prerequisite NEW-WORK)

Owner: `SmoothDifferentialForm.lean` (per the provider docstring). Two
designs:

- **S1a — discrepancy differential (recommended pricing baseline).** Keep
  the product carrier. Define `truePeriods : HolomorphicOneForm ℂ X →ₗ
  (IntegralOneCycle X →ₗ[ℤ] ℂ)` by genuine integration (this is S2), then
  set `d₁(α, φ) := (coefficient part, φ − truePeriods(α-part))` and
  `d₀(f, ψ) := (df-coefficient, 0)` (exact forms have zero periods, so the
  degree-1 payload of `d₀` is honestly `0`). Then `ClosedForm 1 X = ker d₁`
  ties the payload to the *actual* periods, `hω` becomes "all genuine
  periods of `α` vanish," and the provider becomes the classical theorem.
  `d² = 0` survives. Statement-level cost: **medium, frontier-moving, one
  owner commit-series** — but every downstream file reading `ClosedForm 1 X = ⊤`
  by `rfl`-adjacent automation must be re-audited (NEW-WORK: **routine but
  wide**, repo-scale grep + rebuild).
- **S1b — full chartwise smooth forms** (real `(1,0)/(0,1)` decomposition,
  wedge, chartwise `d`): the eventual Hodge-layer substrate. **Hard,
  own-subtree, multi-month**; not needed just to make #242 honest.

- **S2 — periods as integrals (the shared hard leaf).** Required by either
  design, and independently by jc7's B4:
  1. Fix `chartedForm`'s dropped `D(c.symm)` factor
     (`ChartedForm.lean:15-29`) and re-prove the `PathIntegralViaChartCorrect*`
     algebra over the corrected integrand. **Routine-to-medium, farmable,
     but touches a 140-file family** — mostly mechanical re-threading.
  2. Cover-independence of `pathIntegralViaCoverWith` (today a
     `Nonempty Unit` stub, `PeriodHomologyInvariance.lean:148`): common
     refinement of two partitions + `curveIntegral_subpath_of_le` +
     chart-overlap agreement of corrected integrands. **Medium-hard,
     multi-commit, serial** (overlap agreement needs the S2.1 fix).
  3. Extend per-simplex integration ℤ-linearly to `SingularOneChain X`
     (Blueprint sub-leaf A.2, free-module universal property). **Routine,
     single commit.**
  4. Stokes kills-boundary: `I(∂₂ s) η = 0`. Classical route: subdivide the
     2-simplex domain until each affine piece maps into one chart (Lebesgue
     number; affine subdivision of `Δ²` — *not* in Mathlib, NEW-WORK
     **medium**); per small piece, the corrected chart integrand is
     holomorphic, hence closed (Cauchy–Riemann — today a `Nonempty Unit`
     stub, `HolomorphicFormIsClosed.lean:103`; real proof **medium** from
     `ContMDiff` sections), hence has a local primitive on a convex chart
     image (Mathlib `Poincare.lean:380/:397` — **free**); boundary integral
     of an exact form telescopes to zero (`curveIntegral` FTC + `trans` —
     **routine**); sum over pieces, interior edges cancel (**medium**
     bookkeeping; the proved Green-rectangle leaves
     `StokesOnRSWithBoundary.lean:128/:173` serve the alternative
     rectangle-chart route). Net: **hard, own-subtree, the single worst
     leaf in both this document and jc7's** — but with the convex Poincaré
     lemma now in Mathlib it is finite and chartable, no longer
     potential-theory-shaped.

## 4. Stage A — the classical argument, step by step (priced)

On the repaired substrate, `hω` = "all genuine periods of the coefficient
form `α` over `H₁(X, ℤ)` vanish." Fix the convention `θ = (f, ψ)` with
`ψ := 0`.

- **A1. Basepoint and global paths.** `ConnectedSpace X` + charts over `ℂ`
  ⇒ `LocPathConnectedSpace X` (directly by
  `ChartedSpace.locPathConnectedSpace`, `ChartedSpace.lean:268`) ⇒
  `PathConnectedSpace X` via `pathConnectedSpace_iff_connectedSpace`.
  Choose basepoint `p` and, per `x`, a path `γₓ : Path p x`
  (`Classical.choice`). **Nearly free.**
- **A2. Candidate primitive.** `θ(x) := pathIntegralViaCover ω γₓ` — needs
  the unparameterised wrapper over `pathIntegralViaCoverWith` (partition
  from compactness of `[0,1]` + Lebesgue number; partial machinery exists in
  the `PathIntegralViaCover*` family). **Routine-to-medium**, gated on
  S2.2's cover-independence.
- **A3. Loop integrals factor through H₁ — the heart.**
  (a) A loop at `p` *is* a continuous `C(I, X)` with equal endpoints, i.e. a
  singular 1-simplex whose chain is a cycle (`simplex_to_path` is the bridge
  in the other direction; the forward direction is a definition + `∂σ = x −
  x = 0`). NEW-WORK **routine, single commit**.
  (b) Integral agreement: the per-simplex chain integration of S2 applied to
  the loop's simplex equals the `Path`-level integral of A2. **Routine** if
  S2.3 is set up with this as its defining clause.
  (c) Kills-boundary (S2.4) ⇒ the loop integral depends only on
  `singularH1ClassOfCycle` (`Hurewicz.lean:522/:536`) ⇒ vanishes by `hω`.
  **Assembly routine; all cost lives in S2.4.**
- **A4. Well-definedness.** Two paths `γ, γ'` from `p` to `x`: concatenation
  `γ.trans γ'.symm` is a loop; additivity + symm of the corrected path
  integral (`PathIntegralViaChartCorrectAdd` family, re-proved in S2.1)
  give `∫γ − ∫γ' = ∫loop = 0` by A3. **Medium plumbing, farmable.**
- **A5. Smoothness and `dθ = ω`.** Near `x₀`, work in the (stable) chart:
  the corrected integrand is holomorphic on the convex chart image, so has
  a primitive `F` (Mathlib `Poincare.lean:397`). Path-independence (A4)
  localises: `θ(x) = θ(x₀) + ∫segment`, and the segment integral is
  `F(chart x) − F(chart x₀)` by `curveIntegral` FTC
  (`Basic.lean:507` + `curveIntegral_trans :274`). Hence `θ = const + F ∘
  chart` locally — `ContMDiff` with the right derivative; chartwise this is
  exactly `d₀(f, 0) = (α, truePeriods-discrepancy 0)`, i.e. `dθ = ω` in the
  S1a substrate (the payload equation holds because `ker d₁` already forces
  `φ = truePeriods(α) = 0` under `hω`). **Medium, multi-commit; the
  chart-coherence of `F` across overlaps is where `StableChartAt` earns its
  keep** — watch jc8's #237 `StableChartAt` elimination, which rewrites the
  hypotheses of every citation above.
- **A6. Assembly into the provider** via
  `…primitiveExists_exact_assembly` (`:1115-1125`). **Routine, single
  commit.**

## 5. Comparison with jc7's landed `docs/perron-b4-conjugate-phase0.md`

jc7's document landed (upstream `68bb3afc`) while this one was being
written; it was read in full. The findings interact more sharply than
"shared NEW-WORK":

1. **B4 rejected the integral route — for exactly the gaps priced here.**
   Its route (a) (`v = Im ∫ 2(∂u/∂z) dz`) was killed by the same verified
   Mathlib negatives: no 1-forms/curve integrals on charted spaces, no
   simply-connected primitive theorem, C⁰-homotopies from
   `IsSimplyConnected` vs the C² hypothesis in `Poincare.lean`. The two
   independent surveys agree on every negative — a useful confidence check
   for the manager.
2. **B4's dodge is not available to #242.** B4 escaped into a
   covering-space engine (germ space of local conjugates + monodromy
   killed by `SimplyConnectedSpace` lifting, `Lifting.lean:421`) because
   its domain is a *simply connected* cut domain and its conclusion never
   mentions integrals. #242's domain is the whole compact surface (genus
   `g`, not simply connected), and its hypothesis *is* "the integration
   periods vanish" — the comparison map must become an honest integration
   map for the statement to mean anything (§1, §3). So the chain-level
   integration + Stokes kills-boundary engine (S2.3/S2.4) is irreducible
   for #242 even though B4 avoided it. **The previously hoped-for "one
   shared Stokes engine for both" does not materialize; S2 is #242's own
   worst leaf.**
3. **What genuinely is shared.** (i) B4's W1 (constant-difference lemma —
   two conjugates on a preconnected open differ by a constant) has a
   verbatim analogue here ("two local primitives of `ω` differ by a
   constant"), needed in A4/A5; build the chartwise
   `fderiv = 0 ⇒ locally constant` plumbing once. (ii) B4's W3/W4
   germ-covering construction is a candidate **fallback Stage A route**
   for #242: the germ space of local primitives of `ω` is a covering with
   deck group the periods, and monodromy then factors through `H₁` because
   `ℂ` is abelian. Caveat making it strictly a fallback: connecting that
   monodromy factorization to `IntegralOneCycle X` needs Hurewicz
   (`H₁ ≅ π₁ᵃᵇ`) — absent in Mathlib, and the repo's cellular comparison
   is the 4-sorry blocked corner of `Hurewicz.lean`. The Stokes route
   (S2.4) works directly with singular chains and avoids Hurewicz
   entirely. (iii) Both reduce chart-local analysis to
   `CurveIntegral/Poincare.lean` / `Harmonic/Analytic.lean` ball-local
   results.
4. **Sequencing note for the manager.** If B4's W1/W3/W4 land first, #242's
   Stage A inherits the constant-difference plumbing (and the fallback
   route) for free; nothing in #242's Stage S waits on B4, and nothing in
   B4 waits on #242.

## 6. Honest conclusion

- **Do not attempt Lean work on #242 now.** The sorry is unprovable on the
  current substrate; the only sound next move is the Stage S owner decision
  (S1a recommended as pricing baseline) plus the shared S2 engine. A
  "proof" appearing without Stage S would necessarily be exploiting a
  vacuity that does not exist — reject it in review.
- **Total scale:** Stage S = one medium owner commit-series (S1a) + one
  hard own-subtree engine (S2, dominated by S2.4 Stokes) + one wide-but-
  mechanical re-threading (S2.1 over the 140-file integral family). Stage A
  = ~6 steps, all routine-to-medium once Stage S lands, generously
  supported by pinned Mathlib (`CurveIntegral/Basic+Poincare`,
  `LocPathConnected`). Nothing here is engine-scale in the
  Perron/uniformization sense; the worst leaf is finite, chartable, and
  shared with jc7.
- **Revisit triggers:** (i) the `SmoothDifferentialForm.lean` owner's S1
  design decision (S1a vs S1b changes A5's shape); (ii) jc8's #237
  `StableChartAt` elimination — every citation above carries the
  `[StableChartAt ℂ X]` hypothesis (the landed `f6958276` already ported
  one pullback-continuity lemma off it); (iii) any Mathlib bump past the
  pin — the simply-connected Poincaré lemma (WIP PR #24019, announced in
  `Poincare.lean`'s header) would shortcut parts of S2.4/A3; (iv) B4's
  W1/W3/W4 landing — adopt its constant-difference and germ-covering
  layers into Stage A per §5.4; (v) a Hurewicz (`H₁ ≅ π₁ᵃᵇ`) theorem
  appearing in Mathlib or the repo — upgrades §5.3(ii) from fallback to
  contender.

## Search log

- Docs: full reads of `docs/perron-engine-phase1.md`,
  `docs/rr-dimension-input-phase0.md` (format standard),
  `docs/perron-a2a3-topology-phase0.md`, and — after it landed mid-write —
  `docs/perron-b4-conjugate-phase0.md` (§5); `gh issue view 242`.
- Project: `grep` for `deRhamComparisonMap1`, `exteriorDerivative`,
  `ClosedForm`, `ExactForm`, `SmoothDiffForm*`, `HolomorphicOneForm`,
  `IntegralOneCycle`, `StableChartAt`, `periodPairing`,
  `period_homology_invariance(_descent)`, `chain_integration_kills_boundary`,
  `chartedForm`, `pathIntegralInChart`, `pathIntegralViaCoverWith`,
  `exists_uniform_chart_partition`, `simplex_to_path`,
  `singularH1ClassOfCycle`, `Hurewicz`, `Nonempty Unit` (stub census),
  `sorry` counts across `Jacobian/Periods/` (225 files, 215 sorry-free) and
  `Jacobian/Blueprint/Sec03/`.
- Mathlib (pinned checkout): `curveIntegral` (found
  `MeasureTheory/Integral/CurveIntegral/{Basic,Poincare}.lean` — not under
  `Analysis/`), `IsExactOn` / `HasPrimitives`, `ParametricIntegral`,
  `SimplyConnectedSpace`, `pathConnectedSpace_iff_connectedSpace`; negative:
  no manifold Poincaré lemma, no simply-connected curve-integral
  independence, no barycentric/affine subdivision of `Δ²` for integration.
