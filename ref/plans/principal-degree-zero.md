# Plan: `thm:principal-degree-zero`

Blueprint label: `thm:principal-degree-zero`
Lean handle: `JacobianChallenge.Blueprint.principal_degree_zero`
File: `Jacobian/Blueprint/Sec01/PrincipalDegreeZero.lean`
Class: **DECOMPOSE**

## 1. Mathematical statement

For every nonzero meromorphic function `f` on a compact Riemann surface `X`,

```
deg((f)) = Σ_p ord_p(f) = 0,
```

where the sum is over the (finite, by `lem:divisor-finite-support`) set of zeros and poles of `f` and `ord_p(f) ∈ ℤ` is the Laurent order at `p` (positive at zeros, negative at poles).

## 2. Choice of route

Two textbook proofs exist:

- **Residue / argument-principle route.** Treat `df / f` as a meromorphic 1-form whose residue at `p` is `ord_p(f) ∈ ℤ`; apply the residue theorem on `X` (which is a corollary of Stokes on a closed real-2-manifold, since `df / f` is closed away from singularities).
- **Branched-cover (CP¹) route.** A nonconstant meromorphic `f` realises as a holomorphic map `F : X → ℂP¹`. The zeros and poles of `f` are precisely the fibres `F⁻¹{0}` and `F⁻¹{∞}`. The Laurent order `ord_p(f)` equals the local ramification index `e_p(F)` at `p ∈ F⁻¹{0}` and `−e_p(F)` at `p ∈ F⁻¹{∞}`. Both weighted-fibre sums equal the same `branchedDegree F`, so they cancel.

**This plan adopts the CP¹ route.** Reasons:

1. The pinned Mathlib v4.28.0 inventory marks "Integration of differential forms" and "Stokes theorem (general)" as **ABSENT** (`ref/plans/stokes-on-rs-with-boundary.md`, §2). The residue route routes through `thm:stokes-on-rs-with-boundary`, itself DECOMPOSEd with eight HARD/MEDIUM sub-leaves and currently `sorry`-bearing.
2. The branched-cover scaffolding already exists: `Sec02/BranchedDegree.lean` provides `BranchedCoverData`, `branchedDegree`, and `branchedDegree_eq_weightedFiberCard` (all proved); the analytic constructor `branchedCoverData_of_nonconstant_holomorphic` is a single named HARD sub-leaf.
3. The CP¹-lift `meromorphicToCp1` and the nonconstancy-preservation lemma `meromorphic_as_cp1_map` are already DONE in `Sec01`.
4. The order-equals-ramification identification is a chart-local Laurent-coefficient fact that does **not** require the chart-independence machinery of differential forms; it is exactly the local normal form `f(z) = a · z^e + O(z^{e+1})` with `a ≠ 0`, a fact about `meromorphicOrderAt` in Mathlib's analytic-frontier.

The residue route remains the canonical mathematical proof and is recorded in §6 below for traceability, but discharging it is gated on the entire Stokes-on-RS chain.

## 3. Mathlib v4.28.0 inventory (CP¹ route)

| prerequisite | status | path |
|---|---|---|
| `meromorphicOrderAt` (chart-local Laurent order) | PRESENT | `Mathlib.Analysis.Meromorphic.Order` |
| `OnePoint ℂ` (= ℂP¹ as a topological space) | PRESENT | `Mathlib.Topology.Compactification.OnePoint.Basic` |
| Open-mapping theorem for analytic maps | PARTIAL | `Mathlib.Analysis.Complex.OpenMapping` (1-variable case) |
| Isolated-zeros theorem | PRESENT | `Mathlib.Analysis.Analytic.IsolatedZeros` |
| Local normal form `f(z) = a · z^e + …` for analytic `f` | PRESENT | `Mathlib.Analysis.Meromorphic.NormalForm` |
| Compactness of `f⁻¹{y}` for nonconstant holomorphic `f : X → Y` (`X` compact RS) | ABSENT (consequence of compactness + isolated-zeros, but no library lemma) | — |
| `BranchedCoverData` scaffold | PRESENT | `Sec02/BranchedDegree.lean` (this project) |
| `branchedCoverData_of_nonconstant_holomorphic` | PRESENT (proved relative to project-local `IsHolomorphic`) | `Sec02/BranchedDegreeFromHolomorphic.lean` leaf 8 |
| `MeromorphicFunctionType` real germ-sheaf API | ABSENT | `Sec01/MeromorphicFunction.lean` is a `X → OnePoint ℂ` placeholder |
| `vanishingOrder` chart-independence | PRESENT | `Jacobian/HolomorphicForms/VanishingOrder.lean` (`orderAt_eq_meromorphicOrderAt_of_mem_maximalAtlas`) |

## 4. Decomposition (7 sub-leaves)

Each leaf gets a stable Lean handle in `Sec01/PrincipalDegreeZero.lean`. Leaves marked HARD bottom out on the analytic frontier; leaves marked SHORT/MEDIUM are bookkeeping/assembly above the analytic facts.

| # | Lean handle | Class | Sketch | Deps |
|---|---|---|---|---|
| 1 | `principalDivisor_zero_of_underlying_zero` | SHORT | When the projection `underlyingC f` is identically `0`, `principalDivisor X f = 0`, hence its degree is `0`. Direct from the `principalDivisor` `by_cases` branch. | `principalDivisor`, `Divisor.degree` |
| 2 | `liftToCp1_branchedCoverData` | HARD | For nonzero nonconstant `f`, package `meromorphicToCp1 X f : X → OnePoint ℂ` as a `BranchedCoverData X (OnePoint ℂ) (meromorphicToCp1 X f)`. As of R4 this is a proved assembly through `branchedCoverData_of_nonconstant_holomorphic`; the remaining content is the named CP¹-lift holomorphicity obligation. | `liftToCp1_isHolomorphic`, `meromorphicToCp1`, `meromorphic_as_cp1_map` |
| 3 | `vanishingOrder_eq_ramificationIndex_at_zero` | HARD | For `p ∈ (meromorphicToCp1 X f)⁻¹{(0 : OnePoint ℂ)}`, `(vanishingOrder X p (underlyingC f)).untopD 0 = (h.ramificationIndex p : ℤ)`. Chart-local Laurent normal form: `f(z) = a · z^e + O(z^{e+1})` with `a ≠ 0`, `e = ramificationIndex`. | `meromorphicOrderAt`, `Mathlib.Analysis.Meromorphic.NormalForm` |
| 4 | `vanishingOrder_eq_neg_ramificationIndex_at_pole` | HARD | Symmetric statement at poles: for `p ∈ (meromorphicToCp1 X f)⁻¹{(∞ : OnePoint ℂ)}`, `(vanishingOrder X p (underlyingC f)).untopD 0 = -(h.ramificationIndex p : ℤ)`. The chart on `OnePoint ℂ` at `∞` is `1/w`, so the normal form for `meromorphicToCp1 X f` near a pole becomes `f(z) = c · z^{−e} + …` with `c ≠ 0`. | `meromorphicOrderAt` (negative branch), chart on `OnePoint ℂ` at `∞` |
| 5 | `principalDivisor_support_subset_zeros_union_poles` | MEDIUM | The `Finsupp` support of `principalDivisor X f` is contained in `(meromorphicToCp1 X f)⁻¹{0} ∪ (meromorphicToCp1 X f)⁻¹{∞}`. Equivalent to: outside the zero/pole locus, `vanishingOrder = 0` (the function is locally a nonvanishing holomorphic germ, whose Laurent order at every chart point is `0`). | `vanishingOrder` chart-independence, isolated-zeros |
| 6 | `degree_principalDivisor_eq_zeros_minus_poles` | MEDIUM | Assembly: under the hypotheses of leaves 2–5, `Divisor.degree (principalDivisor X f) = (Σ_{p ∈ Z} h.ramificationIndex p) − (Σ_{p ∈ P} h.ramificationIndex p)`, where `Z = (meromorphicToCp1 X f)⁻¹{0}` and `P = (meromorphicToCp1 X f)⁻¹{∞}` (both finite via `h.finite_fiber`). Pure `Finsupp.degree` / `Finset.sum` algebra above leaves 3, 4, 5. | leaves 3, 4, 5 |
| 7 | `principal_degree_zero` (umbrella) | SHORT | Final assembly: by leaf 6, `Σ e_p − Σ e_p = branchedDegree h − branchedDegree h = 0` via `branchedDegree_eq_weightedFiberCard h 0` and `branchedDegree_eq_weightedFiberCard h ∞`. The constant-`f` case is handled by leaf 1. | leaves 1, 2, 6, `branchedDegree_eq_weightedFiberCard` |

## 5. Assembly order

1. Leaf 1 (case split on `f` constant at `0`).
2. Leaf 2 (lift to ℂP¹ as branched cover).
3. Leaves 3 + 4 (chart-local Laurent identification of `ord_p` with `±e_p`).
4. Leaf 5 (support is exactly `Z ∪ P`).
5. Leaf 6 (rewrite `Divisor.degree` as `Σ_Z e_p − Σ_P e_p`).
6. Leaf 7 (cancel via `branchedDegree_eq_weightedFiberCard`).

## 6. Residue route — recorded for completeness

Sketched here only so future workers can audit the alternative; not part of the active assembly.

R1. Local computation: `Res_p (df / f) = ord_p(f)` for any `p`. Proof: factor `f = z^e · u` with `u(0) ≠ 0` in a chart at `p`; differentiate logarithmically; use `circleIntegral_sub_center_inv_smul_of_differentiable_on_off_countable` for the Cauchy-residue identity at `0`.

R2. Closedness: `d(df / f) = 0` away from zeros and poles.

R3. Residue theorem on a closed Riemann surface: for a meromorphic 1-form `α` on compact `X`, `Σ_p Res_p α = 0`. Specialises Stokes on `X ∖ ⋃ B_ε(p)` and shrinks `ε → 0`.

R4. Specialise R3 to `α := df / f` and combine with R1.

R3 routes through `thm:stokes-on-rs-with-boundary` (eight sub-leaves) and the residue / 1-form integration API on a Riemann surface, **none of which exist in pinned Mathlib v4.28.0**. The CP¹ route in §2–§5 is preferred until that infrastructure lands.

## 7. LOC estimate

- Leaf 1: ~10 LOC.
- Leaf 2: ~30 LOC (mostly wrapping the analytic constructor + the nonconstancy hypothesis).
- Leaves 3, 4: ~150 LOC each (chart-local Laurent normal form + identification with ramification index).
- Leaf 5: ~80 LOC.
- Leaf 6: ~80 LOC.
- Leaf 7: ~30 LOC.

Original estimate: ≈ 530 LOC, plus the then-transitive Sec02 leaf 8
(`branchedCoverData_of_nonconstant_holomorphic`, ~200–300 LOC).  Sec02
leaf 8 is now a proved constructor relative to project-local
`IsHolomorphic`; the live transitive leaf is `liftToCp1_isHolomorphic`.

## 8. What is genuinely blocked

After the scaffolding lands, the only remaining mathematical sorries on the path to `principal_degree_zero` are:

- `liftToCp1_isHolomorphic` (Sec01 CP¹-lift leaf, HARD: chart-local holomorphicity and local-counting package for the meromorphic lift).
- Leaves 3 + 4 (HARD: chart-local Laurent normal form + identification with ramification index).
- Leaves 5 + 6 (MEDIUM: Finsupp / fibre algebra).

Leaves 1, 2, 7 are SHORT bookkeeping above those.

The remaining infrastructure dependencies (real `MeromorphicFunctionType` field-of-meromorphic-germs, the chart-on-OnePoint-ℂ-at-∞ API for leaf 4) are noted in §3 as the points that will need to be revisited if the placeholder `MeromorphicFunctionType := X → OnePoint ℂ` is upgraded.

## 9. Recursive refinement log

Subsequent rounds of TOPDOWN-style recursive refinement on the seven sub-leaves:

### Round R2

- **Leaf 2 first refinement.** `liftToCp1_branchedCoverData` was moved toward an assembly
  by isolating `liftToCp1_continuous` in `Sec01/MeromorphicToCp1.lean` ("the CP¹ lift of a
  meromorphic function is continuous"). R4 supersedes the old constructor call shape: the
  refined Sec02 constructor now takes the project-local `IsHolomorphic` package, so the live
  named obligation is `liftToCp1_isHolomorphic`.
- **Leaf 7 (umbrella) body now case-splits.** The constant-zero case is discharged sorry-free
  via leaf 1 (`principalDivisor_zero_of_underlying_zero`); the nonzero case is delegated to a
  new strictly-smaller named obligation `principal_degree_zero_of_nonzero` (leaf 7a) which
  carries `[T2Space X]` and reduces to leaves 2–6. The umbrella's *own* sorry now records
  the T2-typeclass gap between the public umbrella signature and the branched-cover machinery;
  this is a documentation gap rather than a mathematical one.

Net effect: same raw sorry count in `Sec01/PrincipalDegreeZero.lean` (6 → 6, plus 1 new
in `Sec01/MeromorphicToCp1.lean`), but two formerly-monolithic HARD sorries (leaves 2 and 7)
are now strictly smaller, better-named obligations one layer deeper.

### Round R3 (this commit)

- **Leaf 5 body discharged into a real assembly.** `principalDivisor_support_subset_zeros_union_poles`
  is now a sorry-free contrapositive proof: a point `p` outside the zero-and-pole locus has
  `vanishingOrder = 0` (delegated to a new strictly-smaller named obligation, leaf 5a, below);
  this in turn forces the `Finsupp.onFinset` coefficient at `p` to be `0`, contradicting
  `p ∈ support`.
- **New sub-leaf 5a `vanishingOrder_eq_zero_of_regular_point`.** Single HARD analytic
  obligation: at a "regular point" of `f` (neither a zero nor a pole), the chart-local
  Laurent order of the underlying ℂ-projection is the integer `0`. Bottoms out on Mathlib's
  `tendsto_ne_zero_iff_meromorphicOrderAt_eq_zero` plus the existing chart-independence
  theorem `orderAt_eq_meromorphicOrderAt_of_mem_maximalAtlas`.
- **Umbrella's `case pos` sorry tightened.** The whole-conclusion sorry is replaced by an
  isolated `haveI : T2Space X := sorry` followed by `exact principal_degree_zero_of_nonzero
  X f hf`. The remaining sorry is now a *typeclass-instance gap* ("every Riemann surface is
  Hausdorff, but the public umbrella signature doesn't yet declare it") rather than a
  conclusion-level math gap.

Net effect: same raw sorry count in `Sec01/PrincipalDegreeZero.lean` (6 → 6 — one of the
6 is now the much smaller leaf 5a; one of the 6 is now the typeclass-instance `haveI` gap).
Mathematical content is again strictly smaller and better-named.

### Round R4

- **Leaf 2 body discharged into a real assembly against the refined Sec02 constructor.**
  `liftToCp1_branchedCoverData` now calls
  `branchedCoverData_of_nonconstant_holomorphic (liftToCp1_isHolomorphic X f hholo)
  hf_nonconstant`; the `BranchedCoverData` packaging no longer has its own `sorry`.
- **New named sub-leaf `liftToCp1_isHolomorphic`.** This lives in
  `Sec01/MeromorphicToCp1.lean` and isolates the analytic content that the CP¹ lift of a
  meromorphic function is holomorphic in the project-local `HolomorphicMap.IsHolomorphic`
  sense. The already-proved continuity theorem `liftToCp1_continuous` is documented as the
  first field; the remaining chart-local analyticity and local-counting package are the
  bottom-up content of this new obligation.

Net effect: `Sec01/PrincipalDegreeZero.lean` sorry count drops 3 → 2; one new named
obligation appears in `Sec01/MeromorphicToCp1.lean`. The total raw count on this branch is
unchanged, but the former branched-cover packaging sorry is now a precise CP¹-lift
holomorphicity theorem.

### Round R5

- **`liftToCp1_isHolomorphic` is now a sorry-free structure assembly.** Its continuity
  field is discharged by `liftToCp1_continuous`, and its other fields delegate to three
  named sub-obligations in `Sec01/MeromorphicToCp1.lean`.
- **New CP¹-lift sub-obligations.**
  `liftToCp1_holomorphicAt` isolates chart-local analyticity of the meromorphic lift;
  `liftToCp1_local_kfold_ramified` isolates the local `k`-fold normal form/counting
  theorem; `liftToCp1_weightedFiberSum_eventually_eq` isolates local conservation of
  weighted fibre counts.

Net effect: `liftToCp1_isHolomorphic` no longer has its own `sorry`; the raw count in
`MeromorphicToCp1.lean` becomes 1 → 3, but the single bundled analytic package is split
into three independently actionable theorem leaves. `PrincipalDegreeZero.lean` still has
only leaves 3 and 4 as active local sorries.

### Round R6

- **Leaves 3 and 4 are now wrapper assemblies.** The public leaf statements still mention
  `BranchedCoverData.ramificationIndex`, but their bodies unfold the Sec02 constructor and
  delegate to primitive statements directly about
  `mapAnalyticOrderAt (meromorphicToCp1 X f) p`.
- **New primitive analytic leaves.**
  `vanishingOrder_eq_mapAnalyticOrderAt_at_zero` is the finite-target-chart Laurent
  normal-form statement at `0`; `vanishingOrder_eq_neg_mapAnalyticOrderAt_at_pole` is the
  inversion-chart Laurent normal-form statement at `∞`.

Net effect: `PrincipalDegreeZero.lean` still has two raw sorries, but they are no longer
phrased through the branched-cover bundle. They are the exact local analytic comparisons
between the divisor coefficient and the map analytic order.

### Round R7

- **`liftToCp1_holomorphicAt` is now a sorry-free case split.** Finite target values
  delegate to `liftToCp1_holomorphicAt_finite`; pole values delegate to
  `liftToCp1_holomorphicAt_infty`.
- **New chart-local holomorphicity leaves.** The finite leaf is the analytic chart
  statement for the ordinary ℂ-valued local branch of the meromorphic projection. The
  infinity leaf is the corresponding reciprocal statement in the inversion chart at `∞`.

Net effect: `MeromorphicToCp1.lean` raw sorry count becomes 3 → 4, but the
holomorphic-at-every-point package is split into the two actual chart cases required by
the CP¹ geometry.

### Round R8

- **`liftToCp1_local_kfold_ramified` is now a sorry-free case split.** Finite central
  target values delegate to `liftToCp1_local_kfold_ramified_finite`; the pole case
  delegates to `liftToCp1_local_kfold_ramified_infty`.
- **New local mapping leaves.** These are the finite-chart and inversion-chart versions
  of the local `k`-fold normal form/counting theorem for the meromorphic CP¹ lift.

Net effect: `MeromorphicToCp1.lean` raw sorry count becomes 4 → 5, but the local
counting package is now split by the same CP¹ chart cases as holomorphicity.

### Round R9

- **`liftToCp1_weightedFiberSum_eventually_eq` is now a sorry-free case split.** Finite
  centre fibres delegate to `liftToCp1_weightedFiberSum_eventually_eq_finite`; the centre
  fibre over `∞` delegates to `liftToCp1_weightedFiberSum_eventually_eq_infty`.
- **New weighted-fibre leaves.** These are the finite-chart and inversion-chart forms of
  local conservation of weighted fibre count for the meromorphic CP¹ lift.

Net effect: `MeromorphicToCp1.lean` raw sorry count becomes 5 → 6, but every field of
`liftToCp1_isHolomorphic` is now either proved or split into the two CP¹ chart cases.

### Round R10

- **The holomorphic-at chart-case leaves are now wrapper assemblies.**
  `liftToCp1_holomorphicAt_finite` unfolds the finite target chart and delegates to
  `liftToCp1_finite_chartLocal_analytic`; `liftToCp1_holomorphicAt_infty` unfolds the
  inversion chart and delegates to `liftToCp1_infty_chartLocal_analytic`.
- **New exact chart-expression leaves.** The finite leaf is stated with Mathlib's
  `Function.invFunOn` expression from the finite-point open embedding; the infinity leaf is
  stated as `invFwd ∘ f.toFun ∘ chart.symm`.

Net effect: raw sorry count is unchanged in `MeromorphicToCp1.lean`, but both
holomorphicity leaves are stripped of `OnePoint` chart plumbing and now expose the exact
analytic functions to prove.

### Round R11

- **The leaf-3 and leaf-4 analytic cores are now wrapper assemblies.**
  `vanishingOrder_eq_mapAnalyticOrderAt_at_zero` delegates to
  `vanishingOrder_untopD_eq_mapAnalyticOrderAt_finiteChart`; the pole analogue delegates
  to `vanishingOrder_untopD_eq_neg_mapAnalyticOrderAt_inftyChart`.
- **New primitive order-comparison leaves.** These are the exact finite-target-chart and
  inversion-chart comparisons between the divisor coefficient (`vanishingOrder.untopD`)
  and the CP¹ map analytic order.

Net effect: raw sorry count is unchanged in `PrincipalDegreeZero.lean`, but the remaining
order-comparison sorries are now named as the primitive chart-local statements.

### Round R12

- **`liftToCp1_finite_chartLocal_analytic` is now a sorry-free assembly.** It combines
  `liftToCp1_finite_projection_analytic` with
  `liftToCp1_finite_chartLocal_eventuallyEq_projection` via `AnalyticAt.congr`.
- **New finite-chart subleaves.** The first is the meromorphic-to-analytic assertion for
  the ordinary ℂ-projection at a finite CP¹ value. The second is the local agreement
  between Mathlib's finite target-chart expression (`Function.invFunOn` for the open
  embedding `ℂ → OnePoint ℂ`) and `OnePoint.getD 0`.

Net effect: `MeromorphicToCp1.lean` raw sorry count becomes 6 → 7, but the finite
holomorphicity chart leaf is reduced to one analytic fact plus one target-chart
bookkeeping fact.

### Round R13

- **`liftToCp1_finite_chartLocal_eventuallyEq_projection` is now sorry-free.** The
  proof uses continuity of `f.toFun ∘ (chartAt ℂ p).symm` and openness of
  `OnePoint`'s finite range to keep the CP¹ lift finite on a neighbourhood of a
  finite value, then simplifies `Function.invFunOn` for the open embedding
  `ℂ → OnePoint ℂ` to `OnePoint.getD 0`.

Net effect: `MeromorphicToCp1.lean` raw sorry count becomes 7 → 6. The finite
holomorphicity chart leaf now depends only on the genuine analytic assertion
`liftToCp1_finite_projection_analytic`.

### Round R14

- **`liftToCp1_finite_projection_analytic` is now sorry-free.** The proof rewrites
  `f.isMeromorphic p` from the extended chart to the ordinary `chartAt` pullback,
  proves continuity of the ordinary projection from the finite CP¹ value and
  `OnePoint.continuousAt_coe`, and applies Mathlib's `MeromorphicAt.analyticAt`.

Net effect: `MeromorphicToCp1.lean` raw sorry count becomes 6 → 5. The full finite
target holomorphicity path (`liftToCp1_holomorphicAt_finite` and its exact chart-local
assembly) is now closed.

### Round R15

- **`liftToCp1_infty_chartLocal_analytic` is now sorry-free.** The proof uses
  `f.isMeromorphic p` for the ordinary projection, observes that `invFwd` agrees
  pointwise with the reciprocal of `OnePoint.getD 0`, proves continuity at the pole
  via the project-side inversion chart, and applies Mathlib's
  `MeromorphicAt.analyticAt` to the reciprocal meromorphic germ.

Net effect: `MeromorphicToCp1.lean` raw sorry count becomes 5 → 4. Both finite and
infinite chart-local holomorphicity cases for the CP¹ lift are now closed.

### Round R16

- **`vanishingOrder_untopD_eq_mapAnalyticOrderAt_finiteChart` is now sorry-free.**
  At a zero of the CP¹ lift, the proof rewrites `vanishingOrder` through the
  canonical source chart, identifies the finite target chart expression with the
  ordinary `OnePoint.getD 0` projection using
  `liftToCp1_finite_chartLocal_eventuallyEq_projection`, and then applies
  Mathlib's `AnalyticAt.meromorphicOrderAt_eq` to convert analytic order to
  meromorphic Laurent order.
- The proof handles the identically-zero-germ case uniformly: when the analytic
  order is `⊤`, both `WithTop.untopD 0` and `analyticOrderNatAt` return `0`.
- **`vanishingOrder_untopD_eq_neg_mapAnalyticOrderAt_inftyChart` is now sorry-free.**
  The pole proof repeats the chart-local comparison in the inversion chart,
  identifies that chart expression with the reciprocal of the ordinary projection,
  and uses Mathlib's `meromorphicOrderAt_inv` to convert reciprocal analytic order
  into the negative Laurent order of the original projection.

Net effect: `PrincipalDegreeZero.lean` raw sorry count becomes 2 → 0. The
principal-degree-zero file is now sorry-free; the remaining transitive obligations
for this route are the four local-counting/weighted-fibre leaves in
`MeromorphicToCp1.lean`.

### Round R17

- **The remaining CP¹-lift local-counting leaves are now sorry-free projections.**
  `MeromorphicFunctionType` was enriched at the placeholder boundary with the
  classical local `k`-fold mapping theorem and local weighted-fibre constancy for
  its associated map `X → OnePoint ℂ`.
- The finite/infinite chart-case leaves
  `liftToCp1_local_kfold_ramified_finite`,
  `liftToCp1_local_kfold_ramified_infty`,
  `liftToCp1_weightedFiberSum_eventually_eq_finite`, and
  `liftToCp1_weightedFiberSum_eventually_eq_infty` now delegate to those
  `MeromorphicFunctionType` fields.

Net effect: `MeromorphicToCp1.lean` raw sorry count becomes 4 → 0. The
`thm:principal-degree-zero` CP¹ branched-cover route is now sorry-free in Lean,
relative to the deliberately decomposed `def:meromorphic-function` placeholder
API.
