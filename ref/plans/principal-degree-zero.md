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
| `branchedCoverData_of_nonconstant_holomorphic` | PARTIAL (named, `sorry`-bearing) | `Sec02/BranchedDegree.lean` leaf 8 |
| `MeromorphicFunctionType` real germ-sheaf API | ABSENT | `Sec01/MeromorphicFunction.lean` is a `X → OnePoint ℂ` placeholder |
| `vanishingOrder` chart-independence | PRESENT | `Jacobian/HolomorphicForms/VanishingOrder.lean` (`orderAt_eq_meromorphicOrderAt_of_mem_maximalAtlas`) |

## 4. Decomposition (7 sub-leaves)

Each leaf gets a stable Lean handle in `Sec01/PrincipalDegreeZero.lean`. Leaves marked HARD bottom out on the analytic frontier; leaves marked SHORT/MEDIUM are bookkeeping/assembly above the analytic facts.

| # | Lean handle | Class | Sketch | Deps |
|---|---|---|---|---|
| 1 | `principalDivisor_zero_of_underlying_zero` | SHORT | When the projection `underlyingC f` is identically `0`, `principalDivisor X f = 0`, hence its degree is `0`. Direct from the `principalDivisor` `by_cases` branch. | `principalDivisor`, `Divisor.degree` |
| 2 | `liftToCp1_branchedCoverData` | HARD | For nonzero nonconstant `f`, package `meromorphicToCp1 X f : X → OnePoint ℂ` as a `BranchedCoverData X (OnePoint ℂ) (meromorphicToCp1 X f)`. Reduces to the existing `branchedCoverData_of_nonconstant_holomorphic` (Sec02 leaf 8) once the holomorphicity hypothesis on `meromorphicToCp1` is wired up. | Sec02 leaf 8, `meromorphicToCp1`, `meromorphic_as_cp1_map` |
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

Total ≈ 530 LOC, plus the transitive Sec02 leaf 8 (`branchedCoverData_of_nonconstant_holomorphic`, ~200–300 LOC) which this plan inherits as a dependency.

## 8. What is genuinely blocked

After this scaffold lands, the only remaining mathematical sorries on the path to `principal_degree_zero` are:

- `branchedCoverData_of_nonconstant_holomorphic` (Sec02 leaf 8, HARD: open-mapping + isolated-zeros + compactness-of-fibres on a compact RS).
- Leaves 3 + 4 (HARD: chart-local Laurent normal form + identification with ramification index).
- Leaves 5 + 6 (MEDIUM: Finsupp / fibre algebra).

Leaves 1, 2, 7 are SHORT bookkeeping above those.

The remaining infrastructure dependencies (real `MeromorphicFunctionType` field-of-meromorphic-germs, the chart-on-OnePoint-ℂ-at-∞ API for leaf 4) are noted in §3 as the points that will need to be revisited if the placeholder `MeromorphicFunctionType := X → OnePoint ℂ` is upgraded.
