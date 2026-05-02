# Breakthrough plan for `thm:principal-degree-zero`

This document is the multi-phase roadmap to discharge `principal_degree_zero`
end-to-end. Sibling document: `ref/plans/principal-degree-zero.md` (the
seven-leaf decomposition; this document is the *meta-plan* that sequences
attacks against those leaves).

Working method: TOPDOWN recursive shrinking (`ref/TOPDOWN.md`). Each round
either discharges a `sorry` outright, or replaces a `sorry` with a strictly
smaller named obligation.

Author's stance up front: the breakthrough is **not** a single LOC
expenditure; it is a sequence of architectural moves. The placeholder
`MeromorphicFunctionType X := X → OnePoint ℂ` (in
`Sec01/MeromorphicFunction.lean`) is the load-bearing simplification that
prevents the *analytic* leaves (3, 4, 5a, Sec02 leaf 8,
`liftToCp1_continuous`) from being provable. To break through those, the
project needs a real meromorphic-germ-sheaf API, which is a Phase B
architectural refactor. Within that refactor the analytic leaves become
Mathlib-shaped one-liners or short calculations.

---

## Phase A — algebraic discharges (no architectural change)

Tractable purely with `Finsupp` / `Finset` algebra and the existing
`BranchedCoverData` API. After Phase A, the only remaining sorries on the
chain to `principal_degree_zero` are *strictly analytic*.

### A1. Leaf 6 — `degree_principalDivisor_eq_zeros_minus_poles`

Discharge the body as Finsupp/Finset algebra above leaves 3, 4, 5
(treated as black-box hypotheses). The proof shape:

1. Unfold `Divisor.degree` to `Finsupp.degree`, which is
   `Σ p ∈ support, divisor p`.
2. Use leaf 5 (support ⊆ zeros ∪ poles) to inject `support` into
   `zeros_finset ⊎ poles_finset` (where the disjoint union is honest
   because `(0 : OnePoint ℂ) ≠ ∞`).
3. `Finset.sum_subset` extends the sum to the larger union, with the
   excess summands `0` (because outside support, the coefficient is `0`).
4. `Finset.sum_disjUnion` splits the union sum into the two fibre sums.
5. Substitute leaf 3 / leaf 4 to rewrite the coefficient at each fibre
   point as `±(h.ramificationIndex p : ℤ)`.
6. Pull the negative sign out of the poles sum.

Estimated size: ~120 LOC.

### A2. Leaf 7a — `principal_degree_zero_of_nonzero`

Discharge the body as the small assembly above leaves 1, 2, 6 +
`branchedDegree_eq_weightedFiberCard`. The proof shape:

1. Case-split on whether `f` is constant on `OnePoint ℂ`.
2. Constant case: by hypothesis `_hf`, the underlying ℂ-projection is not
   identically zero, so the constant is some `c : ℂ` with `c ≠ 0`. Then
   `vanishingOrder X p (fun q => (f q).getD 0) = 0` everywhere, so
   `principalDivisor X f = 0` and `Divisor.degree 0 = 0`. New named
   obligation: `principalDivisor_eq_zero_of_nonzero_constant`.
3. Nonconstant case:
   - Get `h := liftToCp1_branchedCoverData X f hconst trivial`.
   - Rewrite via leaf 6.
   - Rewrite each fibre sum as `(branchedDegree h : ℤ)` via
     `branchedDegree_eq_weightedFiberCard h y` (at `y = 0` and `y = ∞`).
   - The two terms cancel: `n − n = 0`.

Estimated size: ~80 LOC + ~30 LOC for the new
`principalDivisor_eq_zero_of_nonzero_constant` named obligation
(itself sorry-bearing in Phase A — discharged in Phase C — because it
needs the Laurent-order-at-a-nonzero-constant fact, which requires
meromorphicity).

### A3. Leaf 5a — Mathlib lookup attempt

`vanishingOrder_eq_zero_of_regular_point` reduces, via
`orderAt_eq_meromorphicOrderAt_of_mem_maximalAtlas`, to
`tendsto_ne_zero_iff_meromorphicOrderAt_eq_zero` (Mathlib).

But the Mathlib lemma requires `MeromorphicAt f x` as an explicit
hypothesis, which the placeholder `_hholo : True` does not provide.
**Conclusion: A3 is blocked by Phase B.**

---

## Phase B — architectural refactor of `MeromorphicFunctionType`

Replace the placeholder `MeromorphicFunctionType X := X → OnePoint ℂ`
with a structure that carries meromorphicity as a field. After this
refactor the placeholder hypotheses `_hholo : True` can be replaced by
projections from the structure.

### B1. New structure

```
structure MeromorphicFunctionType (X : Type*)
    [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X] where
  toFun : X → OnePoint ℂ
  isMeromorphic :
      ∀ p : X,
        JacobianChallenge.HolomorphicForms.VanishingOrder.MeromorphicAtX
          (fun q => (toFun q).getD 0) p
```

Plus `instance : CoeFun (MeromorphicFunctionType X) (fun _ => X → OnePoint ℂ)`
so existing `f x` syntax continues to typecheck.

### B2. Update consumers

- `Sec01/PrincipalDivisor.lean`: `(f x).getD 0` → `(f.toFun x).getD 0`.
- `Sec01/MeromorphicToCp1.lean`: identity definition uses `f.toFun`.
- `Sec01/MeromorphicAsCp1Map.lean`: nonconstancy hypothesis stays as a
  hypothesis on `f.toFun`.
- `Sec01/PrincipalDegreeZero.lean`: every `_hholo : True` becomes
  unnecessary and is removed (or kept as `True` for API compatibility,
  with the actual meromorphicity now extracted from `f.isMeromorphic`).

### B3. Remove `_hholo : True` from leaves 2–7a

After B2 the `_hholo` placeholder no longer carries any signal — every
analytic leaf can extract meromorphicity directly from `f.isMeromorphic`.
Remove the parameters or stub them as ignored.

Estimated size: ~200–400 LOC of mechanical signature changes plus
verification builds.

---

## Phase C — analytic discharges (post-refactor)

### C1. `liftToCp1_continuous`

Given `f.isMeromorphic`, the lift `meromorphicToCp1 X f := f.toFun` is
continuous: meromorphic-into-`OnePoint ℂ` is by definition continuous in
the chart-local sense, and the project's chart-pullback continuity
machinery transports this to `Continuous f.toFun`.

Estimated size: ~80 LOC.

### C2. Leaf 5a `vanishingOrder_eq_zero_of_regular_point`

With `f.isMeromorphic p` available, the Mathlib chain
- `f.isMeromorphic p : MeromorphicAt (f ∘ chart.symm) (chart p)`
- `tendsto_ne_zero_iff_meromorphicOrderAt_eq_zero` mp direction

reduces to: at a regular point of `f`, the chart-pullback tends to
`(f.toFun p).getD 0` (a finite nonzero ℂ-value), hence the meromorphic
order at the chart image is `0`.

Estimated size: ~60 LOC.

### C3. Leaves 3, 4 and the `ramificationIndex` definition

`Sec02/BranchedDegree.lean` leaf 8
(`branchedCoverData_of_nonconstant_holomorphic`) must define
`ramificationIndex p` as the absolute value of the meromorphic order
of the chart-pullback. With this choice, leaves 3, 4 become tautological
unfoldings:

- Leaf 3 (zero point): `(orderAt p f).untopD 0 = ramificationIndex p`
  because at a zero, the order is the positive ramification index.
- Leaf 4 (pole point): `(orderAt p f).untopD 0 = -ramificationIndex p`
  because at a pole, the order is the negative of the ramification index.

The definitional choice for `ramificationIndex` is the substantive design
work; the leaves themselves become bookkeeping.

### C4. Sec02 leaf 8 `branchedCoverData_of_nonconstant_holomorphic`

The full analytic constructor: given a nonconstant
`f : X → OnePoint ℂ` with `f.isMeromorphic`, package as
`BranchedCoverData`. Subleaves:

C4a. **`finite_fiber`** for every `y : OnePoint ℂ`. Proof: each fibre is
the zero set of `meromorphicToCp1 - y` (with `y = ∞` handled separately
via `1/f - 0`). The zero set of a non-identically-zero meromorphic
function is discrete by isolated-zeros (Mathlib
`AnalyticAt.eventually_ne_zero_of_isolated_zeros`), and a discrete set
in a compact T2 space is finite.

C4b. **`weightedFiberCard_const`**: this is the key analytic fact —
`Σ_{p ∈ f⁻¹{y}} ramificationIndex p` is independent of `y`. Proof:
classical degree-of-cover argument; on a connected target, the weighted
preimage count is locally constant, hence globally constant.

C4c. **`ramificationIndex` definition**: `e_p := |orderAt p (f.toFun.getD 0)|`
or equivalent. Positive because `f` is non-identically-zero in a
neighbourhood of `p`.

Estimated size: ~600–1200 LOC.

---

## Phase D — close the umbrella's typeclass gap

The umbrella `principal_degree_zero` carries
`[TopologicalSpace X] [CompactSpace X] [ChartedSpace ℂ X] [IsManifold ...]`
without `[T2Space X]`, so its `case pos` body has an isolated
`haveI : T2Space X := sorry`. To discharge:

D1. Decision: either (i) add `[T2Space X]` to the umbrella signature
   (matches every reasonable definition of "compact Riemann surface"),
   or (ii) provide a project-internal `[ChartedSpace ℂ X] →
   [IsManifold ... X] → T2Space X` instance, or (iii) keep the gap as
   a documentation marker.

The cleanest move is (i), but the umbrella's signature is shared with
its consumer `InputDivisors.input_divisors_holds`. Coordinated change.

---

## Execution log

### Round R1
Initial 7-leaf decomposition + plan doc (commit `c74afca`).

### Round R2
Leaf 2 body sorry-free; umbrella case-splits via leaf 1; new leaf 7a
(commit `3ff77fe`).

### Round R3
Leaf 5 body sorry-free above new leaf 5a; umbrella's typeclass gap
isolated to a `haveI` (commit `3d8486b`).

### Round R4 (Phase A1 + A2 + supporting refactor)

**A1 — leaf 6 discharged.** `degree_principalDivisor_eq_zeros_minus_poles`
body became a real Finsupp/Finset assembly above leaves 3, 4, 5.
Required adding the hypothesis `(hcond : ∃ x, (f x).getD 0 ≠ 0)` to
leaf 6's signature so that the `principalDivisor` `by_cases`
constructor lives in its non-trivial branch; the constant-zero-projection
case is handled separately by the umbrella + leaf 1.

**Sec02 supporting refactor.** `BranchedCoverData.weightedFiberCard`
was a structure field with default `((finite_fiber y).toFinset).sum
ramificationIndex`. As a field, it could be overridden by any
constructor, breaking the link between the formula and the
`weightedFiberCard_const` field. Refactor: make `weightedFiberCard` a
derived (`noncomputable`) `def` outside the structure, and rename the
constancy field to `fiberSum_const` (stated directly in terms of the
formula). Backward-compat lemma `weightedFiberCard_const` reproved as
a one-liner. No external module broke.

**A2 — leaf 7a discharged.** `principal_degree_zero_of_nonzero` body
became a `by_cases` on whether `f` is constant on `OnePoint ℂ`:

- **Constant case:** new sub-leaves 7b
  (`vanishingOrder_const_nonzero`, HARD analytic, bottoms out on
  Mathlib `meromorphicOrderAt_const`) and 7c
  (`principalDivisor_eq_zero_of_constant_nonzero`, sorry-free assembly
  above 7b) drive the constant `c = ↑z` (`z ≠ 0`) case to the zero
  divisor; the constant cases `c = ∞` and `c = ↑0` are ruled out by
  `hf : ∃ x, (f x).getD 0 ≠ 0`.
- **Nonconstant case:** apply leaf 6 to express degree as
  `(Z fibre sum) − (P fibre sum)`, then identify each ℤ-fibre-sum with
  `(h.weightedFiberCard y : ℤ)` via the new derived definition and
  cancel through `weightedFiberCard_const`.

**Net sorry-shape after R4:**

- `Sec01/PrincipalDegreeZero.lean`: 6 → 5 (leaves 3, 4, 5a, 7b, umbrella's
  T2-typeclass `haveI`).
- `Sec01/MeromorphicToCp1.lean`: 1 (`liftToCp1_continuous`).
- `Sec02/BranchedDegree.lean`: 4 (leaves 5, 6, 7, 8 — unchanged).

The remaining sorries on the chain to `principal_degree_zero` are:
- Leaves 3, 4 (HARD chart-local Laurent normal form).
- Leaf 5a (HARD Mathlib `tendsto_ne_zero_iff_meromorphicOrderAt_eq_zero`).
- Leaf 7b (HARD Mathlib `meromorphicOrderAt_const`).
- Sec02 leaf 8 (HARD analytic constructor).
- `liftToCp1_continuous` (HARD continuity of the CP¹ lift).
- Umbrella's T2-typeclass gap (Phase D).

All of these except the umbrella's T2 gap require the Phase B refactor
of `MeromorphicFunctionType` to provide a real meromorphicity hypothesis;
once that lands, leaves 3, 4, 5a, 7b, `liftToCp1_continuous` reduce to
short Mathlib lookups, and Sec02 leaf 8 becomes the major HARD analytic
construction.

### Round R5 (Phase B refactor + initial Phase C)

**Phase B refactor.** `MeromorphicFunctionType` upgraded from a placeholder
`def := X → OnePoint ℂ` to a structure with three fields: `toFun`,
`toFun_continuous`, `isMeromorphic`. A `CoeFun` instance preserves the
existing `f x` syntax at every consumer; only `meromorphicToCp1`'s body
changed from `:= f` to `:= f.toFun`. No other consumer broke.

**Phase C — initial discharges using the new structure:**

- `liftToCp1_continuous` (`Sec01/MeromorphicToCp1.lean`): sorry-free,
  reduces to `f.toFun_continuous`.
- Leaf 7b `vanishingOrder_const_nonzero`: sorry-free, reduces to Mathlib
  `meromorphicOrderAt_const` after unfolding through the project's
  `orderAt` chart-pullback definition.

### Round R6 (Phase C — leaf 5a + Phase D — umbrella)

**Leaf 5a `vanishingOrder_eq_zero_of_regular_point` discharged.** Six-step
proof:

1. From `meromorphicToCp1 X f p ≠ ↑0` and `≠ ∞`, extract `z : ℂ` with
   `f.toFun p = ↑z` and `z ≠ 0`.
2. `(·).getD 0` is continuous at `f.toFun p = ↑z` via Mathlib's
   `OnePoint.continuousAt_coe` reducing to `id`-continuity.
3. Compose with `f.toFun_continuous` to get continuity of the projection
   at `p`.
4. Pull back through the chart via `continuousAt_extChartAt_symm` and
   `extChartAt_to_inv` to get continuity of
   `(projection ∘ chart.symm)` at `chart p`.
5. Continuity at the chart point + `nhdsWithin_le_nhds` gives
   `Tendsto (proj ∘ chart.symm) (𝓝[≠] (chart p)) (𝓝 z)`.
6. Mathlib's `tendsto_ne_zero_iff_meromorphicOrderAt_eq_zero` (mp,
   feeding `f.isMeromorphic p`) closes
   `meromorphicOrderAt = 0`, hence `vanishingOrder = 0`.

Required adding `open Filter` and `open scoped Topology` to the file.

**Phase D — umbrella's T2 typeclass gap closed.** Added `[T2Space X]`
to both `principal_degree_zero` and its consumer
`InputDivisors.input_divisors_holds`. The umbrella body simplifies:

```
by_cases hf : ∃ x, (f x).getD 0 ≠ 0
· exact principal_degree_zero_of_nonzero X f hf
· exact principalDivisor_zero_of_underlying_zero X f hf
```

— sorry-free.

**Net sorry-shape after R6 on the principal_degree_zero chain:**

- `Sec01/PrincipalDegreeZero.lean`: 4 → 2 (leaves 3, 4 only).
- `Sec01/MeromorphicToCp1.lean`: 0 → 0.
- `Sec01/InputDivisors.lean`: 0 → 0 (only signature change).
- `Sec02/BranchedDegree.lean`: 4 → 4 (only leaf 8 is on our chain).

Total: 3 named sorries between the umbrella and the analytic floor.

### Remaining work to fully discharge `principal_degree_zero`

Three named obligations stand between the current state and a fully
sorry-free umbrella:

1. **Leaf 3 (HARD)** `vanishingOrder_eq_ramificationIndex_at_zero`.
   Reduces to: at a zero of `f` of "multiplicity `e`" in the chart,
   `meromorphicOrderAt = e`, and `ramificationIndex p = e` by
   construction of `liftToCp1_branchedCoverData`.

2. **Leaf 4 (HARD)** `vanishingOrder_eq_neg_ramificationIndex_at_pole`.
   Symmetric to leaf 3 at poles, with the chart at `∞ ∈ OnePoint ℂ`
   substituting `1/w` for the chart variable.

3. **Sec02 leaf 8 (HARD)**
   `branchedCoverData_of_nonconstant_holomorphic`. The full analytic
   constructor: open-mapping theorem for analytic maps + isolated-zeros
   theorem + compactness-of-fibres on a compact RS, with concrete
   definitions for `ramificationIndex`, `finite_fiber`, `fiberSum_const`.

To make leaves 3 and 4 *trivially* dischargeable, the cleanest move is
to re-implement `liftToCp1_branchedCoverData`'s body directly in
`Sec01/PrincipalDegreeZero.lean` (rather than delegating to Sec02 leaf
8), defining `ramificationIndex p` explicitly via `vanishingOrder`. The
remaining content (`finite_fiber`, `fiberSum_const`) collapses to two
focused HARD analytic obligations covering all of Sec02 leaf 8's
content.

LOC estimate to reach a fully sorry-free `principal_degree_zero`:
roughly 800–1500 LOC of analytic infrastructure (isolated-zeros on
compact RS + chart-local Laurent analysis), spread across Sec01 and
Sec02. This is multi-session work.
