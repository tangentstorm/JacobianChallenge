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

### Round R4 (this commit, Phase A1)
Leaf 6 body discharged as Finsupp/Finset algebra above leaves 3, 4, 5.

### Round R5 (this commit, Phase A2)
Leaf 7a body discharged as the small assembly above leaves 1, 2, 6 +
`branchedDegree_eq_weightedFiberCard`. New named obligation
`principalDivisor_eq_zero_of_nonzero_constant` (HARD, blocked by Phase B).

### Round R6+ (future)
Phase B + Phase C + Phase D as outlined above.
