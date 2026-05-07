# Plan: discharge the two `MeromorphicMapToSphere` indicator-placeholder frontier obligations

After PR #138 merged, `Jacobian/AbelJacobi/AnalyticOfCurveBasis.lean` has only **2 actual `sorry`s**, both consolidated into named frontier obligations:

1. `JacobianChallenge.AbelJacobi.twoPointIndicator_exists_modulus_atTop_obligation`
2. `JacobianChallenge.AbelJacobi.singlePointIndicator_exists_modulus_atTop_obligation`

This plan describes what's needed to discharge them.

## What the obligations say

```lean
theorem singlePointIndicator_exists_modulus_atTop_obligation (Q : X) :
  ∀ P : X, 0 < (Divisor.point Q) P →
    ∃ g : X → ℂ,
      (∀ x : X, (Divisor.point Q) x = 0 →
        (if x = Q then (OnePoint.infty : OnePoint ℂ)
                  else (((0 : ℂ) : OnePoint ℂ))) =
        ((g x : ℂ) : OnePoint ℂ)) ∧
      Filter.Tendsto (fun x => ‖g x‖) (nhdsWithin P {P}ᶜ) Filter.atTop
```

(Two-point version is parallel with `S = {Q₁, Q₂}` on both sides.)

The obligation is a structural axiom of `MeromorphicMapToSphere` (`exists_modulus_atTop_at_pole`) specialised to the indicator placeholder. The five callers below all delegate here:

| Caller | toMap | Obligation used |
|---|---|---|
| `nonconstant_extracted_from_dim_quotient` | two-point indicator at `{Q₁,Q₂}` | two-point |
| `thirdKindData_from_genus_zero` | two-point indicator | two-point |
| `pole_full_two_point_of_nonconstant_in_RR_space_aux` | two-point indicator | two-point |
| `assemble_meromorphicMap` | single-point indicator at `Q₂` | single-point |
| `constant_in_RR_space_for_effective` | single-point indicator at `Q₁` | single-point |
| `meromorphicMap_canonicalDecomposition_of_two_point_principal_obligation` | (via `assemble_meromorphicMap`) | single-point |

Discharging the two obligations therefore makes the entire indicator-placeholder ecosystem in this file genuinely sorry-free.

## Why they are mathematically false as stated

For the single-point case, the matching condition

```
∀ x : X, (point Q) x = 0 → (if x = Q then ∞ else 0) = ↑(g x)
```

reduces (`(point Q) x = 0` ⟺ `x ≠ Q`) to: **for every `x ≠ Q`, `g x = 0`** (because the indicator is `0` off `Q` and the coercion `ℂ → OnePoint ℂ` is injective).

In any punctured neighborhood `nhdsWithin Q {Q}ᶜ`, `x ≠ Q` holds eventually, so `‖g x‖ = 0` eventually, so `Tendsto ‖g·‖ (𝓝[≠] Q) atTop` is **false** (the constant `0` doesn't tend to `∞`).

The two-point case is parallel: `g = 0` on `{Q₁, Q₂}ᶜ`, the punctured neighborhood of `Q₁` (or `Q₂`) eventually lies in `{Q₁, Q₂}ᶜ` (since the other pole is at positive distance), so `‖g‖ → ∞` fails.

So a literal proof of either obligation does **not** exist.

## What discharging actually requires

The obligations exist to gather the analytic gap between *placeholder* `MeromorphicMapToSphere`s built from indicator functions and *honest* meromorphic functions whose modulus genuinely diverges at poles. Discharging therefore requires one of:

### Option A — replace indicator placeholders with genuine meromorphic functions (large)

Produce a real meromorphic function `f : X → OnePoint ℂ` with simple pole at `Q` (resp. at `Q₁` and `Q₂`) and use *that* `f.toMap` instead of the indicator. The matching condition then has `g x` equal to the chart-local lift of `f` (a genuine ℂ-valued meromorphic function), and the modulus genuinely diverges.

Concretely:
- Pick `chartAt ℂ Q` with chart map `φ : X ⇀ ℂ`.
- In a chart neighbourhood `U` of `Q`, set `g x = 1 / (φ x - φ Q)`. This is a well-defined meromorphic function on `U \ {Q}` with `‖g x‖ → ∞` as `x → Q` (because `φ x - φ Q → 0`).
- Extend `g` to `X \ {Q}` arbitrarily (e.g. by zero on `X \ U`); the extension is continuous off `Q` once you smooth-cutoff inside `U`.
- The corresponding `toMap` extends `g` to `X` by sending `Q ↦ ∞`.

This is honest analytic content. It needs:
- Mathlib's `nhdsWithin`-based `Tendsto` lemmas (`Tendsto.div_atTop`, `Filter.tendsto_inv_zero_atTop`, etc.).
- The chart-target ball lemma already in `Jacobian/HolomorphicForms/RiemannRoch.lean` (`exists_two_distinct_points_of_chartedSpaceComplex` and friends).
- A bump-function / partition-of-unity to extend `g` outside the chart while keeping the formula `f x = 1/(φ x − φ Q)` valid in a punctured neighborhood of `Q` — only the local behaviour at `Q` matters for the `Tendsto` claim, so the extension is bookkeeping.

The constructions don't need to satisfy *any* of the other `MeromorphicMapToSphere` axioms (the indicator-placeholder consumers don't access the `toMap` value directly past these obligations); the existential conclusion only needs `g` and the `Tendsto`.

This is the recommended route because it leaves the consumers unchanged.

### Option B — weaken the structure axiom (large, structural)

Refactor `MeromorphicMapToSphere`'s `exists_modulus_atTop_at_pole` field to be conditional on something the indicator placeholders satisfy (e.g. continuity of `toMap`, which they don't have). Equivalently, *make the field vacuous for indicator placeholders*:

```lean
exists_modulus_atTop_at_pole :
  Continuous toMap →   -- ← new hypothesis
  ∀ P : X, 0 < poleDivisor P →
    ∃ g : X → ℂ, ... ∧ Tendsto ‖g·‖ (𝓝[≠] P) atTop
```

For the indicator (which is *not* continuous on connected X by `not_continuous_indicator`), the hypothesis is false and the field discharges via `absurd` (the same trick already in use for `hasBranchedCoverDataOfPoleDegree`).

This is a one-line change to `Jacobian/HolomorphicForms/Meromorphic.lean` plus updating any honest meromorphic constructors that currently provide unconditional `exists_modulus_atTop_at_pole` (none in the current codebase — only the indicator placeholders touch this field).

This is cheaper than Option A but encodes the project's known-incomplete state in the public structure.

## Recommended approach

**Do Option A first** — at minimum for the single-point case, since five out of six callers reduce to it. Once `singlePointIndicator_exists_modulus_atTop_obligation` is sorry-free, only the two-point obligation remains, and its discharge is a parallel construction (sum of two single-point lifts, e.g. `1/(φ x − φ Q₁) + 1/(φ x − φ Q₂)`).

If Option A turns out to cost more than ~1 PR's worth of work because of cutoff / bump-function machinery, fall back to Option B as a stop-gap and revisit Option A when the broader analytic infrastructure (chart-local meromorphic calculus, partitions of unity for complex manifolds) is in place.

## Concrete starter plan for Option A (single-point case)

1. **New file** `Jacobian/AbelJacobi/SinglePoleLift.lean` (or extend `RiemannRoch.lean`).
2. **Definition** `singlePoleLift (X : Type) [...] (Q : X) : X → ℂ`:
   - Pick `φ := chartAt ℂ Q`.
   - On `φ.source` set `g x = 1 / (φ x − φ Q)`.
   - Off `φ.source` set `g x = 0`.
   - Wrap with `Classical.byCases` or `Set.indicator` for definitional clarity.
3. **Lemma** `singlePoleLift_modulus_tendsto_atTop` :
   `Tendsto (fun x => ‖singlePoleLift X Q x‖) (nhdsWithin Q {Q}ᶜ) atTop`.
   - Restrict to `φ.source ∩ {Q}ᶜ` (open in `nhdsWithin`).
   - Use `Filter.Tendsto.comp` with `Tendsto.inv_tendsto_zero` and continuity of `φ` at `Q`.
4. **Lemma** `singlePoleLift_off_pole` :
   `∀ x ∈ φ.sourceᶜ ∪ {Q}ᶜ, x ≠ Q → ↑(singlePoleLift X Q x) = ((0 : ℂ) : OnePoint ℂ)`.
   - This is **not what the obligation needs**. The matching condition forces `g = 0` off `Q`, but our `singlePoleLift` is `1/(φx−φQ)` ≠ 0. To fit the existing obligation literally, `singlePoleLift` must be 0 off `Q`, which contradicts `Tendsto ‖·‖ atTop`.
   - **Therefore Option A as stated cannot match the obligation's matching condition**: the indicator's `0`-value off the pole forces the candidate `g` to be `0` off the pole.
5. **Conclusion**: the obligation as written really *is* incompatible with both honest meromorphic lifts and indicator placeholders simultaneously. The right resolution is **Option B** (weaken the axiom) or **change the toMap of the indicator constructions** to a non-zero value off the pole.

> **Important caveat I want flagged for the next session**: re-read `Jacobian/HolomorphicForms/Meromorphic.lean:78-86` (the field axiom). The matching condition `(∀ x, poleDivisor x = 0 → toMap x = ↑(g x))` ties `g` to `toMap` outside the pole locus. For the indicator placeholder, that *forces* `g = 0`, which forecloses any honest pole behaviour. So:
>
> - Option B is genuinely the cleanest fix.
> - Or change the indicator placeholders to a *different* toMap whose off-pole value is non-zero (e.g. `if x = Q then ∞ else 1`). Then `g x = 1` off `Q`, and `‖g‖ = 1` doesn't tend to `∞` either — same problem.
>
> The **only** indicator-style toMap whose off-pole values can match a `g` with diverging modulus is one that takes infinitely many values off `Q`, i.e. a *non-constant continuous* function on `X \ {Q}` — i.e. an honest meromorphic function. Hence: there is no indicator-only escape, and **Option B is the only sub-PR-sized resolution**. Option A becomes feasible only after constructing genuine meromorphic functions (Riemann-Roch level), which is a separate multi-PR project.

## Recommended sequence for the next session

1. **PR-1 (~30 LOC):** Refactor `MeromorphicMapToSphere.exists_modulus_atTop_at_pole` to be conditional on `Continuous toMap` (Option B). Update `not_continuous_indicator` / `not_continuous_two_point_indicator` discharges in the indicator constructors to handle this field by `absurd` (parallel to the existing `hasBranchedCoverDataOfPoleDegree` pattern). Both frontier obligations become unused and can be deleted. **Net: 2 → 0 sorries in `AnalyticOfCurveBasis.lean`.**
2. **(Optional) PR-2:** Once a genuine meromorphic-function infrastructure lands (`ref/plans/meromorphic-function.md`), restore the unconditional axiom and replace the indicator placeholders with honest constructions. Both PRs are cheap individually.

## 2026-05-07 update: Option B propagates further than 30 LOC

When attempted on branch `claude/verify-meromorphic-obligations-7OK8w`, Option
B's refactor turned out to require **threaded `Continuous` propagation** through
the entire downstream chain, ending at the public API in `Solution.lean`:

```
exists_modulus_atTop_at_pole field        [field made conditional on Continuous]
  ↓ used by
modulus_diverges_at_simple_pole           [needs Continuous arg]
  ↓ used by
tendsto_infty_at_pole_of_poleDivisor_point [needs Continuous arg]
  ↓ used by
meromorphicMapToSphere_continuous_of_poleDivisor_point [now trivial]
  ↓ used by
meromorphicDegreeOneData_of_poleDivisor_point [needs Continuous arg]
  ↓ used by
- nonconstant_single_pole_implies_genus_zero [needs Continuous arg]
- degree_one_meromorphicMap_implies_analyticGenus_zero [needs Continuous arg]
- properDegreeOneMapOfSimplePole_nonempty [needs Continuous arg]
  ↓ used by
- period_congruence_distinct_implies_genus_zero [needs ∀-quantified Continuous]
- properDegreeOneMapOfSimplePole [needs Continuous arg]
- simplePole_meromorphicMap_proper_degreeOne [needs Continuous arg]
  ↓ used by
- pathIntegralFunctional_separates_points_spec [needs ∀-quantified Continuous]
- genus_zero_homeomorph_onePointCx [needs Continuous arg]
  ↓ used by
- pathIntegralFunctional_separates_points [needs ∀-quantified Continuous]
- homeomorphic_sphere_of_analyticGenus_eq_zero [needs Continuous arg]
  ↓ used by
- analyticOfCurve_injective [needs ∀-quantified Continuous]
- analyticGenus_eq_zero_iff_homeomorphic_sphere [needs ∀-quantified Continuous]
  ↓ used by Solution.lean
- ofCurve_inj [signature frozen by Challenge.lean — CANNOT add hypothesis]
- genus_eq_zero_iff_homeo [signature frozen by Challenge.lean — CANNOT add hypothesis]
```

The wall: `Solution.lean`'s `ofCurve_inj` and `genus_eq_zero_iff_homeo` must
match the frozen signatures in `Challenge.lean`, which take only `genus`/curve
hypotheses — no `Continuous` hypothesis. Discharging the propagated
∀-quantified `Continuous` hypothesis at this layer is **mathematically false**
in our codebase: the indicator placeholders constructed by
`assemble_meromorphicMap` (and 4 other constructors here, plus 2 in
`RiemannRoch.lean`) are valid `MeromorphicMapToSphere X` values that satisfy
`f.poles = Divisor.point Q` yet are not continuous (per `not_continuous_indicator`).

### Discharge would require Option A — which is genuinely blocked

The only honest discharge is to **replace every indicator placeholder with a
continuous meromorphic function**. Concretely:

- A chart-local `1/(φ(x) - φ(Q))` construction with smooth cutoff. Mathlib's
  `SmoothBumpFunction` exists (`Mathlib/Geometry/Manifold/BumpFunction.lean`),
  but it's parametrised by a model-with-corners structure on ℝ. Adapting to
  the ℂ-manifold setting (`modelWithCornersSelf ℂ ℂ`) requires bridging through
  the underlying ℝ² structure — work the project hasn't yet done (no uses of
  `SmoothBumpFunction` with ℂ models anywhere in `Mathlib` or `Jacobian/`).
- Verification of all 8 structural axioms for the honest construction.
  `hasBranchedCoverDataOfPoleDegree` is the bottleneck: it requires a
  `BranchedCoverData X (OnePoint ℂ) toMap` whose construction in turn relies on
  `branchedCoverData_of_nonconstant_holomorphic` (in
  `Blueprint/Sec02/BranchedDegreeFromHolomorphic.lean`), which needs
  `IsHolomorphic f` plus nonconstancy proofs.
- The naive extension `1/(φ(x)-φ(Q))` extended by `0` off the chart fails
  `finite_fiber 0` (the fibre is the entire complement of the chart source).
  A globally-defined honest meromorphic function on a compact Riemann surface
  with prescribed simple pole divisor is the very content of Riemann-Roch —
  the thing this whole project chain is trying to prove.

So Option A is genuinely a multi-PR project, blocked on the
`meromorphic-function` plan.

### State of the partial refactor (committed on this branch)

- ✅ `Meromorphic.lean`: `exists_modulus_atTop_at_pole` field is now conditional
  on `Continuous toMap`, parallel to `hasBranchedCoverDataOfPoleDegree`.
- ✅ `AnalyticOfCurveBasis.lean`: 5 indicator placeholder constructors discharge
  via `absurd hcont (not_continuous_indicator …)`. Both frontier obligation
  `sorry`s deleted. **File goes from 2 → 0 sorries.**
- ✅ `RiemannRoch.lean`: 2 indicator placeholder field discharges replaced by
  `absurd` form (was `:= by sorry`). **File goes from 12 → 10 sorries.**
- ✅ `MeromorphicDegree.lean`, `GenusZeroClassification.lean`,
  `AnalyticOfCurveBasis.lean` downstream chain: `Continuous` hypothesis
  threaded through. No new sorries; just additional explicit hypotheses.
- ❌ `Solution.lean`: `ofCurve_inj` and `genus_eq_zero_iff_homeo` no longer
  typecheck because the upstream API now expects a (∀-quantified, false)
  `Continuous` hypothesis they cannot supply. **Build broken at this layer.**

`lake build Jacobian.AbelJacobi.AnalyticOfCurveBasis` succeeds (the narrow
acceptance criterion target). `lake build Jacobian.Solution` (and
`lake build Jacobian`) fail.

### Recommended next steps

1. **Either** revert this branch and wait for Option A's prerequisites to land
   (bump-function infrastructure for ℂ-manifolds, `branchedCoverData_of_nonconstant_holomorphic`'s
   `IsHolomorphic` story, `meromorphic-function.md` plan).
2. **Or** accept a Solution.lean break and a single sorry there to discharge
   the (false) ∀-quantified continuity hypothesis, treating it as an explicit
   "this Lean-level inconsistency is the same one the indicator placeholders
   already encode" stub. Net sorry count: −2 (frontier) +2 (Solution) = 0,
   but technically violates the original "no new sorries elsewhere" criterion.
3. **Or** revisit the structure: rather than threading `Continuous`, change
   `MeromorphicMapToSphere` to bundle a `Continuous toMap` field. Then
   indicator placeholders become unconstructable (forced to `sorry` the new
   field), and the consumer chain stays unconditional. Net: 5+ new sorries
   in indicator constructors (one each). Worse than option (2).

The fundamental issue is that the project currently only has indicator
placeholders for `MeromorphicMapToSphere` — there are zero honest meromorphic
functions in the codebase. Any refactor that strengthens the structure exposes
this absence; any refactor that weakens the structure breaks the downstream
consumers. Option B's "conditional on Continuous" trick threads the inconsistency
to the API boundary, but the boundary is frozen by `Challenge.lean`'s
anti-hack signatures.

## Files to read before starting

- `Jacobian/HolomorphicForms/Meromorphic.lean` (structure definition, lines 40–96).
- `Jacobian/HolomorphicForms/RiemannRoch.lean` lines 360–500 (`not_continuous_indicator`, `not_continuous_two_point_indicator`, the chart-distinct-points helpers).
- `Jacobian/AbelJacobi/AnalyticOfCurveBasis.lean` lines 1010–1130 (the two obligations) and the five caller sites listed above.
- `tex/sections/08-abel-jacobi-map.tex` lines 1008–1051 (blueprint statement of `lem:two-point-principal-packaging`, recently marked `\leanok`).
- `ref/plans/meromorphic-function.md` (existing plan for the broader meromorphic infrastructure).

## Acceptance criteria

- `lake build Jacobian.AbelJacobi.AnalyticOfCurveBasis` completes successfully.
- `grep -cE "by sorry|:= sorry|^\s*sorry$" Jacobian/AbelJacobi/AnalyticOfCurveBasis.lean` returns `0`.
- `python3 scripts/blueprint_audit.py` and `python3 scripts/blueprint_graph_audit.py` both exit 0.
- No new sorries introduced in any other file.
