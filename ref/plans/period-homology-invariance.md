# Plan: `lem:period-homology-invariance`

Blueprint label: `lem:period-homology-invariance`
Lean handle: `JacobianChallenge.Periods.period_homology_invariance_statement`
File: `Jacobian/Blueprint/Sec03/PeriodHomologyInvariance.lean` (new file from worker branch)
Class: **DECOMPOSE** (worker has shipped a two-layer scaffold)

## 1. Mathematical statement

If `γ, γ' : IntegralOneCycle X` represent the same class in `H_1(X, ℤ)`,
then `∫_γ ω = ∫_{γ'} ω` for every `ω ∈ Ω¹(X)`.

## 2. Choice of route

Two structural levels at which the lemma can be discharged:

- **Typed (descended) form.** Once `IntegralOneCycle X = H_1(X, ℤ)` is
  built from `Mathlib.AlgebraicTopology.SingularHomology`, two cycles
  representing the same class are *equal* in the type. The lemma
  becomes `congrArg (periodPairing ω)` — one line. The mathematical
  content has been paid up-front when `periodPairing` was given the
  type `IntegralOneCycle X →+ ℂ` (rather than the chain-level type).

- **Descent form.** Records the obligation that the chain-level
  integration map descends through `H_1` — i.e. there exists a
  ℤ-linear map on singular 1-chains whose composition with `∂_2`
  vanishes (and whose induced map on `H_1` is `periodPairing`).
  *This* is where the closed-forms + Stokes content lives:
  `∫_{∂Σ} ω = ∫_Σ dω = 0` because `dω = 0`.

The worker branch `claude/period-homology-invariance-xOgBd` shipped
a two-layer stub in `Jacobian/Blueprint/Sec03/PeriodHomologyInvariance.lean`
(139 LOC) that pins down both forms explicitly.

## 3. Mathlib v4.28.0 inventory

| prerequisite | status | path |
|---|---|---|
| `H_1(X, ℤ)` (singular homology) | PRESENT | `Mathlib.AlgebraicTopology.SingularHomology` |
| `IntegralOneCycle X` (project alias for `H_1(X, ℤ)`) | PRESENT | `Jacobian/Periods/IntegralOneCycle.lean` |
| `periodPairing : IntegralOneCycle X →+ ...` | PRESENT (opaque) | `Jacobian/Periods/PeriodFunctional.lean` |
| Path integration `pathIntegralChart` | PRESENT | `Jacobian/Periods/PathIntegralChart.lean` |
| Multi-chart wrapper `pathIntegralViaCoverWith` | PARTIAL | `Jacobian/Periods/PathIntegralViaCover.lean` |
| Linearity / partition-independence of `pathIntegralViaCover` | PARTIAL (sorry) | same |
| `lem:holomorphic-form-is-closed` (`dω = 0`) | PARTIAL (currently `True := trivial` placeholder) | `Jacobian/Blueprint/Sec03/HolomorphicFormIsClosed.lean` |
| `thm:stokes-on-rs-with-boundary` | ABSENT (sorry) | `Jacobian/Blueprint/Sec03/StokesOnRSWithBoundary.lean` |

## 4. Decomposition

The worker's branch (now merged) provides the structure:

| # | Lean handle | Class | Sketch | Status |
|---|---|---|---|---|
| 1 | `period_homology_invariance` (typed form) | SHORT | `congrArg`-style: equal classes in `H_1` give equal images under `periodPairing`. | Worker shipped scaffold; 1-line proof |
| 2 | `period_homology_invariance_descent` (descent form) | HARD | The chain-level integration `∫ ω` annihilates `∂_2 Σ` for any 2-chain `Σ`. Equivalent to "∫_{∂Σ} ω = ∫_Σ dω = 0" which combines (a) holomorphic-form-is-closed and (b) Stokes-on-RS-with-boundary applied at the chain level. | Worker shipped scaffold; sorry pending (a) + (b) |
| 3 | `pathIntegralViaCoverWith_partition_indep` | MEDIUM | Well-definedness of the chart-cover path integral across different partition choices. Bridge between (1) typed and (2) descent forms. | Worker references; sorry pending |
| 4 | `chainIntegral_zero_on_boundaries` | MEDIUM | `∫_{∂_2 Σ} ω = 0` for any 2-chain `Σ`, given (a) + (b). | Implicit in (2); could split out |

## 5. Assembly order

Worker's typed/descent split is the right structure. To finish:

1. Discharge (a) `lem:holomorphic-form-is-closed` (Mathlib manifold
   exterior-derivative API; ~200–400 LOC).
2. Discharge (b) `thm:stokes-on-rs-with-boundary` (per
   `ref/plans/stokes-on-rs-with-boundary.md`; ~1800 LOC).
3. With (a) + (b), the descent form's sorry becomes a 5–10 line
   chain-level computation.
4. With descent form discharged, the typed form is one `congrArg`.

## 6. What is genuinely blocked

This lemma is *paradigmatically* Stokes-blocked. The two upstream
gaps (closed-forms + Stokes-on-RS) are exactly the two pieces named
in `ref/plans/stokes-on-rs-with-boundary.md`. Once that plan ships,
this lemma is a ~50 LOC consequence.

The worker branch's merit: it encodes the *structural* obligation
(typed-vs-descent split) in code now, so future work can layer
against a stable interface.

## 7. LOC estimate

- Worker scaffold: 139 LOC (already shipped).
- Marginal remaining work once Stokes + closed-forms land: ~80 LOC.
- Transitive (including Stokes plan): ~2000 LOC.

## 8. Aristotle packet plan

This lemma's leaves are *not* independently submittable today —
every meaningful sub-goal threads through the Stokes-on-RS pipeline.
The recommendation is to wait until `ref/plans/stokes-on-rs-with-boundary.md`
has shipped its core leaves (specifically `integrateTwoForm` + the
local Stokes on chart pullbacks), then submit a single packet
finishing leaves (3) + (4) + the descent-form proof.

Until then, the worker scaffold is the right state: type signatures
fixed, sorries explicit, blockers documented in the file's docstring.
