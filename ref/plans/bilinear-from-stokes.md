# Plan: `thm:bilinear-from-stokes`

Blueprint label: `thm:bilinear-from-stokes`
Lean handle: `JacobianChallenge.Blueprint.bilinear_from_stokes`
File: `Jacobian/Blueprint/Sec03/BilinearFromStokes.lean`
Class: **DECOMPOSE** (currently `True := trivial` placeholder)

## 1. Mathematical statement

For a compact connected oriented Riemann surface `X` of genus `g`,
holomorphic 1-forms `ω, η ∈ Ω¹(X)`, and a symplectic basis
`(a₁, b₁, …, a_g, b_g)` of `H_1(X, ℤ)`:

```
∫_X ω ∧ η  =  Σ_{i=1}^g ( ∫_{a_i} ω · ∫_{b_i} η  -  ∫_{b_i} ω · ∫_{a_i} η )
```

The wedge integral of two holomorphic 1-forms on the surface decomposes
into a finite sum of products of single-cycle periods.

## 2. Choice of route

The classical proof uses the polygonal model:

1. Cut `X` along the symplectic basis cycles to obtain the fundamental
   polygon `P = Polygon4g g` (interior `P°` simply connected).
2. On `P°`, take a primitive `F : P° → ℂ` of `ω` (this is exactly
   `lem:primitive-on-polygon`).
3. Then `ω ∧ η = d(F · η)` on `P°` (since `dF = ω` and `dη = 0`).
4. Apply Stokes on the polygon-with-boundary:
   `∫_P ω ∧ η = ∫_P d(F · η) = ∫_∂P F · η`.
5. The boundary `∂P` consists of `4g` arcs identified in pairs.
   For each pair `aᵢ ↔ aᵢ⁻¹`, the values of `F` at corresponding
   parameter `t` differ by the period `∫_{bᵢ} ω` (the monodromy
   accumulated by going around the `bᵢ` cycle).
6. Summing over pairs gives the telescoping `Σ (period · period -
   period · period)`.

This is the *only* mathematically clean route for the no-axiom
formalization: every proposed alternative (Hodge, de Rham + cup
product) ultimately routes through some form of cellular decomposition
+ Stokes on the cells, i.e. equivalent infrastructure.

## 3. Mathlib v4.28.0 inventory

| prerequisite | status | path |
|---|---|---|
| `Polygon4g g` and quotient topology | PRESENT | `Jacobian/Periods/Polygon4g.lean` |
| `lem:primitive-on-polygon` (3 sub-leaves sorry-free) | PARTIAL | `Jacobian/Periods/PrimitiveOnPolygon.lean` |
| `thm:polygonal-model` (homeo `X ≃ₜ Polygon4g g`) | ABSENT (sorry) | `Jacobian/Blueprint/Sec03/PolygonalModel.lean` (depends on `ref/plans/polygonal-model.md` Stage A) |
| `thm:stokes-on-rs-with-boundary` | ABSENT (sorry) | `Jacobian/Blueprint/Sec03/StokesOnRSWithBoundary.lean` (depends on `ref/plans/stokes-on-rs-with-boundary.md`) |
| `integrateTwoForm` (shared with Stokes + hermitian plans) | ABSENT | — |
| Symplectic basis on `H_1(X, ℤ)` | PARTIAL | `JacobianChallenge.Blueprint.Sec03.isSymplecticBasis` (definition only) |
| Path integrals along `H_1` cycles | PRESENT | `Jacobian/Periods/PathIntegralViaCover*` (substantial infrastructure) |
| Exterior derivative `d(F · η) = dF ∧ η + F · dη` | PARTIAL | Mathlib has Leibniz rule for differential forms on normed spaces; manifold version may need a project wrapper |

## 4. Decomposition (7 sub-leaves)

Each leaf gets a stable Lean handle in
`Jacobian/Blueprint/Sec03/BilinearFromStokes.lean`. Many depend on
`thm:polygonal-model` and `thm:stokes-on-rs-with-boundary` umbrellas
that are themselves sorry-bound — those dependencies are inherited.

| # | Lean handle | Class | Sketch | Deps |
|---|---|---|---|---|
| 1 | `wedge_holomorphic_eq_dF_eta` | SHORT | If `dω = 0` (by `lem:holomorphic-form-is-closed`) and `dη = 0`, and `dF = ω`, then on any open subset `ω ∧ η = d(F · η)` (Leibniz: `d(F·η) = dF ∧ η + F · dη = ω ∧ η + 0`). | `lem:holomorphic-form-is-closed`, manifold Leibniz |
| 2 | `pullback_via_polygonalModel` | MEDIUM | Use `polygonal_model X g _` to obtain `homeo : X ≃ₜ Polygon4g g`, then pull `ω` and `η` back to the polygon's interior via the homeomorphism. | `thm:polygonal-model` |
| 3 | `polygon_primitive_F` | SHORT | Apply `lem:primitive-on-polygon` to the pulled-back `ω` to get a holomorphic primitive `F : (Polygon4g g)° → ℂ`. | `lem:primitive-on-polygon` |
| 4 | `wedge_integral_via_stokes_polygon` | HARD | Apply `thm:stokes-on-rs-with-boundary` to the polygon: `∫_{Polygon4g g} ω ∧ η = ∫_{∂(Polygon4g g)} F · η` (using leaves 1–3). | `thm:stokes-on-rs-with-boundary`, leaves 1–3 |
| 5 | `boundary_telescoping_per_pair` | MEDIUM | For each `i ∈ Fin g`, the contribution to `∫_∂P F · η` from the four arcs `aᵢ, bᵢ, aᵢ⁻¹, bᵢ⁻¹` equals `(∫_{aᵢ} ω) · (∫_{bᵢ} η) − (∫_{bᵢ} ω) · (∫_{aᵢ} η)`. The `F` values at paired-side points differ by exactly the symplectic period of `ω` along the *other* generator. | symplectic-basis monodromy combinatorics; uses `mk_a_pair`/`mk_b_pair` from `Polygon4g` |
| 6 | `boundary_integral_eq_period_sum` | SHORT | Sum leaf 5 over `i : Fin g` to get the full bilinear sum on the right-hand side. | leaf 5, `Finset.sum` |
| 7 | `bilinear_from_stokes` (umbrella) | SHORT | Combine 4 + 6 via `wedgeIntegral X ω η = ∫_∂P F · η = Σ (period products)`. | leaves 4, 6 |

## 5. Assembly order

1. Leaf 1 (Leibniz `ω ∧ η = d(F · η)`).
2. Leaf 2 (pullback infrastructure — depends on `polygonal_model` umbrella).
3. Leaf 3 (apply `primitive_on_polygon` — already 3-of-3 sub-leaves sorry-free).
4. Leaf 4 (Stokes on the polygon).
5. Leaf 5 (per-pair telescoping — the genuinely combinatorial step).
6. Leaf 6 (sum over `Fin g`).
7. Leaf 7 (assemble).

## 6. What is genuinely blocked

This theorem is the *paradigm* of "Stokes-derived" identity. Its
discharge is gated on:

- **`thm:polygonal-model`** (Stage A of polygonal-model plan ≈ surface classification, ~3000–5000 LOC).
- **`thm:stokes-on-rs-with-boundary`** (~1800 LOC per existing plan, of which ~400 LOC is the shared `integrateTwoForm` with hermitian-positivity).

Once those two land, leaves 1, 2, 3, 5, 6, 7 are all SHORT/MEDIUM and
~500 LOC total. Leaf 4 is HARD only because it threads Stokes through
chart-pullbacks; ~300 LOC.

**Marginal LOC for this plan (assuming polygonal-model + Stokes are
done):** ~800 LOC.
**Total LOC including dependencies:** ~6000 LOC.

The right characterisation: this theorem is **assembly above a giant
foundation**. It cannot be made smaller without short-circuiting
(opaquely positing the bilinear identity itself, which the project has
explicitly rejected).

## 7. Aristotle packet plan

Only leaves 1, 5, 6, 7 are independently submittable today (leaves
2, 3, 4 wait on polygonal-model and Stokes umbrellas):

| Leaf | Risk | Notes |
|------|------|-------|
| 1 | low | Manifold Leibniz rule. May need a project-local helper if Mathlib's manifold-form Leibniz isn't directly exposed. |
| 5 | medium | The combinatorial telescoping at the polygon's edge identifications. Project-local; uses `Polygon4g.SideRel` constructors directly. The hardest "real math" leaf in this plan; likely worth a multi-round refinement. |
| 6 | low | Linearity of `Finset.sum` over the period-pair contributions. |
| 7 | low | One-line composition. |

Sequencing recommendation: defer until polygonal-model and
Stokes-on-RS-with-boundary plans land their core leaves, then submit
leaves 1, 5, 6, 7 in parallel.

## 8. Companion: `input:riemann-bilinear` umbrella

`input:riemann-bilinear` (sec03) packages this theorem +
`thm:hermitian-positivity` + `thm:period-vectors-full-real-rank` as a
single classical input. Once all three land sorry-free, the umbrella
is a one-line `And.intro` chain.
