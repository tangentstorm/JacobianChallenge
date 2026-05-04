# R9 — Bundled differential forms `Ω^k(M)` on a smooth manifold

**Headline.** For every smooth manifold `M` modelled on a Banach space
`E` and every `k : ℕ`, there is a bundled `ℝ`-vector space
`Ω^k(M)` of smooth `k`-forms, equipped with `d`, `∧`, pullback, and
integration, all simultaneously linear and natural, satisfying
`d² = 0`, the Leibniz rule, naturality of `f^* ∘ d = d ∘ f^*`, and
Stokes for closed manifolds.

**Lean target.**
`JacobianChallenge.Analysis.BundledForms.bundled_forms_overview` in
`Overview.lean`.

**Build.** `lake build Jacobian.Analysis.BundledForms`

R9 is the *single foundational sub-gap* shared by R4 (de Rham), R5
(Hodge), and R7 (Dolbeault).  Promoted from "R4-sub-A" to its own
top-level dep-graph node so that downstream consumers can depend on
a single, named bundled-form package.

## Classical content (5 phases)

1. **`Ω^k(M)` algebra.**  `Ω^k` is a `C^∞(M, ℝ)`-module; `Ω⁰ = C^∞(M, ℝ)`.
2. **Exterior derivative.**  `d : Ω^k → Ω^{k+1}` ℝ-linear, `d² = 0`.
3. **Wedge product.**  `∧` ℝ-bilinear, graded commutative, Leibniz
   w.r.t. `d`.
4. **Pullback.**  `f^* : Ω^k(N) → Ω^k(M)` ℝ-linear, commutes with
   `d`, functorial in `f`.
5. **Integration.**  `∫_M : Ω^n(M) → ℝ` for compact oriented
   `n`-manifolds; Stokes `∫_M dω = 0` (closed case).

Plus the **bigraded variant** for complex manifolds:
`Ω^k = ⨁_{p+q=k} Ω^{p,q}`, `d = ∂ + ∂̄`.

## Lean plan (sub-leaves under `Overview.lean`)

| Sub-leaf | Phase | Notes |
|---|---|---|
| `bundled_forms_module` | 1 | `AddCommGroup`, `Module ℝ` |
| `bundled_forms_smooth_module` | 1 | `C^∞(M)`-module structure |
| `bundled_forms_omega_zero` | 1 | `Ω⁰ = C^∞(M)` |
| `bundled_forms_d_linear` | 2 | `d` ℝ-linear |
| `bundled_forms_d_sq_zero` | 2 | `d² = 0` |
| `bundled_forms_wedge_bilinear` | 3 | `∧` bilinear |
| `bundled_forms_wedge_anticommutative` | 3 | `α ∧ β = (-1)^{pq} β ∧ α` |
| `bundled_forms_wedge_leibniz` | 3 | Leibniz |
| `bundled_forms_pullback_linear` | 4 | `f^*` ℝ-linear |
| `bundled_forms_pullback_compat` | 4 | `f^* ∘ d = d ∘ f^*` |
| `bundled_forms_pullback_functorial` | 4 | `(g∘f)^* = f^* ∘ g^*` |
| `bundled_forms_integrate` | 5 | `∫_M` for compact oriented |
| `bundled_forms_stokes_closed` | 5 | Stokes (closed manifolds) |
| `bundled_forms_bigraded_decomposition` | 6 | `Ω^k = ⨁ Ω^{p,q}` |
| `bundled_forms_d_splits` | 6 | `d = ∂ + ∂̄` |

## Recursive sub-gaps

* **R9-sub-A.** Bundled tangent / cotangent bundle infrastructure on a
  manifold.  Mathlib has `TangentBundle`; the alternating-form package
  on `T*M` is missing.
* **R9-sub-B.** Smooth-section infrastructure for a vector bundle.
  `Mathlib.Geometry.Manifold.VectorBundle.SmoothSection` exists; the
  alternating-form variant is not yet packaged.
* **R9-sub-C.** Chart-local description: in a chart, `Ω^k(M)`
  restricts to alternating `k`-multilinear maps on `ℝ^n`, with `d`
  given by partial derivatives.

## Plain-English

The simplest object in differential geometry is the smooth function
on a manifold — that's `Ω⁰(M)`.  One step up is the smooth `1`-form,
which at each point pairs against tangent vectors to give a number;
that's `Ω¹(M)`.  Higher `k` packs alternating-multilinear data.
The whole tower `Ω⁰ → Ω¹ → Ω² → ⋯` carries the exterior derivative
`d`, the wedge product `∧`, pullback by smooth maps, and (in top
degree on a compact oriented manifold) integration.  These four
operations interact via the standard identities that make differential
forms the universal language of integration on manifolds.

Mathlib v4.28.0 has the underlying machinery — manifold derivative
(`MFDeriv`), alternating multilinear maps, partition-of-unity — but
not the integrated bundled-form package.  R9 is what you need to
state precisely "the de Rham complex of `M`," "the exterior algebra
of `M`," "the Stokes formula on `M`."  Without R9, every theorem
about forms on a manifold has to talk around the missing object.
~400–600 LOC for a complete API; foundational for R4, R5, and R7
simultaneously.

## See also

* Blueprint section `subsec:gap-R9-bundled-forms` in
  `tex/sections/12-classical-analysis-gaps.tex`.
* Bottom-up sketch `Jacobian/StageB/DifferentialForms.lean` (which
  this Overview imports and extends).

**Estimated full LOC** (R9 + sub-A + sub-B + sub-C): 800–1200.
