# R4 — De Rham theorem

**Headline.** For a smooth manifold `M`,
`H^k_dR(M, ℂ) ≅ H^k_sing(M, ℂ)` via integration of forms over
chains.

**Lean target.** `JacobianChallenge.Analysis.DeRham.deRham_overview`
in `Overview.lean`; full realisation will replace
`StageB.deRham_theorem`.

**Build.** `lake build Jacobian.Analysis.DeRham`

## Classical proof (4 phases, Bott–Tu route)

1. **Differential-form package.** `Ω^k(M)`, `d`, `∧`, pullback.
2. **Integration of forms.** Smooth singular `k`-simplex; Stokes for
   one simplex; smooth-singular subcomplex is a quasi-isomorphism.
3. **Comparison map.** Integration descends to cohomology, natural,
   compatible with cup product.
4. **Isomorphism via good covers.** Both theories trivialise on
   contractibles; both satisfy Mayer–Vietoris; finite-good-cover
   induction + five-lemma + colimit gives the iso.

## Lean plan (sub-leaves under `Overview.lean`)

| Sub-leaf | Phase | Status |
|---|---|---|
| `deRham_omega_k_module` | 1 | placeholder; R4-sub-A |
| `deRham_exterior_derivative_squared_zero` | 1 | placeholder |
| `deRham_pullback_compat` | 1 | placeholder |
| `deRham_wedge_leibniz` | 1 | placeholder |
| `deRham_smooth_singular_simplex` | 2 | placeholder |
| `deRham_integration_simplex` | 2 | placeholder |
| `deRham_stokes_simplex` | 2 | placeholder; R4-sub-B |
| `deRham_smooth_singular_quasi_iso` | 2 | placeholder |
| `deRham_integration_cohomology_map` | 3 | placeholder |
| `deRham_integration_natural` | 3 | placeholder |
| `deRham_compat_cup` | 3 | placeholder |
| `deRham_both_satisfy_homotopy_invariance` | 4 | placeholder |
| `deRham_mayer_vietoris` | 4 | placeholder |
| `deRham_good_cover_exists` | 4 | placeholder; R4-sub-C |
| `deRham_five_lemma_induction` | 4 | placeholder |

## Recursive sub-gaps

* **R4-sub-A.** Bundled `Ω^k(M)` as a `C^∞(M)`-module with `d`,
  `∧`, pullback all simultaneously linear and natural.  ~400 LOC.
  **Shared with R5 and R7.**
* **R4-sub-B.** Smooth singular chains + Stokes on a smooth `k`-simplex.
  ~300 LOC building on Mathlib's measure-theoretic Stokes for boxes.
* **R4-sub-C.** Good-cover existence on a smooth manifold (needs
  Riemannian metric + convex-radius lemma).  ~250 LOC plus shared
  Riemannian-metric infrastructure (~500 LOC, **shared with R5**).

## Plain-English

Two ways to count holes in a smooth manifold.  Forms way: closed
modulo exact (`d²=0` makes the quotient meaningful).  Chains way:
cycles modulo boundaries (`∂²=0`).  De Rham's theorem says these are
naturally isomorphic, the iso being integration: pair a form with a
cycle, compute a number.  Without de Rham, analytic-genus and
topological-genus have no meaningful comparison.  The proof is
substantial because Mathlib has no bundled differential-form package
yet (R4-sub-A is foundational for three of the eight gaps).

## See also

* Blueprint section `subsec:gap-R4-de-rham` in
  `tex/sections/12-classical-analysis-gaps.tex`.
* Bottom-up sketch `Jacobian/StageB/DeRhamComparison.lean`.

**Estimated full LOC** (R4 + sub-A + sub-B + sub-C): 2500–3500.
