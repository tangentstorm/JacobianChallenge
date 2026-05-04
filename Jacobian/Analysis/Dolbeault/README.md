# R7 — Dolbeault isomorphism

**Headline.** For a complex manifold `X` and a holomorphic vector
bundle `E`, `H^q_∂̄(X, E) ≅ H^q(X, 𝒪(E))`.  On a Riemann surface
with `E = 𝒪_X`: `H^{0,1}_∂̄(X) ≅ H¹(X, 𝒪_X)`.

**Lean target.**
`JacobianChallenge.Analysis.Dolbeault.dolbeault_overview` in
`Overview.lean`; full realisation lives at
`Jacobian/HolomorphicForms/Serre/Dolbeault.lean`.

**Build.** `lake build Jacobian.Analysis.Dolbeault`

## Classical proof (4 stages)

1. **Dolbeault complex.** `Ω^{p,q}(X)` bigraded forms; `d = ∂ + ∂̄`;
   `∂̄² = 0`; cohomology `H^{p,q}_∂̄`.
2. **∂̄-Poincaré on a polydisk.** Locally, every `∂̄`-closed
   `(p,q)`-form with `q ≥ 1` is `∂̄`-exact.  One-dim case via
   Cauchy–Pompeiu.
3. **Fine resolution.** `0 → Ω^p_X → Ω^{p,0} → Ω^{p,1} → ⋯` is a
   fine resolution of `Ω^p_X`.
4. **Sheaf cohomology via fine resolution.** Therefore
   `H^q(X, Ω^p_X) ≅ H^q_∂̄(X)`.

## Lean plan (sub-leaves under `Overview.lean`)

12 sub-leaves across 4 phases.  Mathlib has neither bigraded forms
(R7-sub-A) nor fine-sheaf machinery on manifolds (R7-sub-C); the
Cauchy–Pompeiu integral exists in Mathlib's complex-analysis.

## Recursive sub-gaps

* **R7-sub-A.** Bigraded forms `Ω^{p,q}` with `∂` / `∂̄`.
  ~600 LOC, **partially shared with R5**.
* **R7-sub-B.** ∂̄-Poincaré on a polydisk.  One-variable: ~80 LOC
  on Cauchy–Pompeiu.  Multivariable: induction; ~250 LOC.
* **R7-sub-C.** Fine sheaves on a smooth manifold + smooth partition
  of unity for sheaves.  ~250 LOC.
* **R7-sub-D.** Sheaf cohomology = cohomology of any fine resolution
  (general derived-functor argument).  ~300 LOC.

## Plain-English

On a complex manifold, forms split by bidegree.  The `∂̄` operator
sends `(p,q)` to `(p,q+1)`.  Its cohomology — the "Dolbeault
cohomology" — is the analytic side.  The algebraic side is sheaf
cohomology of holomorphic forms, the natural language of
Riemann–Roch.  Dolbeault's theorem says these agree.  On a Riemann
surface and `(p,q) = (0,1)`: `H^{0,1}_∂̄(X) ≅ H¹(X, 𝒪_X)` — the
sheaf-side input to Serre duality.

The proof shows the Dolbeault complex is a fine resolution of the
holomorphic-form sheaf.  Locally trivial via the
`∂̄`-Poincaré lemma (one-variable case = Cauchy–Pompeiu).  Mathlib
has the integral; the bundled-bigraded-form package and the
fine-sheaf API need to be built.

## See also

* Blueprint section `subsec:gap-R7-dolbeault` in
  `tex/sections/12-classical-analysis-gaps.tex`.
* Existing top-down sketch `Jacobian/HolomorphicForms/Serre/Dolbeault.lean`.

**Estimated full LOC** (R7 + sub-A + sub-B + sub-C + sub-D): 2200–2900.
