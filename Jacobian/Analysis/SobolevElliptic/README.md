# R10 — Sobolev spaces of forms + elliptic regularity for the Laplacian

**Headline.** For a compact oriented Riemannian manifold `M` and
`k : ℕ`, the Sobolev space `H^s(Ω^k(M))` is well-defined for every
`s : ℝ`, and the Laplace–Beltrami operator
`Δ : H^{s+2}(Ω^k) → H^s(Ω^k)` is *Fredholm*.  Furthermore every
distributional solution of `Δω = f` with `f` smooth is itself smooth
(*elliptic regularity*).

**Lean target.**
`JacobianChallenge.Analysis.SobolevElliptic.sobolev_elliptic_overview`
in `Overview.lean`.

**Build.** `lake build Jacobian.Analysis.SobolevElliptic`

R10 is the **single largest sub-gap** in the entire eight-node tree
— estimated **2500–4000 LOC**, on the critical path for both R5
(Hodge decomposition) and indirectly R7 (Dolbeault) and R8 (Serre
duality).  Promoted from "R5-sub-B" to its own top-level dep-graph
node because it is shared and substantial.

## Classical content (6 phases)

1. **Distributional / Sobolev framework.**  `H^s(Ω^k)` for `s : ℝ`,
   density of smooth forms, Sobolev embedding `H^s ↪ C^0` for
   `s > n/2`.
2. **Ellipticity of `Δ`.**  Principal symbol `|ξ|² · id` is invertible
   for `ξ ≠ 0`.
3. **Elliptic regularity.**  Garding inequality: smooth forms remain
   smooth after applying `Δ`.
4. **Rellich–Kondrachov.**  `H^{s'} ↪ H^s` is compact for `s' > s`
   on a compact manifold.
5. **Fredholm property.**  Combining 3 + 4: `Δ : H^{s+2} → H^s` is
   Fredholm, with finite-dimensional kernel/cokernel.  Hence
   the Hodge orthogonal decomposition
   `Ω^k = Harm^k ⊕ d(Ω^{k-1}) ⊕ δ(Ω^{k+1})`.
6. **Bochner / Kähler identities.**  On a Kähler manifold, the
   Laplacians for `d`, `∂`, `∂̄` are proportional — refines R10 into
   the R5 bigrading.

## Lean plan (sub-leaves under `Overview.lean`)

15 sub-leaves across 6 phases; Phase 1 alone is ~600 LOC of
distribution-theory and norm construction.  See `Overview.lean` for
the named list.

## Recursive sub-gaps

* **R10-sub-A.** Distribution theory on a smooth manifold.  Mathlib
  has distributions on `ℝ^n` (`Mathlib.Analysis.Distribution.SchwartzSpace`);
  the manifold variant is missing.  ~600 LOC.
* **R10-sub-B.** The `H^s`-norm on `Ω^k(M)`: chart-local construction
  + partition of unity.  ~500 LOC.
* **R10-sub-C.** Garding inequality (Phase 3 prerequisite).  ~300 LOC.
* **R10-sub-D.** Rellich–Kondrachov compactness theorem (Phase 4).
  ~400 LOC.
* **R10-sub-E.** Fredholm-alternative theorem on a compact manifold
  (Phase 5).  ~300 LOC.

## Plain-English

When you ask "does the equation `Δω = f` have a solution?" on a
compact manifold, you face a problem: `Ω^k(M)` (smooth forms) is too
small a space to admit the *abstract* solution operator (the inverse
of `Δ` modulo its kernel).  The standard trick is to enlarge the
space: replace `Ω^k(M)` with the Sobolev space `H^s(Ω^k(M))`, where
`s` measures the number of "weak derivatives" you allow.  In the
larger space, `Δ : H^{s+2} → H^s` becomes a *Fredholm* operator —
its kernel and cokernel are finite-dimensional, its range is closed
— which is exactly what you need to invert it on the orthogonal
complement of the kernel.

The deep result is *elliptic regularity*: even though you allowed
yourself to enlarge the space, the actual solutions of `Δω = f` for
smooth `f` end up being smooth themselves.  So at the end of the
day you can think of `Δ` as a Fredholm operator on smooth forms,
with a finite-dimensional kernel (the harmonic forms) and a smooth
inverse (the *Green operator*) on the orthogonal complement.  This
is what powers Hodge decomposition (R5).

Mathlib v4.28.0 has Sobolev spaces on `ℝ^n` and Schwartz
distributions, but no manifold-level Sobolev theory and no elliptic
regularity for second-order operators on a manifold.  Building this
from scratch is a major undertaking — comparable in scope to
formalizing the basics of Riemannian geometry — and accounts for the
single largest budget item in the eight-gap tree.

## See also

* Blueprint section `subsec:gap-R10-sobolev-elliptic` in
  `tex/sections/12-classical-analysis-gaps.tex`.
* Bottom-up sketch `Jacobian/StageB/{LaplaceBeltrami, HarmonicForms}.lean`.
* Mathlib starting points: `Mathlib.Analysis.Distribution.SchwartzSpace`,
  `Mathlib.Analysis.Calculus.Sobolev`.

**Estimated full LOC** (R10 + sub-A through sub-E): 4500–6500.
