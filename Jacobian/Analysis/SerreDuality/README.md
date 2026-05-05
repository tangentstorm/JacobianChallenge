# R8 — Serre duality on a compact Riemann surface

**Headline.** For a compact Riemann surface `X` and coherent sheaf
`F`, the cup-product / trace pairing
`H^q(X, F) × H^{1-q}(X, ℋom(F, K_X)) → H¹(X, K_X) → ℂ`
is non-degenerate.  In particular `H¹(X, 𝒪_X) ≅ H⁰(X, K_X)^∨`
forces `dim H¹(X, 𝒪_X) = g`.

**Lean target.**
`JacobianChallenge.Analysis.SerreDuality.serre_duality_overview` in
`Overview.lean`; full realisation at
`Jacobian/HolomorphicForms/SerreDualityRS.lean`.

**Build.** `lake build Jacobian.Analysis.SerreDuality` — currently
**0 sorry / 0 error** on the pinned Mathlib v4.28.0 toolchain.

R8 is the **most-developed** of the eight gaps: ~32 files under
`Jacobian/HolomorphicForms/Serre/` decompose `serre_duality_rs` into
~80 named sub-leaves.

## Honest implementation status

* **Build is sorry-free, mathematical content is not.** Most leaves
  under `Jacobian/HolomorphicForms/Serre/` and the new
  `ResidueChain.lean` are placeholder forwards (`True := trivial`,
  or forwards to other placeholders).  The dependency shape is
  fixed; no real harmonic / Čech / residue analysis is in place.
* **The Subsingleton bridge.** The Round-13 placeholder
  `harmonicForms = PUnit` with `harmonicForms_to{H0,H1} = 0` makes
  the surjectivity sub-leaves (`harmonicForms_to{H0,H1}_surjective`)
  logically equivalent to `Subsingleton (RSSheafCohomology X F q)`.
  The build is sorry-free because we add the `Subsingleton` instance
  argument, prove surjectivity from it, and propagate it up the
  chain (`Dolbeault → HodgePairing → Nondegeneracy → DatumExists →
  SerreDualityRS → Overview`).
* **Backout when R5 + R7 land.** When real harmonic-form theory is
  in place, every `[Subsingleton (RSSheafCohomology …)]` argument
  must be removed (otherwise the chain becomes vacuous on
  positive-genus surfaces).  Concretely:
  `git grep -n "Subsingleton.*RSSheafCohomology" Jacobian/`
  enumerates the full backout list.  Files that need genuine
  rewrites at the same time: `HarmonicForms.lean`, `L2Pairing.lean`
  (the three vacuous witness theorems), `FiniteDimInstances.lean`.

## Classical proof (4 stages)

1. **Dualizing sheaf.** `K_X = Ω¹_X`, line bundle.  `ℋom(F, K_X)`,
   the canonical Serre dual.
2. **Trace map.** Residue map at each point; aggregate via Čech to
   `tr : H¹(X, K_X) → ℂ`.  Residue theorem ⇒ `tr` well-defined and
   isomorphism.
3. **Cup-product pairing.** Cup `∪`, evaluation `F ⊗ ℋom(F,K_X) → K_X`,
   trace ⇒ pairing into `ℂ`.
4. **Non-degeneracy via harmonic forms.** Identify both sides with
   harmonic spaces (R5 + R7); pairing realises `L²` inner product;
   positive-definite ⇒ non-degenerate.

## Lean plan (sub-leaves under `Overview.lean`)

13 phase-named sub-leaves (R8.1.1–R8.5.3) summarising the existing
~80-leaf decomposition tree.  See the 32-file Serre directory for
finer-grained obligations.

## Recursive sub-gaps

* **R8-sub-A.** Sheaf cohomology of an analytic line bundle on a
  Riemann surface.  Sketched at
  `Jacobian/HolomorphicForms/SheafCohomologyRS.lean`.  ~600 LOC.
* **R8-sub-B.** Cup product on Čech cohomology.  Mathlib has the
  simplicial cup product; Čech needs porting.  ~300 LOC.
* **R8-sub-C.** Residue theorem on a compact Riemann surface.
  ~250 LOC; depends on Stokes on a Riemann surface with boundary.
  Now decomposed in two more refinement rounds: blueprint chain D
  passes `srt-r6 ... srt-r10` (Round 2: cut-disk manifold + Stokes
  via Mathlib's box divergence theorem) and `srt-r11 ... srt-r15`
  (Round 3: distributional `∂̄(1/(πz)) = δ₀` via Cauchy–Pompeiu +
  chart-local Cauchy residue via `Complex.circleIntegral_one_div_z`).
  Lean stubs in `ResidueChain.lean`.
* **R8-sub-D.** `L²`-realisation of the Serre pairing via harmonic
  forms.  Bridges R5 + R7 + R8.  ~200 LOC.

## Plain-English

Serre duality is a magical identity.  On a compact Riemann surface,
`H¹(X, 𝒪_X)` is the dual vector space to `H⁰(X, K_X) = `
holomorphic 1-forms — explicitly paired by an integration on `X`.
In particular both sides have dimension `g`.  This is the
key ingredient in Riemann–Roch (otherwise an inequality, Serre
upgrades it to equality) and the bridge identifying the analytic
Jacobian with `Pic⁰(X)`.

The proof: trace via residues; cup-product pairing using the cup
product on Čech and the natural evaluation map; identify both sides
with harmonic forms via R5 + R7; harmonic pairing = `L²` pairing,
positive-definite, non-degenerate.

R8 is the most-developed gap: ~32 files already sketch the proof
tree.  Many leaves remain sorry, several (the `L²`-bridge to R5 + R7,
the residue theorem) are themselves non-trivial sub-gaps.

## See also

* Blueprint section `subsec:gap-R8-serre` in
  `tex/sections/12-classical-analysis-gaps.tex`.
* The 32-file Serre tree at `Jacobian/HolomorphicForms/Serre/`.
* Plan: `ref/plans/serre-duality-rs.md`.

**Estimated full LOC** (R8 + sub-A + sub-B + sub-C + sub-D, modulo
R5 + R7): 3300–4300.
