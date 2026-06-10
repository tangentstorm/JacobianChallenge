# Worker jc0 — Plan: Genus-Zero Uniformization (#231 → #232/#233/#234)

Discharge the 3 remaining genus-zero sorries. The local-analytic uniformization
substrate is **already built and sorry-free** (see "Done substrate" below);
the goal is now to assemble the biholomorphism from it and derive the single-pole
data. Multi-commit, top-down. Branch off `origin/main`.

## 0. Allowed write scope
* **Write:** `Jacobian/HolomorphicForms/GenusZeroClassification.lean`,
  `Jacobian/HolomorphicForms/MeromorphicToBranchedCover.lean`, new helper files
  under `Jacobian/HolomorphicForms/`.
* **Forbidden:** `Jacobian/Challenge.lean`. Avoid other workers' active files.

## 1. The 3 sorries (re-confirm with `scripts/list-sorries.py --text` each cycle)
1. `exists_biholomorph_onePoint_of_genus_zero` — GenusZeroClassification.lean (#232)
2. `exists_biholomorph_onePoint_of_analyticGenus_zero` — MeromorphicToBranchedCover.lean (#233)
3. `complexSimplePolePrincipalPart_of_biholomorph_onePoint` — MeromorphicToBranchedCover.lean (#234)

## 2. Done substrate (sorry-free — build on these, don't redo)
* Chart-ball power-series package; open-image / nonzero-derivative local inverse;
  small-ball local injectivity; local normalized ball.
* Normal-family / Montel: locally-uniform convergence, Cauchy derivative
  estimates, equicontinuity, Arzelà–Ascoli compact closure, Montel subsequence
  extraction, locally-uniform analytic limit, center-normalization preservation.
* Two-chart `OnePoint ℂ` transition; global gluing data scaffold; canonical
  forward gluing map (forward existence + chart-expression discharged).
* `exists_contMDiff_homeomorph_to_onePointCx` is sorry-free and projects from the
  single high-level provider `exists_biholomorph_onePoint_of_genus_zero` (#232),
  which is the tracked GenusZero root.

## 3. Commit sequence

### Milestone 0 — Map the genus-zero blueprint to Mathlib (FIRST)
Make the genus-zero subtree of the blueprint complete: every node bottoms out in
a green project node or a named Mathlib lemma. The proof skeleton is already
surveyed in goal.md (§ FIRST JOB) — ~59 sorry-free substrate lemmas to turn into
`\lean{}`-tracked blueprint nodes wired with `\uses`.
- [x] **0a.** Audit the current genus-zero nodes in
      `tex/sections/04-branched-covers-genus-zero.tex`: which already exist,
      which sorry nodes (#232/#233/#234) float without a proof skeleton.
- [x] **0b.** Add blueprint lemma nodes for the GREEN substrate clusters
      (Liouville/vanishing, chart-coefficient extraction, inversion/decay,
      reverse-direction transport, forward gluing assembly), each with a real
      `\lean{}` and `\uses` edges down to green nodes or Mathlib citations.
      Confirm each cited decl is sorry-free (`scripts/list-sorries.py --text`,
      `#print axioms`) before colouring it green — do not fake a green node.
- [x] **0c.** Wire #232/#233/#234 so their only remaining orange/uncoloured
      dependency is the single genuine uniformization gap. Build the blueprint
      (`bash scripts/build-blueprint.sh` — fails on unresolved `\uses`/`\ref`)
      and the audit (`scripts/blueprint_audit.py`); both must pass. Commit.
- [x] **0d.** The resulting tree is the authoritative plan for Milestones A–C:
      the named provider you must still prove is now the lone frontier node.

### Milestone A — #232: the uniformization root (the hard one)
- [ ] **A1.** Assemble `exists_biholomorph_onePoint_of_genus_zero` from the
      substrate: select a finite cover of normalized local Montel-limit charts
      (the `GenusZeroNormalizedMontelPatchSelector` shape), glue through the
      two-chart `OnePoint ℂ` atlas, and prove the resulting map and its inverse
      are `ContMDiff`. If the patch-family existence is the genuine analytic
      gap, isolate it as the narrowest named provider and prove the gluing on
      top (provider discipline).
- [x] **A1.1.** Replace the broad public #232 `sorry` with the narrower provider
      `genusZeroGlobalGluingData_of_homeomorph_onePoint :
      Nonempty (GenusZeroGlobalGluingData X)`, then prove
      `exists_biholomorph_onePoint_of_genus_zero` by applying
      `GenusZeroGlobalGluingData.exists_contMDiff_homeomorph` to that data.
      This should move the reachable genus-zero root to the named provider with
      no net new sorries.
- [x] **A1.2.** Replace the gluing-data provider `sorry` with an even narrower
      normalized-selector provider
      `genusZeroNormalizedMontelPatchSelector_of_homeomorph_onePoint :
      Nonempty (GenusZeroNormalizedMontelPatchSelector X)`, then prove
      `genusZeroGlobalGluingData_of_homeomorph_onePoint` by assembling
      `GenusZeroGlobalGluingData` from the selector using the existing
      `genusZeroGlobalGluing_*` green lemmas. This should move the reachable
      genus-zero root to the selector provider with no net new sorries.
- [x] **A1.3a.** Add the graph-visible Montel selector obligation spine beneath
      `genusZeroNormalizedMontelPatchSelector_of_homeomorph_onePoint`, using
      real `\lean{}` declarations only and decomposing the patch-family branch
      down to the existing green chart-ball normal-family substrate plus the
      precise open finite global assembly provider.
- [x] **A1.3b.** Refine the finite Montel patch-family assembly node into
      graph-visible sub-obligations for local patch realization, coherent
      local selectors, chart-ball source domains, two-chart source/target cover,
      normalized-limit two-chart cover, and final `GenusZeroGlobalPatchFamily`
      packaging, using only real Lean declarations in `\lean{}`.
- [x] **A1.3c.** Prove the green target-side cover helper
      `onePointCx_identity_or_inversionChart_source :
      ∀ y : OnePoint ℂ, y ∈ identityChart.source ∨ y ∈ inversionChart.source`
      and update the two-chart target-cover blueprint node to cite it as
      `\leanok`.
- [x] **A1.3d.** Prove
      `GenusZeroTwoChartMontelCoverSelector.target_chart_cover_global`, deriving
      the `GenusZeroGlobalPatchFamily.target_chart_cover`-shaped witness from
      the two-chart cover selector, and update the global patch-family
      packaging blueprint node to cite it.
- [x] **A1.3e.** Prove
      `GenusZeroTwoChartMontelCoverSelector.patch_cover_global`, deriving the
      `GenusZeroGlobalPatchFamily.patch_cover`-shaped witness from the two-chart
      cover selector, and update the global patch-family packaging blueprint
      node to cite it.
- [x] **A1.3f.** De-circularize the Montel selector blueprint plan: remove
      selector-field and repackager projections from the graph, delete/demote
      fake-green packaging nodes, and restate the #232 selector frontier as one
      honest construction node followed by property obligations depending on
      that construction.
- [x] **A2.** `lake build Jacobian.HolomorphicForms.GenusZeroClassification` clean;
      `#print axioms exists_biholomorph_onePoint_of_genus_zero` shows no `sorryAx`
      beyond any deliberately-isolated provider; `Jacobian.Solution` green.

### Milestone B — #233: analytic-genus-zero packaging
- [x] **B1.0.** Split the #232 topological-homeomorphism-to-biholomorphism
      interface into an upstream helper file under `Jacobian/HolomorphicForms/`
      so `MeromorphicToBranchedCover.lean` can consume
      `exists_biholomorph_onePoint_of_genus_zero` without importing
      `GenusZeroClassification.lean` and creating an import cycle. Preserve all
      public theorem names/signatures, introduce no new sorries, and do not
      change #233's body yet.
- [x] **B1.** `exists_biholomorph_onePoint_of_analyticGenus_zero`: from
      `analyticGenus ℂ X = 0`, obtain the topological `X ≃ₜ OnePoint ℂ` and feed
      it to #232 to get the biholomorphism. Thin layer on top of A.

### Milestone C — #234: simple-pole principal part from the biholomorphism
- [x] **C1.0.** Replace the broad #234 `sorry` in
      `complexSimplePolePrincipalPart_of_biholomorph_onePoint` with a narrower
      explicit pullback-data provider for a target `OnePoint ℂ` simple-pole
      coordinate at `e P` and its biholomorphic pullback along `e`. Preserve the
      public theorem signature, introduce no net new sorries, and keep the
      route independent of the circular fixed-pole/Riemann--Roch chain.
- [x] **C1.1.** Tighten the #234 pullback provider so the source lift is
      definitionally `targetLift ∘ e`, rather than a separately chosen
      function plus an equality proof. Introduce a narrower target-plus-transport
      facts provider carrying `targetPrincipalPart` and
      `HasComplexSimplePolePrincipalPart (targetLift ∘ e) P`; rebuild
      `BiholomorphOnePointSimplePolePullbackData` from it with `sourceLift_eq := rfl`.
      Preserve the public theorem signature, introduce no net new sorries, and
      keep the route independent of the circular fixed-pole/Riemann--Roch chain.
- [x] **C1.2.** Make the target simple-pole coordinate explicit. Add a local
      `onePointSimplePoleCoordinate (Q : OnePoint ℂ) : OnePoint ℂ → ℂ`
      definition using a concrete Möbius-style coordinate with pole at `Q`, and
      tighten the #234 facts provider so `targetLift` is definitionally this
      coordinate at `e P`. Preserve the public theorem signature, introduce no
      net new sorries, and keep the route independent of the circular
      fixed-pole/Riemann--Roch chain.
- [x] **C1.3.** Name the source pullback coordinate explicitly. Add a local
      `biholomorphPulledBackSimplePoleCoordinate (P : X) (e : X ≃ₜ OnePoint ℂ) :
      X → ℂ` definition as `onePointSimplePoleCoordinate (e P) ∘ e`, and tighten
      the #234 facts/data providers so all source principal-part fields and
      returned source lifts use this named coordinate definitionally. Preserve
      the public theorem signature, introduce no net new sorries, and keep the
      route independent of the circular fixed-pole/Riemann--Roch chain.
- [x] **C1.4.** Expose the exact target/source principal-part fields. Replace
      the remaining #234 facts-provider `sorry` with a narrower field-facts
      provider carrying the eight concrete obligations for
      `HasComplexSimplePolePrincipalPart` on
      `onePointSimplePoleCoordinate (e P)` and
      `biholomorphPulledBackSimplePoleCoordinate P e` (meromorphic everywhere,
      continuous one-point extension, order one, and punctured modulus
      divergence for each). Rebuild `BiholomorphOnePointSimplePolePullbackFacts`
      sorry-free from those fields. Preserve public theorem signatures,
      introduce no net new sorries, and keep the route independent of the
      circular fixed-pole/Riemann--Roch chain.
- [x] **C1.5a.** Correct the finite-pole branch of
      `onePointSimplePoleCoordinate` so the value at `∞` is the continuous
      value `0`, and add small sorry-free normal-form/evaluation lemmas for
      the explicit target coordinate. Do not move the #234 frontier yet; this
      is a prerequisite cleanup after the reverted C1.5 proof attempt exposed
      the old finite-pole normal form as mathematically wrong.
- [x] **C1.5b.** Expose sorry-free normal forms for
      `onePointExtend (onePointSimplePoleCoordinate Q) Q`, split into the
      `Q = ∞` and finite-pole cases. Keep this as a support step for the
      target-side continuity/order proof; do not move the #234 frontier yet.
- [x] **C1.5c.** Package the pointwise target-extension normal forms into
      whole-function identities: the `Q = ∞` one-point extension is `id`, and
      the finite-pole extension is the concrete sphere map sending `∞ ↦ 0`,
      `a ↦ ∞`, and `z ≠ a ↦ ↑((z - a)⁻¹)`. Keep this as a support step for
      target continuity/order proofs; do not move the #234 frontier yet.
- [x] **C1.5d.** Prove the target-side continuity field helper
      `Continuous (onePointExtend (onePointSimplePoleCoordinate Q) Q)` for
      every `Q : OnePoint ℂ`, using the C1.5c whole-function normal forms and
      local continuity lemmas for the finite-pole case. Keep this as one
      target-field support lemma; do not move the #234 frontier yet.
- [x] **C1.5e.** Thread the target continuity helper into the #234 field-facts
      assembly by removing `target_continuous_extension` from the remaining
      provider structure and filling that target field directly from
      `continuous_onePointExtend_onePointSimplePoleCoordinate`. This should
      narrow the reachable #234 frontier from eight fields to seven while
      preserving public theorem signatures.
- [x] **C1.5f.** Prove the target-side punctured-neighborhood modulus
      divergence helper
      `Filter.Tendsto (fun q => ‖onePointSimplePoleCoordinate Q q‖)
      (nhdsWithin Q ({Q}ᶜ : Set (OnePoint ℂ))) Filter.atTop` for every
      `Q : OnePoint ℂ`, using the explicit coordinate normal forms and local
      one-point/complex filter lemmas. Keep this as a support helper; do not
      move the #234 frontier yet.
- [x] **C1.5g.** Thread the target modulus-divergence helper into the #234
      field-facts assembly by removing `target_modulus_tendsto` from
      `BiholomorphOnePointSimplePolePullbackFieldFacts` and filling the target
      `HasComplexSimplePolePrincipalPart.modulus_tendsto` field directly from
      `tendsto_norm_onePointSimplePoleCoordinate_atTop (e P)`. This should
      narrow the reachable #234 frontier from seven fields to six while
      preserving public theorem signatures.
- [x] **C1.5h.** Prove a local target-side order-one helper for the explicit
      simple-pole coordinate:
      `mapAnalyticOrderAt (onePointExtend (onePointSimplePoleCoordinate Q) Q) Q = 1`
      for every `Q : OnePoint ℂ`. Use the existing target extension normal
      forms and the `OnePoint ℂ` chart/inversion infrastructure. Keep this as a
      support helper only; do not thread it into the six-field provider yet.
- [x] **C1.5i.** Thread the target order-one helper into the #234 field-facts
      assembly by removing `target_orderAt_pole` from
      `BiholomorphOnePointSimplePolePullbackFieldFacts` and filling the target
      `HasComplexSimplePolePrincipalPart.orderAt_pole` field directly from
      `mapAnalyticOrderAt_onePointSimplePoleCoordinate_pole (e P)`. This should
      narrow the reachable #234 frontier from six fields to five while
      preserving public theorem signatures.
- [x] **C1.5j.** Prove the target-side meromorphicity helper
      `∀ q, MeromorphicAtX (onePointSimplePoleCoordinate Q) q` for every
      `Q : OnePoint ℂ`, using the explicit coordinate normal forms in the
      identity and inversion charts. Keep this as a support helper only; do
      not thread it into the five-field provider yet.
- [x] **C1.5k.** Thread the target meromorphicity helper into the #234
      field-facts assembly by removing `target_meromorphic_everywhere` from
      `BiholomorphOnePointSimplePolePullbackFieldFacts` and filling the target
      `HasComplexSimplePolePrincipalPart.meromorphic_everywhere` field directly
      from `meromorphicAtX_onePointSimplePoleCoordinate (e P)`. This narrows
      the reachable #234 frontier to the four source transport fields.
- [x] **C1.5l.** Prove and thread the source meromorphicity helper
      `meromorphicAtX_biholomorphPulledBackSimplePoleCoordinate`, transporting
      target meromorphicity through the biholomorphism and removing
      `source_meromorphic_everywhere` from
      `BiholomorphOnePointSimplePolePullbackFieldFacts`. This narrows the
      reachable #234 frontier to the three remaining source transport fields:
      continuity of the one-point extension, order one, and punctured modulus
      divergence.
- [x] **C1.5m.** Prove and thread the source one-point-extension continuity
      helper `continuous_onePointExtend_biholomorphPulledBackSimplePoleCoordinate`,
      identifying the source extension with the target extension composed with
      the biholomorphism and removing `source_continuous_extension` from
      `BiholomorphOnePointSimplePolePullbackFieldFacts`. This narrows the
      reachable #234 frontier to the two remaining source transport fields:
      order one and punctured modulus divergence.
- [ ] **C1.5.** Prove the target-side `OnePoint ℂ` simple-pole field facts
      for `onePointSimplePoleCoordinate Q`, then move the remaining #234
      frontier from the eight-field provider to a source-transport-only
      provider for the four pulled-back fields along the biholomorphism `e`.
      Preserve public theorem signatures, introduce no net new sorries, and
      keep the route independent of the circular fixed-pole/Riemann--Roch chain.
- [ ] **C1.** `complexSimplePolePrincipalPart_of_biholomorph_onePoint`: pull the
      standard simple-pole coordinate on `OnePoint ℂ` back along the
      biholomorphism `e : X ≃ₜ OnePoint ℂ`; prove the pulled-back coordinate is
      meromorphic everywhere, extends to `∞` at `P`, has analytic order one in
      the inversion chart, and diverges in norm near `P` —
      `∃ F, HasComplexSimplePolePrincipalPart F P`. NOT from the circular RR
      chain. The sibling `singlePoleAnalyticData_of_biholomorph_onePoint` is
      already sorry-free on top of this.

### Path B — Riemann-Roch fixed-pole construction decomposition
- [x] **B-RR0.** Decompose the direct RR single-pole-map route in the blueprint
      without attempting the core proof. The spine is now explicit in
      `tex/sections/04-branched-covers-genus-zero.tex`:
      `analyticGenus ℂ X = 0` -> `dim L([P]) = 2` ->
      a nonconstant `f ∈ L([P])` exists -> the pole divisor is exactly `[P]` ->
      package the map as
      `genusZero_fixedPole_rr_effectiveGranular_provider`.

      The Lean-facing spine is:
      * hard core placeholder:
        `genusZero_riemannRoch_difference_eq_two`
        (currently only `∃ ℓP ℓKP : ℕ, (ℓP : ℤ) - (ℓKP : ℤ) = 2`, not a real
        `finrank` theorem for a concrete RR space);
      * supporting residual-vanishing placeholder:
        `genusZero_riemannRoch_K_minus_point_dim_zero`;
      * intended linear-algebra extraction:
        `riemannRochSpace_dim_ge_two_implies_nonconstant_meromorphic`
        (currently projects from the fixed-pole provider, so it still needs to
        be rebuilt from a genuine RR space dimension theorem);
      * pole-exactness support:
        `genusZero_poleDivisor_eq_point_of_nonconstant_mem_L_point`;
      * open construction frontier:
        `genusZero_fixedPole_rr_effectiveGranular_provider`.

- [ ] **B-RR1. Hard core.** Build the actual finite-dimensional
      Riemann-Roch space API for `L([P])` and prove the dimension count
      `dim L([P]) = 2` from genus zero. This requires an honest
      divisor-compatible vector-space model for RR sections; the old
      `riemannRochSpace : Submodule ℂ MeromorphicFunctionType` was removed
      because pointwise `OnePoint ℂ` addition cannot model pole cancellation.
      No current theorem in `RiemannRoch.lean` provides the real formula
      `dim L(D) - dim L(K-D) = deg D + 1 - g`; the existing
      `genusZero_riemannRoch_*` declarations are structural placeholders, not
      a proved RR dimension formula.

- [ ] **B-RR2. Independent support leaf.** Prove the negative-degree/residual
      vanishing input for `K - [P]`: in genus zero, sections of `L(K-[P])`
      vanish. This should be independent once the section model for `K-[P]` is
      fixed.

- [x] **B-RR2.1. Germ-Order Bridge.** The carrier `MeromorphicFunctionWithDivisors`
      records an `order` field for bookkeeping, but lacks the bridge to actual
      analytic germ behavior. We will state an exact open bridge relating `f.order P`
      to `orderAt` of the function's finite lift or germ, and use this to prove
      `toMap_eq_infty_of_poleDivisor_pos`. (Sorry count 4 → 4).

- [ ] **B-RR3. Independent support leaf.** Prove the pure linear-algebra
      extraction: if constants embed as a one-dimensional subspace of `L([P])`
      and `finrank L([P]) = 2`, then there exists a nonconstant
      `MeromorphicMapToSphere` in `L([P])`.

- [ ] **B-RR4. Independent support leaf.** Connect a constructed nonconstant
      RR element to the direct granular provider: exact pole divisor `[P]`,
      effective zero divisor, meromorphic finite lift, and order-one pole. The
      pole-exactness theorem already exists; the remaining analytic Laurent
      fields must come from the actual RR section construction, not from
      `genusZero_fixedPole_rrSection_nonempty`, the biholomorphism route, or
      any prepackaged single-pole data.

### Milestone D — Acceptance
- [ ] **D.** `lake build Jacobian.Solution` clean; `scripts/list-sorries.py --text`
      shows the 3 gone with no new sorries; `#print axioms` on the genus-zero
      route confirms no stray axiom/sorry; run the standard audits
      (`fix-sorries.py`, `audit-sorries.py`, `blueprint_audit.py`).

## 4. Notes / hazards
* **Circularity (critical):** the genus-zero single-pole content must NOT use
  `genusZero_pointRRSection_meromorphic_getD_exists`,
  `genusZero_fixedPole_analyticRRWitness_nonempty`,
  `genusZero_fixedPole_simplePoleRRSection_nonempty`,
  `genusZero_fixedPole_rrSection_nonempty`, or
  `genusZero_pointRRSection_outside_constants_exists` — that chain routes through
  the very root it would prove. Derive #234 from the biholomorphism (#232) instead.
* `OnePoint ℂ` ChartedSpace/IsManifold already exist — reuse, don't rebuild.
* Per proving-guide: never declare blocked on a Mathlib gap — build the missing
  helper locally in `Jacobian/HolomorphicForms/`.
* Net reachable-sorry change for the goal: −3.
