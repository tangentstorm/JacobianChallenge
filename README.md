# Jacobian Challenge

A Lean 4 / Mathlib formalization project targeting the Jacobian variety of a
compact Riemann surface.

The public specification lives in `Jacobian/Challenge.lean` and asks for:

- `genus X` for a compact Riemann surface `X`;
- `Jacobian X` as a compact complex Lie additive group of dimension `genus X`;
- the Abel-Jacobi map `Jacobian.ofCurve`;
- pushforward and pullback maps along holomorphic maps;
- the degree of a holomorphic map of compact Riemann surfaces;
- the identity `pushforward f (pullback f P) = degree f • P`.

Approach: the analytic period-lattice construction
`Jacobian X = H0(X, Ω¹)* / H1(X, Z)`, built up through reusable layers
(complex tori, holomorphic forms, period integration, Abel-Jacobi, degree).

See `plan.md` for the full roadmap, phase breakdown, anti-hack audit, and
delegation strategy for Aristotle.

## Progress Report

Last tick: 2026-04-25 19:33 EDT

```text
Layer                     Bar                    %    Note
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
Project scaffolding       ████████████████████  100%  done
Mathlib inventory         ████████████████████  100%  v4.28.0 audit
Complex torus quotient    ████████████████████  100%  ZLattice bridge sorry-free
Quotient manifold layer   ████████████████████  100%  ChartedSpace + IsManifold sorry-free
Holomorphic forms         ░░░░░░░░░░░░░░░░░░░░    0%  pending
Path integration/periods  ░░░░░░░░░░░░░░░░░░░░    0%  pending
Abel-Jacobi API           ░░░░░░░░░░░░░░░░░░░░    0%  pending
Trace/degree/push-pull    ░░░░░░░░░░░░░░░░░░░░    0%  pending
```

```text
Aristotle status
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
Active jobs (ours): 0/5. Aristotle queue still wedged (same 5
                    unrelated jobs QUEUED 5h+).
Integrated this tick: nothing from Aristotle.
Local progress this tick: added
                          `Jacobian/ComplexTorus/ContDiffAtLocalSectionMk.lean`.
                          Promotes the existing on-set
                          `contDiffOn_localSection_mk` to a pointwise
                          `ContDiffAt ℂ ω` claim at every `x ∈
                          mk ⁻¹' (mk '' Metric.ball w r)`. The trick
                          is to specialize `v₁ := x` so the
                          intersection `Metric.ball x r ∩ <saturation>`
                          becomes a neighborhood of `x` (both factors
                          open and contain `x`); then
                          `ContDiffOn.contDiffAt` finishes the job.
                          ~12 lines, no automation. Build green.
Quotient manifold layer: 100%. LieAddGroup smoothness work in
                         progress — `mk_locally_translate` (last
                         tick) and `contDiffAt_localSection_mk`
                         (this tick) are now both in place. Next
                         step: assemble `ContMDiff (mk V Λ)` via
                         `contMDiffAt_iff_target_of_mem_source` plus
                         the `ContDiffAt` lemma.
```

```text
Current build status
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
Challenge        pass    lake build Jacobian.Challenge
Statement bank   pass    lake build Jacobian.WorkPackets.StatementBank
ComplexTorus     pass    lake build Jacobian.ComplexTorus (with IsManifold)
IsManifold       pass    lake build Jacobian.ComplexTorus.IsManifold (no sorry)
Witness          pass    lake build Jacobian.ComplexTorus.Witness (no sorry)
MkLocallyTranslate pass  lake build Jacobian.ComplexTorus.MkLocallyTranslate (no sorry)
ContDiffAtLocalSectionMk pass lake build Jacobian.ComplexTorus.ContDiffAtLocalSectionMk (no sorry)
```

```text
Next tick priorities
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
1. `Jacobian/ComplexTorus/MkSmooth.lean`: assemble `ContMDiff (mk V Λ)`
   from `contDiffAt_localSection_mk`. Plumbing: pointwise
   `ContMDiffAt`, then `contMDiffAt_iff_target_of_mem_source` with
   `y := mk x` (the chart at `mk x` contains `mk x` by
   `mem_chartAtPoint_source`), then `contMDiffAt_iff_contDiffAt` on
   the source side, then unfold `extChartAt` to expose the
   `localSection_w ∘ mk` shape, then apply `contDiffAt_localSection_mk`.
2. With `mk` smoothness, attack `+` smoothness via the lifting
   `+ ∘ mk² = mk ∘ +`: smooth `+` on `V` followed by smooth `mk`.
3. Same pattern for `-` smoothness; assemble the `LieAddGroup`
   instance.
```
