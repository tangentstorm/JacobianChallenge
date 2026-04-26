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

Last tick: 2026-04-25 21:52 EDT

```text
Layer                            Bar                    %    Note
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
Project scaffolding              ████████████████████  100%  done
Mathlib inventory                ████████████████████  100%  v4.28.0 audit
Complex torus quotient           ████████████████████  100%  ZLattice bridge sorry-free
Quotient charted-space/manifold  ████████████████████  100%  ChartedSpace + IsManifold sorry-free
Projection (mk) smoothness       ████████████████████  100%  contMDiff_mk
LieAddGroup smoothness           ████████████████████  100%  +, -, LieAddGroup instance
Holomorphic forms                ██████░░░░░░░░░░░░░░   30%  type + module + analyticGenus
Path integration/periods         ██████░░░░░░░░░░░░░░   30%  +Lebesgue radius for chart cover
Abel-Jacobi API                  ░░░░░░░░░░░░░░░░░░░░    0%  pending
Trace/degree/push-pull           ░░░░░░░░░░░░░░░░░░░░    0%  pending
```

```text
Aristotle status
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
Active jobs (ours): 0/5. Aristotle queue still wedged (5 unrelated
                    jobs QUEUED 7h+).
Integrated this tick: nothing from Aristotle.
Local progress this tick: added
                          `Jacobian/Periods/LebesgueChartRadius.lean`
                          (no sorries), the combinatorial input for
                          multi-chart path integration. Statement:
                          for any continuous `γ : C(K, X)` from a
                          compact metric space `K` into a charted
                          space `X`, there exists `δ > 0` such that
                          every `δ`-ball in `K` lands inside some
                          chart's source. ~10-line proof: cover `X`
                          by chart sources (covers because
                          `γ t ∈ (chartAt E (γ t)).source` by
                          `mem_chart_source`), pull back via `γ` to
                          get an open cover of `K`, apply
                          `lebesgue_number_lemma_of_metric`. With
                          this in hand, partitioning `[0, 1]` of
                          mesh `< δ` lets each sub-path land inside
                          a single chart and feed
                          `pathIntegralInChart`.
Complex torus layer: complete. Queue D: chart-local path integral,
                     IntegralOneCycle, period pairing (opaque),
                     period subgroup, and now Lebesgue radius. Next
                     substantive step: combine the Lebesgue radius
                     with a finite [0,1] partition to assemble
                     multi-chart `pathIntegralViaCover`.
```

```text
Current build status
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
Challenge          pass    lake build Jacobian.Challenge
Statement bank     pass    lake build Jacobian.WorkPackets.StatementBank
ComplexTorus       pass    lake build Jacobian.ComplexTorus (umbrella)
IsManifold         pass    lake build Jacobian.ComplexTorus.IsManifold (no sorry)
Witness            pass    lake build Jacobian.ComplexTorus.Witness (no sorry)
MkSmooth           pass    lake build Jacobian.ComplexTorus.MkSmooth (no sorry)
AddSmooth          pass    lake build Jacobian.ComplexTorus.AddSmooth (no sorry)
NegSmooth          pass    lake build Jacobian.ComplexTorus.NegSmooth (no sorry)
LieAddGroup        pass    lake build Jacobian.ComplexTorus.LieAddGroup (no sorry)
HolomorphicForms.Recon pass lake build Jacobian.HolomorphicForms.Recon (recon, no sorry)
HolomorphicForms.CotangentBundle pass lake build Jacobian.HolomorphicForms.CotangentBundle (no sorry)
HolomorphicForms.Defs pass lake build Jacobian.HolomorphicForms.Defs (no sorry)
HolomorphicForms.FiniteDimensional pass lake build Jacobian.HolomorphicForms.FiniteDimensional (no sorry)
Periods.Recon       pass    lake build Jacobian.Periods.Recon (recon, no sorry)
Periods.ChartedForm pass    lake build Jacobian.Periods.ChartedForm (no sorry)
Periods.PathIntegralChart pass lake build Jacobian.Periods.PathIntegralChart (no sorry)
Periods.PathLift   pass    lake build Jacobian.Periods.PathLift (no sorry)
Periods.IntegralOneCycle pass lake build Jacobian.Periods.IntegralOneCycle (no sorry)
Periods.PeriodFunctional pass lake build Jacobian.Periods.PeriodFunctional (opaque pairing)
Periods.LebesgueChartRadius pass lake build Jacobian.Periods.LebesgueChartRadius (no sorry)
```

```text
Next tick priorities
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
1. Combine `exists_lebesgue_radius_chart` with a finite
   `[0, 1]`-partition to define a multi-chart path integral
   `pathIntegralViaCover`. The first version can return the sum of
   chart-local integrals indexed by partition points + chart picks;
   well-definedness (independence of partition) is a follow-up.
2. With multi-chart `pathIntegralViaCover` in hand, the `opaque
   periodPairing` can graduate to a real definition.
3. Independently, attempt the torus sanity check
   (`analyticGenus ℂ (V ⧸ Λ.subgroup) ≥ 1` via constructing a
   non-trivial section).
```
