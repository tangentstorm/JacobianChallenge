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

Last tick: 2026-04-25 20:14 EDT

```text
Layer                          Bar                    %    Note
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
Project scaffolding            ████████████████████  100%  done
Mathlib inventory              ████████████████████  100%  v4.28.0 audit
Complex torus quotient         ████████████████████  100%  ZLattice bridge sorry-free
Quotient charted-space/manifold ████████████████████ 100%  ChartedSpace + IsManifold sorry-free
Projection (mk) smoothness     ████████████████████  100%  contMDiff_mk
LieAddGroup smoothness         ████████████████████  100%  +, -, LieAddGroup instance
Holomorphic forms              ░░░░░░░░░░░░░░░░░░░░    0%  pending
Path integration/periods       ░░░░░░░░░░░░░░░░░░░░    0%  pending
Abel-Jacobi API                ░░░░░░░░░░░░░░░░░░░░    0%  pending
Trace/degree/push-pull         ░░░░░░░░░░░░░░░░░░░░    0%  pending
```

```text
Aristotle status
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
Active jobs (ours): 0/5. Aristotle queue still wedged (5 unrelated
                    jobs QUEUED 6h+).
Integrated this tick: nothing from Aristotle.
Local progress this tick: 🎉🎉 **LieAddGroup instance lands**.
                          Three new files (all sorry-free):
                          - `NegSmooth.lean`: `ContMDiff` of
                            `q ↦ -q` via the chart-source
                            decomposition `Neg.neg = mk ∘ Neg.neg ∘
                            chart` (each step smooth) plus `mk_neg`
                            congr.
                          - `AddSmooth.lean`: `ContMDiff` of
                            `(q1, q2) ↦ q1 + q2` via the
                            same pattern with the product chart:
                            `Add = mk ∘ + ∘ (chart1 × chart2)` plus
                            `mk_add` congr.
                          - `LieAddGroup.lean`: assembles the
                            `ContMDiffAdd` and `LieAddGroup`
                            instances. Two-line `where`-clauses
                            providing `contMDiff_add` and
                            `contMDiff_neg`.
Lie group layer: complete. The complex torus is now a fully
                 analytic Lie additive group:
                 `LieAddGroup (modelWithCornersSelf ℂ V) ω
                 (V ⧸ Λ.subgroup)`. All three anti-hack
                 "torus-like analytic structure" instances on
                 `Jacobian X` are now backed by real infrastructure.
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
```

```text
Next tick priorities
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
1. Begin Queue C — `HolomorphicOneForm`. The complex-torus layer
   (charted-space, manifold, projection smoothness, LieAddGroup) is
   complete; the next infrastructure block is holomorphic
   1-forms on a manifold. First packet: define `HolomorphicOneForm
   X` for an analytic complex manifold `X` (using existing
   differential-form API) and prove its `AddCommGroup` /
   `Module ℂ` structure.
2. State `FiniteDimensionalHolomorphicOneForms` as a named theorem
   even if the proof is deferred (it is the single largest missing
   ingredient for the genus identity).
3. Begin path-integration / period scaffolding so the analytic
   `Jacobian X = H⁰(X, Ω¹)* / H₁(X, ℤ)` definition is reachable
   once Queue C has finite-dimensionality.
```
