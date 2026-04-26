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

Last tick: 2026-04-25 20:30 EDT

```text
Layer                          Bar                    %    Note
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
Project scaffolding            ████████████████████  100%  done
Mathlib inventory              ████████████████████  100%  v4.28.0 audit
Complex torus quotient         ████████████████████  100%  ZLattice bridge sorry-free
Quotient charted-space/manifold ████████████████████ 100%  ChartedSpace + IsManifold sorry-free
Projection (mk) smoothness     ████████████████████  100%  contMDiff_mk
LieAddGroup smoothness         ████████████████████  100%  +, -, LieAddGroup instance
Holomorphic forms              █░░░░░░░░░░░░░░░░░░░    5%  Queue C recon landed
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
Local progress this tick: Queue C kickoff. Added
                          `Jacobian/HolomorphicForms/Recon.lean`,
                          a name-discovery and design document for
                          the `HolomorphicOneForm X` definition.
                          Surveys Mathlib's TangentBundle / mfderiv /
                          ContMDiffSection (PRESENT) vs
                          CotangentBundle / MDifferentialForm /
                          HolomorphicOneForm (ABSENT). Recommends
                          starting with a self-contained
                          chart-coherence definition (Approach B in
                          the file) and lays out the first
                          Aristotle-sized packets: define
                          `HolomorphicOneForm`, prove `AddCommGroup`,
                          prove `Module ℂ`, update the StatementBank
                          placeholder, state
                          `FiniteDimensionalHolomorphicOneForms` as a
                          class. Build green; not re-exported as
                          public API (recon convention).
Complex torus layer: complete (charted-space, manifold, projection
                     smoothness, full `LieAddGroup` instance).
                     Queue C is the next infrastructure block.
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
```

```text
Next tick priorities
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
1. Promote the Queue C recon plan into code. New file
   `Jacobian/HolomorphicForms/Defs.lean` containing the
   chart-coherence definition of `HolomorphicOneForm X` per
   Recon.lean Approach B.
2. `Jacobian/HolomorphicForms/AddCommGroup.lean` and
   `.../Module.lean`: derive `AddCommGroup` and `Module ℂ` from
   pointwise operations.
3. Update the `StatementBank.HolomorphicOneForm` placeholder
   (currently `:= ℂ`) to use the real type, then state
   `FiniteDimensionalHolomorphicOneForms` as a class with the
   proof deferred.
```
