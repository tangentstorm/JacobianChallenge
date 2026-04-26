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

Last tick: 2026-04-25 21:14 EDT

```text
Layer                            Bar                    %    Note
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
Project scaffolding              ████████████████████  100%  done
Mathlib inventory                ████████████████████  100%  v4.28.0 audit
Complex torus quotient           ████████████████████  100%  ZLattice bridge sorry-free
Quotient charted-space/manifold  ████████████████████  100%  ChartedSpace + IsManifold sorry-free
Projection (mk) smoothness       ████████████████████  100%  contMDiff_mk
LieAddGroup smoothness           ████████████████████  100%  +, -, LieAddGroup instance
Holomorphic forms                ████░░░░░░░░░░░░░░░░   25%  type + AddCommGroup + Module ℂ
Path integration/periods         ░░░░░░░░░░░░░░░░░░░░    0%  pending
Abel-Jacobi API                  ░░░░░░░░░░░░░░░░░░░░    0%  pending
Trace/degree/push-pull           ░░░░░░░░░░░░░░░░░░░░    0%  pending
```

```text
Aristotle status
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
Active jobs (ours): 0/5. Aristotle queue still wedged (5 unrelated
                    jobs QUEUED 6h+).
Integrated this tick: nothing from Aristotle.
Local progress this tick: attempted to update
                          `StatementBank.HolomorphicOneForm`
                          placeholder to use the real Defs.lean
                          definition. Reverted: the cascade through
                          `HolomorphicOneFormDual` (which uses
                          `→L[ℂ]` requiring `NormedAddCommGroup`,
                          which `ContMDiffSection` doesn't carry)
                          and `periodFullComplexLattice` (requires
                          `NormedSpace ℂ` on the dual) is broader
                          than this tick — those placeholders need
                          their own redesign together with the
                          Period-layer work in Queue D. The real
                          `HolomorphicOneForm` definition stays in
                          `Defs.lean`; the StatementBank placeholder
                          is left as `:= ℂ` until Queue D begins.
                          Also fixed README progress-bar alignment
                          (label column padded to 33 chars so the
                          "Quotient charted-space/manifold" row
                          lines up with the others).
Complex torus layer: complete. Queue C foundation in
                     `Jacobian/HolomorphicForms/Defs.lean`.
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
```

```text
Next tick priorities
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
1. State `FiniteDimensionalHolomorphicOneForms X` over
   `HolomorphicOneForm ℂ X` (using the real `Jacobian.HolomorphicForms.Defs`
   type) as a class with the proof deferred. This needs to live in
   a new module that imports `HolomorphicForms.Defs` rather than
   `StatementBank.lean` (per the design-cascade discovery this tick).
2. Sanity check on the torus: confirm `Module.finrank ℂ
   (HolomorphicOneForm ℂ (V ⧸ Λ.subgroup))` is positive when
   `V = ℂ` (genus 1 Riemann surface).
3. Begin Queue D scaffolding (path integration, periods) so the
   `HolomorphicOneFormDual` and `periodFullComplexLattice`
   placeholders can be redesigned together.
```
