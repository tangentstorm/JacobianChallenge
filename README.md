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

Last tick: 2026-04-25 21:17 EDT

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
Path integration/periods         ░░░░░░░░░░░░░░░░░░░░    0%  pending
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
                          `Jacobian/HolomorphicForms/FiniteDimensional.lean`,
                          a new module that imports
                          `HolomorphicForms.Defs` and states:
                          - `FiniteDimensionalHolomorphicOneForms E X`
                            class wrapping `Module.Finite ℂ
                            (HolomorphicOneForm E X)`. Proof of
                            finite-dimensionality is deferred (the
                            largest analytic ingredient, classical
                            `dim H⁰(X, Ω¹) = g`).
                          - `analyticGenus E X` as
                            `Module.finrank ℂ (HolomorphicOneForm E X)`,
                            available under the class instance.
                          Build green. Sidesteps the StatementBank
                          cascade discovered last tick by living in
                          its own module.
Complex torus layer: complete. Queue C: type, module structure, and
                     analytic-genus definition all in place; only
                     `Module.Finite` proof and the genus identity
                     remain.
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
```

```text
Next tick priorities
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
1. Sanity check on the torus: confirm `analyticGenus ℂ
   (V ⧸ Λ.subgroup)` is positive (≥ 1) for a genus-1 Riemann
   surface (`V = ℂ`). The `dz` form descends from `V`'s standard
   coordinate; whether that survives Mathlib's bundle setup is the
   first concrete computation.
2. Begin Queue D scaffolding so the `HolomorphicOneFormDual` and
   `periodFullComplexLattice` placeholders can be redesigned with
   the right topology choice (likely working with the linear-dual
   on a finite-dim subspace, once `Module.Finite` lands).
3. Continue thinking about the eventual proof of
   `Module.Finite ℂ (HolomorphicOneForm ℂ X)` — needs Hodge or
   Riemann–Roch input.
```
