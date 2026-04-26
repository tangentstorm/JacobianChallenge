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

Last tick: 2026-04-25 20:47 EDT

```text
Layer                          Bar                    %    Note
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
Project scaffolding            ████████████████████  100%  done
Mathlib inventory              ████████████████████  100%  v4.28.0 audit
Complex torus quotient         ████████████████████  100%  ZLattice bridge sorry-free
Quotient charted-space/manifold ████████████████████ 100%  ChartedSpace + IsManifold sorry-free
Projection (mk) smoothness     ████████████████████  100%  contMDiff_mk
LieAddGroup smoothness         ████████████████████  100%  +, -, LieAddGroup instance
Holomorphic forms              ████░░░░░░░░░░░░░░░░   25%  type + AddCommGroup + Module ℂ
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
Local progress this tick: 🎉 Queue C foundation lands. Two new
                          files (no sorries):
                          - `CotangentBundle.lean`: defines
                            `CotangentSpace E X x` as
                            `TangentSpace I x →L[ℂ] (Bundle.Trivial X
                            ℂ) x` and `CotangentModelFiber E` as
                            `E →L[ℂ] ℂ`. The
                            `VectorBundle ℂ (E →L[ℂ] ℂ)
                            (CotangentSpace E X)` instance is derived
                            for free from Mathlib's
                            `Bundle.ContinuousLinearMap.vectorBundle`.
                            One `example` confirms inferInstance.
                          - `Defs.lean`: defines
                            `HolomorphicOneForm E X` as the
                            `ContMDiffSection` of the cotangent
                            bundle at smoothness `n = ⊤` (analytic).
                            Two `example`s confirm
                            `AddCommGroup` and `Module ℂ` instances
                            are inherited automatically from
                            `ContMDiffSection`'s mathlib instances.
Complex torus layer: complete. Queue C foundation: type +
                     vector-space structure now in place.
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
1. Update `JacobianChallenge.HolomorphicForms.HolomorphicOneForm`
   in `StatementBank.lean` from the `:= ℂ` placeholder to the real
   type defined in `Jacobian/HolomorphicForms/Defs.lean`. This is
   blocked by typeclass alignment: the StatementBank uses `𝓘(ℂ)`
   (modeled on `ℂ` itself, i.e., 1-dimensional) whereas Defs uses
   the more general `modelWithCornersSelf ℂ E`. Either narrow Defs
   to the 1-d case or generalize StatementBank.
2. State `FiniteDimensionalHolomorphicOneForms X` as a class
   wrapping `Module.Finite ℂ (HolomorphicOneForm X)`. Proof
   deferred — the largest analytic ingredient.
3. Stretch goal: confirm the dimension on the simple torus example
   `V ⧸ Λ.subgroup` for `V = ℂ` (`g = 1`), as a sanity check.
```
