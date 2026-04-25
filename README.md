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

Last tick: 2026-04-25 19:25 EDT

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
Active jobs (ours): 0/5. Aristotle queue still wedged server-wide
                    (same 5 unrelated jobs QUEUED 5h+).
Integrated this tick: nothing from Aristotle.
Local progress this tick: added
                          `Jacobian/ComplexTorus/MkLocallyTranslate.lean`,
                          a v₁-free generalization of
                          `localSection_mk_locally_translate`.
                          States: `y ↦ localSection Λ w r (mk y)`
                          agrees with `y ↦ y + g` (for a fixed
                          lattice `g`) on a neighborhood of every
                          `x ∈ mk ⁻¹' (mk '' Metric.ball w r)`. This
                          is the building block needed for the next
                          three substantive lemmas: smoothness of
                          `mk`, smoothness of `+`, and smoothness
                          of `-`. Build green.
Quotient manifold layer: 100%. LieAddGroup smoothness work begun —
                         the local-translation building block for
                         all three smoothness proofs (mk, +, -) is
                         now in place.
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
```

```text
Next tick priorities
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
1. `Jacobian/ComplexTorus/MkSmooth.lean`: prove `ContMDiff` of
   `mk : V → V ⧸ Λ.subgroup` using the new `mk_locally_translate`
   building block. The chart-coord version of `mk` is
   `localSection_w ∘ mk`, which equals a translation locally; that
   gives `ContDiffWithinAt` pointwise, hence `ContMDiff`.
2. With `mk` smoothness in hand, attack `+` smoothness (likely via
   `mk` lifting: `mk(x+y) = mk(x) + mk(y)` reduces quotient `+`
   smoothness to `mk ∘ + : V × V → V/Λ` smoothness, which factors
   as smooth `+` on `V` followed by smooth `mk`).
3. Same pattern for `-` smoothness, then assemble the
   `LieAddGroup` instance.
```
