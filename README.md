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

Last tick: 2026-04-25 19:55 EDT

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
Active jobs (ours): 0/5. Aristotle queue still wedged (5 unrelated
                    jobs QUEUED 5h+).
Integrated this tick: nothing from Aristotle.
Local progress this tick: 🎉 `ContMDiff (mk V Λ)` lands. Two new
                          files:
                          - `MkSmoothOnChartTarget.lean`: a one-liner
                            from `contMDiffOn_chart_symm` giving
                            smoothness of `mk` (as `chart.symm`) on
                            each chart target ball.
                          - `MkSmooth.lean`: the full theorem.
                            Proof: at any `x : V`, get the
                            chart-target representative
                            `x' := chartAt(mk x) (mk x)` with
                            `mk x' = mk x`, so `g := x' - x ∈
                            Λ.subgroup`. Use
                            `MkSmoothOnChartTarget` for `ContMDiffAt
                            mk x'`, compose with the smooth
                            translation `y ↦ y + g` (smooth affine,
                            via `contDiff.add`), and use
                            translation-invariance of `mk` (since
                            `mk g = 0`) to convert
                            `ContMDiffAt (mk ∘ T_g) x` into
                            `ContMDiffAt mk x`. ~50 lines, no
                            automation. Both files build green;
                            wired into the umbrella.
Quotient manifold layer: 100%. The first of three LieAddGroup-layer
                         smoothness theorems (mk, +, -) is done.
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
MkSmoothOnChartTarget pass lake build Jacobian.ComplexTorus.MkSmoothOnChartTarget (no sorry)
MkSmooth         pass    lake build Jacobian.ComplexTorus.MkSmooth (no sorry)
```

```text
Next tick priorities
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
1. `Jacobian/ComplexTorus/AddSmooth.lean`: prove `ContMDiff` of
   `+ : V/Λ × V/Λ → V/Λ`. The same pattern should adapt: pick
   representatives via the product chart, lift down to `V × V`,
   use the chart-target smoothness of `mk` plus translation by
   the lattice element `g := (x'_1, x'_2) - (x_1, x_2) ∈ Λ²`.
2. `Jacobian/ComplexTorus/NegSmooth.lean`: same approach for `-`.
3. Assemble `LieAddGroup (modelWithCornersSelf ℂ V) ⊤ (quotient V Λ)`
   from steps 1 and 2.
```
