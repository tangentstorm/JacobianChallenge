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

Last tick: 2026-04-25 19:17 EDT

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
                    (same 5 unrelated jobs QUEUED 5h+, identical to
                    last tick). No new submissions — piling onto a
                    wedge is wasteful.
Integrated this tick: nothing from Aristotle.
Local progress this tick: extended `ComplexTorus/Witness.lean` to
                          also discharge `quotientLieAddGroupStatement`
                          (the third Queue B placeholder in
                          StatementBank). Drafted the LieAddGroup
                          smoothness packet decomposition (5 narrow
                          target files) into `aristotle_tasks.md`'s
                          new "Planned packets" section so the work
                          is ready to submit when the queue unblocks.
Quotient manifold layer: 100%. ChartedSpace + IsManifold both done,
                         no sorries. All three Queue B
                         chart/manifold StatementBank placeholders
                         (chart, manifold, lie-add-group) now
                         witnessed by the concrete instance.
```

```text
Current build status
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
Challenge        pass    lake build Jacobian.Challenge
Statement bank   pass    lake build Jacobian.WorkPackets.StatementBank
ComplexTorus     pass    lake build Jacobian.ComplexTorus (with IsManifold)
IsManifold       pass    lake build Jacobian.ComplexTorus.IsManifold (no sorry)
Witness          pass    lake build Jacobian.ComplexTorus.Witness (no sorry)
```

```text
Next tick priorities
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
1. Submit (or hand-prove if Aristotle stays wedged) packet 1 of
   the LieAddGroup decomposition: `AddSmoothLocal.lean` —
   `ContMDiffAt` of `(q1, q2) ↦ q1 + q2` at a single point. Pattern
   mirrors the chart-transition smoothness work (lift via surjInv,
   apply chart machinery, observe coordinate version is linear).
2. Same for `NegSmoothLocal.lean` — `ContMDiffAt` of `q ↦ -q`.
   Disjoint write scope from packet 1; the two can run in parallel.
3. Then promote both to `ContMDiff` everywhere, package into the
   `LieAddGroup (modelWithCornersSelf ℂ V) ⊤ (quotient V Λ)`
   instance. Full decomposition in `aristotle_tasks.md`.
```
