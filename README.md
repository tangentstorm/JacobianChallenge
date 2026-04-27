# Jacobian Challenge

A Lean 4 / Mathlib formalization of the Jacobian variety of a compact Riemann surface (see _About_ below for scope).

## Progress Report

Last tick: 2026-04-27 14:15 EDT

```text
Headline progress markers (calculated, not estimated)
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
Public spec discharged           0 / 24   sorries in Jacobian/Challenge.lean (frozen target)
StatementBank declarations      22        (excluding 2 Inventory metadata)
Aristotle integrations to date  31        committed per aristotle_jobs.jsonl
Production infrastructure files 372       sorry-free (excludes Challenge/StatementBank/*Recon)

Note: an earlier "Layer | Bar | %" block carried hand-picked
percentages per layer and was removed for being non-calculated.
The metrics shown here are computed directly from the tree.
```

```text
StatementBank promotion (Q: how many named declarations have a
real production-module implementation?)
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                          promoted / total   notes
Inventory                    2 / 2           metadata only — counted separately
ComplexTorus                 3 / 3           Prop placeholders backed by IsManifold + LieAddGroup instances
HolomorphicForms             3 / 3           abbrev/def used directly as the working types
Periods                      1 / 6           IntegralOneCycle abbrev concrete; periodFunctional still
                                             `opaque`; period_homology/period_pairing_full_rank still
                                             `Prop := True`; periodFullComplexLattice not yet
AnalyticJacobian             1 / 3           AnalyticJacobianType ✓ (= AnalyticJacobianGroup);
                                             equivChallenge + homeomorph_challenge still placeholders
AbelJacobi                   0 / 2           pathIntegralFunctional opaque; analyticOfCurve still a stub
TraceDegree                  0 / 3           pullbackForms / traceForms / analyticDegree all opaque
                          ────────
Substantive total            8 / 20  (40%)   excludes 2 Inventory metadata items
```

```text
Aristotle status
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
Active jobs (ours):     5 / 5  (all submitted this tick, all sorry-stub parking spots until COMPLETE)
                        `37b183aa` evalLinearMap_ne_zero_of_toFun_ne_zero (HolomorphicForms)
                        `6c252557` periodSubgroup_eq_range (Periods)
                        `2f5d999b` mk_eq_zero_iff_mem_range (AnalyticJacobian)
                        `b3a3b251` witnessAbelJacobi_self_both (AbelJacobi)
                        `2d65778f` evalJacobianClass_self_sub_self (AnalyticJacobian)
Integrated this tick:   0 local lemma files. This commit also rewrites the
                        Progress Report header to remove fake per-layer %s
                        and add the StatementBank promotion ratio table.
Tree note:              6 untracked files unrelated, left alone.
```

```text
Build status — all targets compile (lake build Jacobian.{Challenge, …, *.Recon} → pass)

Sorry-free coverage by directory               bar              %   files
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
Jacobian/HolomorphicForms                ████████████████████  100%  (26/26)
Jacobian/AnalyticJacobian                ████████████████████  100%  (19/19)
Jacobian/AbelJacobi                      ████████████████████  100%  (19/19)
Jacobian/TraceDegree                     ████████████████████  100%  (82/82)
Jacobian/Periods                         ███████████████████░   99%  (170/171)†
Jacobian/ComplexTorus                    ███████████████████░   98%  (54/55)†
Top-level umbrellas (Jacobian/*.lean)    █████████████████░░░   86%  (6/7)‡
Jacobian/WorkPackets                     ░░░░░░░░░░░░░░░░░░░░    0%  (0/1)‡

Production infrastructure (excluding intentional design files): 100% (372/372).

† Single `*Recon.lean` discovery file with intentional sorries.
‡ Challenge.lean (frozen public spec) and StatementBank.lean
  (placeholder/dependency-shape file) — sorries are by design.
```

```text
Next tick priorities
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
1. Integrate the four in-flight packets as they land
   (091ac5d1, ee3ce016, fe592ee1, 0b8b1163); wire each into
   the appropriate umbrella.
2. Submit `pullbackFormsFun_smooth` once 0b8b1163 lands —
   the substantive ContMDiff step for upgrading to
   HolomorphicOneForm E X via Queue G.
3. Submit pathIntegralViaChartCorrect linearity (zero/neg/add)
   once ee3ce016 + fe592ee1 land.
4. Begin Claude-owned design of multi-chart `pathIntegralViaCover`
   (subpath / affine reparam, then a clean Aristotle packet for
   the well-definedness lemmas).
5. Decomposed TorusExample retry (smaller helpers around the
   `Bundle.continuousLinearMap` constant-section roadblock that
   stalled `259b18a1`).
```

## About

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
