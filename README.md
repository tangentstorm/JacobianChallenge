# Jacobian Challenge

A Lean 4 / Mathlib formalization of the Jacobian variety of a compact Riemann surface (see _About_ below for scope).

## Progress Report

Last tick: 2026-04-27 12:40 EDT

```text
Layer                            Bar                    %    Note
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
Project scaffolding              ████████████████████  100%  done
Mathlib inventory                ████████████████████  100%  v4.28.0 audit
Complex torus quotient API       ████████████████████  100%  FullComplexLattice + quotient
Quotient charted-space/manifold  ████████████████████  100%  ChartedSpace + IsManifold sorry-free
Projection (mk) smoothness       ████████████████████  100%  contMDiff_mk
LieAddGroup smoothness           ████████████████████  100%  +, -, LieAddGroup instance
Holomorphic forms                ███████████░░░░░░░░░   55%  type/module/analyticGenus + complete genus order/positivity API + full toFun matrix (zero/add/sub/neg/ℂ-smul/ℕ-smul/ℤ-smul/sub-self/double-neg) + `evalLinearMap` complete linearity in form & vec slots + ext + witness positivity
Path integration/periods         ██████████████░░░░░░   70%  full bridge ladder + refl/translation chart instances + named API around periodPairing/periodSubgroup with closure + extensional carrier facts + integer-scalar periodPairing API (n/zsmul + matching subgroup membership)
Analytic Jacobian (group)        ██████░░░░░░░░░░░░░░   31%  abstract quotient group + full mk + integer-action vec-slot + zero-class characterizations + Nontrivial witness chain + cycle-arithmetic mk∘periodPairing identities + evalJacobianClass equality characterizations (mem/exists-cycle iff)
Abel-Jacobi API                  ████████░░░░░░░░░░░░   41%  witness skeleton + composition + vec-slot algebra + base-change + telescoping + genus/Nontrivial chain + explicit `mk`/periodSubgroup bridges + `periodPairing` invariance + witness-zero/equality characterizations + nsmul/zsmul/neg periodPairing sufficient conditions for witness vanishing
Trace/degree/push-pull           ███████████░░░░░░░░░   57%  pullbackFormsFun: full linearity + LinearMap bundle + id + comp-id/comp-const + const-of-const + mixed const/id + id-of-id + light bridge to HolomorphicForms.evalLinearMap + bundled along-id+along-const full dist + bundled along-(id ∘ id) full forwarder bank + bundled comp-const/const-comp full form/vec-slot dist + bundled `pullbackFormsLinearMap` ℕ/ℤ-smul + zero/neg/sub identities for arbitrary f + smul/neg/add combined identities (function + vec-applied)

Note: under the global hypothesis `mfderiv c.symm = id` (true for
translation-transition charts, e.g. the torus), the corrected
period machinery reduces to the simpler provisional one across all
5 integration layers (chartedForm → in-chart → via-chart →
cover-with → Pick). Concrete instances established for the refl
chart and the explicit `translationChart v` construction.
```

```text
Aristotle status
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
Active jobs (ours): 1/5 — `ee14b794` IN_PROGRESS
                    (Jacobian/HolomorphicForms/EvalLinearMapEqZero.lean,
                    rfl-iff smoke test for backend round-trip).
                      Backend still asleep. Canary is
                      submitted-redundant; kept as wake detector.
Integrated this tick (local Claude-owned, 4 lemmas):
                      NEW TraceDegree.PullbackFormsLinearMapSmulAddApplyVec:
                      vec-applied versions of the smul-add /
                      smul-sub / smul-left-add / sub-smul-right
                      combined identities.
Submitted this tick:  `ee14b794` HolomorphicForms.EvalLinearMapEqZero
                      (rfl-iff smoke test).
Submitted this tick:  none.
Failed/split this tick: none.
```

```text
Build status — all targets compile (lake build Jacobian.{Challenge, …, *.Recon} → pass)

Sorry-free coverage by directory               bar              %   files
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
Jacobian/HolomorphicForms                ███████████████████░   95%  (21/22)*
Jacobian/AnalyticJacobian                ████████████████████  100%  (18/18)
Jacobian/AbelJacobi                      ████████████████████  100%  (18/18)
Jacobian/TraceDegree                     ████████████████████  100%  (76/76)
Jacobian/Periods                         ███████████████████░   99%  (169/170)†
Jacobian/ComplexTorus                    ███████████████████░   98%  (54/55)†
Top-level umbrellas (Jacobian/*.lean)    █████████████████░░░   86%  (6/7)‡
Jacobian/WorkPackets                     ░░░░░░░░░░░░░░░░░░░░    0%  (0/1)‡

Production infrastructure (excluding intentional design files): 100% (361/361).

† Single `*Recon.lean` discovery file with intentional sorries.
‡ Challenge.lean (frozen public spec) and StatementBank.lean
  (placeholder/dependency-shape file) — sorries are by design.
* `EvalLinearMapEqZero.lean` is a parking spot for an in-flight
  Aristotle packet (`ee14b794`); not yet wired into the umbrella.
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
