# Jacobian Challenge

A Lean 4 / Mathlib formalization of the Jacobian variety of a compact Riemann surface (see _About_ below for scope).

## Progress Report

Last tick: 2026-04-27 14:48 EDT

```text
Headline progress markers (every value below is a fresh count from this tick)
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
Public spec discharged          0 / 24    sorries in Jacobian/Challenge.lean (frozen target)
StatementBank declarations     22         named decls in Jacobian/WorkPackets/StatementBank.lean
                                          (excluding 2 Inventory metadata items)
Aristotle integrations to date 82         `"status":"integrated"` lines in aristotle_jobs.jsonl
                                          (was misreported as 31 in prior ticks; recounted today)
Production sorry-free files   366 / 381   denominator excludes 11 intentional design files
                                          (Challenge, Solution, StatementBank, 8 *Recon*.lean)

Reproduction:
  total       find Jacobian -name "*.lean" | wc -l                        → 392
  intentional 7+8 (3 design files + 8 Recon discovery files)              → 15 wait,
              Challenge.lean, Solution.lean, StatementBank.lean (3) +
              {AbelJacobi,ComplexTorus,HolomorphicForms,Periods,TraceDegree}
              /Recon.lean + DiscretenessRecon + ManifoldRecon +
              ZLatticeRecon + PathIntegralViaCoverRecon                   → 11
  prod        392 − 11                                                    → 381
  with-sorry  grep -rl "\bsorry\b" prod-files                             → 17
              (2 are doc-comment-only matches in umbrella files)          → 15 real
  sorry-free  381 − 15                                                    → 366
```

```text
StatementBank promotion (curated ratio: how many named declarations have a
real production-module implementation? Denominator is the StatementBank
itself, not a count of the tree.)
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
Active jobs (ours):     5 / 5  (no movement at backend this tick — all 5 still IN_PROGRESS / QUEUED)
                        `37b183aa` evalLinearMap_ne_zero_of_toFun_ne_zero (HolomorphicForms)
                        `6c252557` periodSubgroup_eq_range (Periods)
                        `2f5d999b` mk_eq_zero_iff_mem_range (AnalyticJacobian)
                        `b3a3b251` witnessAbelJacobi_self_both (AbelJacobi)
                        `2d65778f` evalJacobianClass_self_sub_self (AnalyticJacobian; now
                                   redundant — discharged locally this tick by `sub_self _`)
Integrated this tick:   2 lemmas via 1 new local file + 1 sorry-discharge
                        (see "Local cadence" below).
Tree note:              Jacobian/Solution.lean and Jacobian/AbelJacobi/AnalyticOfCurveBasis.lean
                        are dirty/untracked from earlier work — left untouched per PROMPT.md.
```

```text
Local cadence this tick (Claude-owned, no Aristotle dependency)
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
NEW Jacobian/AnalyticJacobian/EvalJacobianClassMkBridge.lean:
  `evalJacobianClass_add_eq_mk`
  `evalJacobianClass_sub_eq_mk`
  `evalJacobianClass_neg_eq_mk`
  `zero_analyticJacobianGroup_eq_mk_zero`
  → 4 mk-bridge lemmas, all term-mode rewrites via existing mk_{add,sub,neg,zero}.

DISCHARGED Jacobian/AnalyticJacobian/EvalJacobianClassSelfSub.lean:
  `evalJacobianClass_self_sub_self` was a parking-spot sorry; closed
  this tick with term-mode `sub_self _`.
```

```text
Build status — recomputed each tick from the tree
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
Challenge target          pass         lake build Jacobian.Challenge
Statement bank            pass         lake build Jacobian.WorkPackets.StatementBank
Current target            pass         lake build Jacobian.AnalyticJacobian.EvalJacobianClassMkBridge
                          pass         lake build Jacobian.AnalyticJacobian.EvalJacobianClassSelfSub

Sorry-free coverage by directory (production files only — Recon files excluded
from both numerator and denominator)
                                       bar              ratio    %
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
Jacobian/AnalyticJacobian        ███████████████████░  21 / 22  95.5%
Jacobian/AbelJacobi              ██████████████████░░  18 / 20  90.0%
Jacobian/HolomorphicForms        █████████████████░░░  25 / 28  89.3%
Jacobian/ComplexTorus            █████████████████░░░  47 / 53  88.7%
Jacobian/Periods                 ████████████████████  168 / 171  98.2%
Jacobian/TraceDegree             ████████████████████  81 / 81  100.0%
Top-level Jacobian/*.lean        ████████████████████  6 / 6   100.0%

Reproduction:
  per dir: total = `find <dir> -maxdepth 1 -name "*.lean" | wc -l`
           recon = `find <dir> -maxdepth 1 -name "*Recon*.lean" | wc -l`
           with-sorry-real = (grep -l "\bsorry\b") minus doc-comment-only files
           ratio = (total − recon − with-sorry-real) / (total − recon)
```

```text
Next tick priorities
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
1. Check the 5 in-flight Aristotle packets; integrate any that
   land and replace `2d65778f` with a fresh packet (since the
   original target was already discharged locally).
2. Continue 4-lemma local cadence — candidate next file:
   `Jacobian/AnalyticJacobian/MkAddCancel.lean` (mk_add_left_cancel
   variants once mk_add is in hand) or another mk-bridge group.
3. Re-derive headline numbers each tick, per the new
   "Accurate measurement rules" in PROMPT.md.
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
