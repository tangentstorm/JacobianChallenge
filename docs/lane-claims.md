# Lane claims board (manager-maintained)

Check THIS FILE in your proposal-time freshness pass (planning-guide
§1.3) **in addition to** branch greps: approved-but-unlanded claims are
invisible to greps, and proposing a claimed item is an automatic ADJUST.
A row here means the item is OWNED even if no file exists on the branch
yet. Updated by the manager when allocations change.

## B2 toolbox (docs/perron-b2-dirichlet-phase0.md §4)
| Item | Owner | State |
|------|-------|-------|
| W1 max principle | jc10 | in flight — discharge target: `WeakMaxPrincipleInput` (PerronRemovableSingularity.lean), name+statement FROZEN (2 consumers: W5b-i 527fe1f9, W6 15c4d181) |
| W2 harmonic∘analytic | jc3 | GREEN (577fec05) |
| W3a–c Poisson operator (incl. the def) | jc6 | GREEN (bdf63495 + c5863c83) |
| W3d boundary limit (continuous data) | jc6 | REVIVED 2026-06-11 (W5b+W6 attainment gap), in flight |
| W4a Harnack | jc11 | GREEN (1bde1270) |
| W4b Harnack convergence | jc11 | in flight |
| W5 PerronSubOn class | jc4 | in flight |
| W6 removable singularity | jc9 | in flight |
| W7–W11 stage assembly | — | GATED (S-repairs + toolbox) |

## Spine (statements + repairs)
| Item | Owner | State |
|------|-------|-------|
| S1–S7 B2 statement repairs + lever + R2 shape | jc3 | LANDED (b65c870f, reviewed); S4 retention + S5 instances ratified |
| C-section statements | jc1 | C1/C2 payload LANDED (a859908e, reviewed; inverted-end repair); C3 next |
| A2 assembly | jc0 | GREEN (f7779110); RULING 2026-06-11: public statement stays unconditioned — C demands are proof obligations (jc1 result.md); degenerate stage≡X discharge rejected on sight |
| A3 cut slices | jc0 | slices 5–6 landed; slice 7 (marked-end/base, R1) bound |
| B4 W-ladder (W1a…) | jc7 | in flight |
| stage-data → sphere-bound bridge | jc4 | reserved (gated on spine) |

## Other lanes
| Item | Owner | State |
|------|-------|-------|
| #237 ports (M2, then B/C/D1, then D2–D5) | jc8 | M2 approved |
| zero-stub stamps (#242 hygiene) | jc2 | GREEN (a034aee7) |
| #242 provider / Stage S | — | PARKED (substrate debt) |
| #244 quotient proof | — | PARKED (priced too high) |
| LoopToCycle (loop→H₁ bridge) | — | BANKED (jc9's design) |
