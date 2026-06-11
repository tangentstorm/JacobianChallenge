# Result - Restore leanok on Montel realized-patch cover packaging

Restored both `\leanok` markers on
`lem:montel-realized-patch-cover-packaging` in
`tex/sections/04-branched-covers-genus-zero.tex`.

The first audit run after the narrow build exposed that
`exists_realizedPatchCover_of_components.{u}` was indexed by
`scripts/blueprint_audit.py` as the non-Lean name ending in `.`.  I made the
mechanical spelling adjustment in
`Jacobian/HolomorphicForms/MontelSourceChartCover.lean` by moving the universe
level to an explicit `universe u` declaration and spelling the theorem name as
`exists_realizedPatchCover_of_components`, preserving the same statement and
proof.

Verification:

- `lake exe cache get`: succeeded earlier in this session; no files to download.
- `bash .sci/bin/build-target.sh`: passed for
  `Jacobian.HolomorphicForms.MontelSourceChartCover`.
- `python3 scripts/blueprint_audit.py`: passed. Tail:
  `B:decls-exist-but-no-env-leanok: 56`; external refs informational.
- `bash scripts/build-blueprint.sh --graph-only`: passed; blueprint built at
  `blueprint/web/index.html`.
