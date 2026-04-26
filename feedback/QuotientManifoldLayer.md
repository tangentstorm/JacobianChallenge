# Code Review: Quotient Manifold Layer

Review scope: source-level review of the current quotient manifold layer around
`Jacobian/ComplexTorus/ChartedSpace.lean`, `IsManifold.lean`, `MkSmooth.lean`,
the new `AddSmooth.lean` / `NegSmooth.lean` / `LieAddGroup.lean` files, the
umbrella import, and the README progress claim. Per instruction, I am assuming
the relevant Lean targets build.

## Summary

The README's narrow claim that the quotient has a charted-space and
`IsManifold` layer is credible: `complexTorusChartedSpace` and
`complexTorusIsManifold` are implemented in source, and the earlier
reconnaissance files are no longer re-exported by `Jacobian/ComplexTorus.lean`.

The main issue is accounting, not the local chart construction. The project now
mixes three different meanings of "quotient manifold layer":

1. charted-space and `IsManifold` instances,
2. smoothness of the projection `mk`,
3. the `LieAddGroup` instance, requiring smooth `+` and `-`.

Those should be tracked separately. As written, the README and witness layer
can make the completion state look stronger than the Lean API actually
guarantees.

## Findings

### 1. `StatementBank` witnesses are too weak for the claimed targets

Severity: high

`Jacobian/WorkPackets/StatementBank.lean:132` defines
`quotientIsManifoldStatement` as:

```lean
exists _ : ChartedSpace V (quotient V Lambda), True
```

and `Jacobian/WorkPackets/StatementBank.lean:136` defines
`quotientLieAddGroupStatement` the same way. Consequently,
`Jacobian/ComplexTorus/Witness.lean:31` and `:40` can discharge both targets
with only `complexTorusChartedSpace Lambda` and `trivial`.

That means `Witness` does not actually certify either:

- `IsManifold (modelWithCornersSelf C V) top (quotient V Lambda)`;
- `LieAddGroup (modelWithCornersSelf C V) top (quotient V Lambda)`.

Suggested fix: strengthen the two statements now that the real instances exist:

```lean
def quotientIsManifoldStatement (Lambda : FullComplexLattice V) : Prop :=
  Nonempty (IsManifold (modelWithCornersSelf C V) (top : WithTop NInfinity) (quotient V Lambda))
```

For `LieAddGroup`, either leave the statement explicitly pending, or make it
ask for the real class once the instance is assembled.

### 2. README progress is stale relative to the wired smooth group files

Severity: medium

`README.md:88` and `README.md:93` still list `AddSmooth.lean` and
`NegSmooth.lean` as next-tick priorities, and `README.md:94` lists the
`LieAddGroup` assembly as future work. But all three files now exist:
`AddSmooth.lean`, `NegSmooth.lean`, and `LieAddGroup.lean`.

`Jacobian/ComplexTorus.lean` also imports all three, so the umbrella source is
ahead of the README status text.

Assuming these files build, README should be updated so it no longer presents
completed and imported files as future priorities. The current build-status
table should include:

- `Jacobian.ComplexTorus.AddSmooth`;
- `Jacobian.ComplexTorus.NegSmooth`;
- `Jacobian.ComplexTorus.LieAddGroup`;
- and the umbrella `Jacobian.ComplexTorus` after those imports.

### 3. The README over-compresses manifold and Lie-additive-group progress

Severity: medium

`README.md:32` says:

```text
Quotient manifold layer   100%  ChartedSpace + IsManifold sorry-free
```

That line is defensible if the layer means only charted-space plus manifold.
But `README.md:67` immediately says this is "The first of three
LieAddGroup-layer smoothness theorems (mk, +, -)", and the next section still
treats `+`, `-`, and the final instance as future work even though the files
exist in the worktree.

Suggested split:

- `Quotient charted-space/manifold`: 100%.
- `Projection smoothness`: 100%.
- `LieAddGroup smoothness`: 0%, 33%, 67%, or 100% depending on whether
  `AddSmooth`, `NegSmooth`, and the final instance are imported and verified.

This would remove ambiguity without downplaying the real charted-space work.

### 4. The final `LieAddGroup` instance exists, but the witness still misses it

Severity: medium

The source has:

- `contMDiff_mk` in `Jacobian/ComplexTorus/MkSmooth.lean:33`;
- `contMDiff_quotient_add` in `Jacobian/ComplexTorus/AddSmooth.lean:33`;
- `contMDiff_quotient_neg` in `Jacobian/ComplexTorus/NegSmooth.lean:30`.
- `lieAddGroup_quotient` in `Jacobian/ComplexTorus/LieAddGroup.lean:29`.

That is enough source structure for the Lie group layer, assuming the file
builds. The remaining issue is the work-packet witness: `StatementBank` still
does not ask for the real `LieAddGroup` class, so `Witness.lean` can pass even
if the actual smooth group instance regresses.

### 5. Inventory text is stale relative to the completed chart layer

Severity: low

`Jacobian/WorkPackets/StatementBank.lean` still includes
`"ChartedSpace / IsManifold / LieAddGroup instance on V quotient Lambda"` in
`missingItems`, even though the charted-space and manifold parts now exist.

Suggested fix: split that inventory item into:

- completed: `ChartedSpace / IsManifold instance on V quotient Lambda`;
- missing or pending: `LieAddGroup instance on V quotient Lambda`;

or move completed items out of `missingItems`.

## Positive Notes

- `Jacobian/ComplexTorus.lean` no longer re-exports `ManifoldRecon`,
  `ZLatticeRecon`, or `DiscretenessRecon`; that addresses the largest API
  hygiene issue from the earlier review.
- The chart construction is sensibly decomposed: isolation, small-ball
  injectivity, local section, continuity, transition local-translation, and
  transition smoothness are separate proof units.
- `MkSmooth.lean` is a useful milestone because it proves the quotient
  projection is smooth as a map into the newly constructed manifold.

## Recommended Next Steps

1. Strengthen `quotientIsManifoldStatement` so the witness theorem proves the
   actual `IsManifold` instance.
2. Update README build status and next priorities to include `AddSmooth`,
   `NegSmooth`, `LieAddGroup`, and the umbrella build.
3. Split README progress accounting into charted/manifold, `mk` smoothness, and
   Lie-additive-group packaging.
4. Update `Inventory.missingItems` so completed charted-space/manifold work is
   not still listed as absent.
