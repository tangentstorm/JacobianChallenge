# Comparator harness

The [Lean comparator](https://github.com/leanprover/comparator) checks that
`Jacobian/Solution.lean` actually proves the public specification in
`Jacobian/Challenge.lean`. For each theorem listed in a config file it:

1. confirms the **statement** elaborates to the same kernel-level type in both
   modules (so the solution proves the *same* theorem, not a weaker variant), and
2. checks the solution's proof uses only the **permitted axioms**.

`Challenge.lean` is the frozen public spec — every declaration in it is a
`sorry` stub. `Solution.lean` supplies the real definitions and proofs. The
comparator is what guarantees the two line up.

## Files

- **`jacobian-smoketest.json`** — adds `sorryAx` to the permitted axioms, so it
  passes as long as every listed *statement* matches, regardless of whether the
  underlying proofs are finished. This is what GitHub CI runs.
- **`jacobian.json`** — the strict config. Permitted axioms are only `propext`,
  `Quot.sound`, `Classical.choice`; it rejects any remaining `sorry`. This is
  the final acceptance check, expected to pass once every helper is sorry-free.

Both configs list the same theorem-level declarations from `Challenge.lean`
(`genus_eq_zero_iff_homeo`, the `Jacobian.ofCurve_*` / `pushforward_*` /
`pullback_*` laws, and `pushforward_pullback`).

## How GitHub CI uses it

`.github/workflows/comparator-smoketest.yml` runs on every PR and push to
`main` that touches `Jacobian/**`, `comparator/**`, or the toolchain/manifest
files. The job:

1. installs `elan` and pulls the Mathlib cache (`lake exe cache get`);
2. clones and builds the comparator binary;
3. builds `Jacobian.Solution` (which transitively builds `Jacobian.Challenge`);
4. runs `comparator comparator/jacobian-smoketest.json`.

A green check means every listed statement in `Solution` matches `Challenge`.

## Running it locally

The comparator binary is not vendored in this repo:

```sh
# Build both modules (a normal lake build does this):
lake build Jacobian.Challenge
lake build Jacobian.Solution

# Smoketest (tolerates sorryAx — matches CI):
lake env path/to/comparator-binary comparator/jacobian-smoketest.json

# Strict (rejects sorryAx — final acceptance):
lake env path/to/comparator-binary comparator/jacobian.json
```

## Keeping the elaborated statements identical

The comparator compares the **fully-elaborated** kernel type of each theorem,
structurally — *not* up to definitional equality. So a `Solution` statement
must elaborate to the same term as the `Challenge` one, instance arguments and
all. Two ways this has drifted in the past, each a syntactic difference between
otherwise-defeq terms:

1. **ℂ instance path.** `Challenge.lean` does `import Mathlib`, so the
   `[ChartedSpace ℂ X]` / `[IsManifold 𝓘(ℂ) ω X]` binders elaborate ℂ's normed
   structure through the **C\*-algebra** instance hierarchy (`CommCStarAlgebra ℂ`,
   from `Mathlib.Analysis.CStarAlgebra.Classes`). If `Solution.lean` does not
   import that file, the same goals resolve through the `NormedField` /
   `RCLike.InnerProductSpace` hierarchy instead — defeq, but a different kernel
   term, so every ℂ-binder theorem mismatches. `Solution.lean` therefore imports
   `Mathlib.Analysis.CStarAlgebra.Classes` to pin the same path.

2. **Auto-bound instances on data definitions.** Lean includes a `variable` in a
   definition's signature only if the body references it. A `Solution`
   definition whose body needs an instance the matching `Challenge` `sorry` stub
   does not (e.g. `branchedDegree` needs `[Nonempty Y]`, supplied by the
   `[ConnectedSpace Y]` variable) picks up an extra binder, which then leaks into
   every theorem mentioning it. `ContMDiff.degree` decides `Nonempty Y`
   Classically in its body rather than taking it as an instance argument,
   precisely to keep its signature equal to `Challenge`'s.

When adding or refactoring a `Solution` declaration, dump both elaborated types
with `set_option pp.all true` and diff them (normalising universe-metavar names
like `u_1`/`u_2`, which the comparator ignores) before relying on the comparator
to catch a regression.
