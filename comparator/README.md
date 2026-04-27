# Comparator harness

Configuration files for the [Lean comparator](https://github.com/leanprover/comparator),
which verifies kernel-level declaration equivalence between
`Jacobian/Challenge.lean` (the frozen public spec) and
`Jacobian/Solution.lean` (the top-down refinement target).

This is **Round 0** of `Jacobian/WorkPackets/TopDown.md`.

## Files

- **`jacobian.json`** — final config. Permitted axioms: `propext`,
  `Quot.sound`, `Classical.choice`. Will reject any imported helper
  that contains `sorry`. Use this once all production-module
  obligations are discharged.
- **`jacobian-staged.json`** — staged-refinement config. Identical to
  the final config except `sorryAx` is added to `permitted_axioms`.
  Use this during refinement to smoke-test that declaration shapes
  match (independently of whether helpers are fully proven).

## Usage

The comparator binary is not installed in this repo. To run:

```sh
# Once comparator is checked out / installed elsewhere, point at the
# config from this directory:
lake env path/to/comparator-binary comparator/jacobian-staged.json
```

The first smoke-test should be against `jacobian-staged.json` to confirm
declaration shapes; the next is against `jacobian.json` once a sufficient
subset of the bottom-up obligations is discharged.

## Theorem-name list

Per `Jacobian/WorkPackets/TopDown.md`'s "Comparator Role" section, the
list contains theorem-level declarations only. Open question recorded
there: *"determine whether comparator should also list data declarations
such as `genus`, `Jacobian`, `Jacobian.ofCurve`, `Jacobian.pushforward`,
`Jacobian.pullback`, and `ContMDiff.degree`"*. Until that is resolved,
keep this list theorem-only.

## Known issue: data-level universe divergence (post-keystone)

After the **keystone refactor** (commit `952e750`,
"Keystone: route basisAlignedPeriodSubgroup to concrete representative"),
`Jacobian/Solution.lean` specialises the data-level declarations
(`genus`, `Jacobian`, `ofCurve`, `pushforward`, `pullback`,
`ContMDiff.degree`) to `(X : Type)` — i.e. universe `0`.

`Challenge.lean` keeps these at `(X : Type u)` / `(X : Type*)`.

**Why:** `Jacobian.Periods.basisAlignedPeriodSubgroup` (and hence
`periodFullComplexLattice`) routes through
`Jacobian.Periods.basisAlignedPeriodSubgroupConcrete`, which transitively
depends on `IntegralOneCycle`, which is locked at `Type 0` because
Mathlib's `singularHomologyFunctor` requires `HasCoproducts.{w} (ModuleCat ℤ)`
and only `w = 0` is available out of the box.

**Consequence for comparator:** because every theorem in `theorem_names`
above mentions `Jacobian X` (which now has different universe shape in
Solution vs Challenge), the kernel-level declaration types do not match
strictly. Comparator's strict declaration-equivalence check will
report a mismatch on every entry until the universe story is repaired.

**Paths to repair (long-term):**

1. **Wait for / contribute** a Mathlib instance
   `HasCoproducts.{u} (ModuleCat ℤ)` (or equivalent), unlocking
   `IntegralOneCycle (X : Type*)`.
2. **Replace** the singular-homology construction in `IntegralOneCycle`
   with a universe-polymorphic alternative (e.g. a hand-rolled
   integer-cycle module, or a direct construction via `Path` /
   `FundamentalGroupoid` quotients that doesn't transit through the
   categorical homology functor).
3. **Bypass** the period-subgroup construction at the universe level
   via a "abstract period data" structure that lives at `Type*`
   (the period subgroup as a chosen `AddSubgroup (Fin g → ℂ)` with
   abstract closedness/discreteness/compactness witnesses, with the
   `Type 0` concrete realisation supplied as a separate theorem).

Until one of those lands, the staged-refinement workflow uses
`jacobian-staged.json` for shape-checking everything except the universe
mismatch, and the universe mismatch is documented as a tracked obligation.

## Smoke test (when binary is available)

```sh
# 1. Build both modules (done by the project's normal lake build):
lake build Jacobian.Challenge
lake build Jacobian.Solution

# 2. Run the staged-refinement comparator:
lake env path/to/comparator-binary comparator/jacobian-staged.json
# Expected (until universe issue resolved): mismatch on every theorem
# due to `Jacobian X`'s universe shape. Record exact error text.

# 3. Once universe issue resolved, run the final config:
lake env path/to/comparator-binary comparator/jacobian.json
# Expected (when bottom-up obligations are discharged): pass.
```
