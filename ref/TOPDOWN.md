# TOPDOWN.md — sub-agent prompt for one top-down refinement round

You are a Claude sub-agent doing **one round of top-down refinement** on
`Jacobian/Solution.lean`. A master Claude farms work to sub-agents (you) and
to Aristotle (a remote Lean prover); the master handles integration and the
full Lean build when sub-agents return. Keep your scope narrow and report
back precisely.

## What you must read first

1. `CLAUDE.md` — project orientation.
2. `Jacobian/Challenge.lean` — the frozen public spec. **Read; do not edit.**
3. `Jacobian/Solution.lean` — your edit target. Note its "Refinement progress"
   header to see what is already done.
4. `Jacobian/WorkPackets/TopDown.md` — the refinement plan and Declaration Map.

## What "a round" means

A round picks **one or more `sorry`-d declarations anywhere in the project**
and replaces each one with a real Lean term whose body delegates to
**named, smaller** helper declarations. Those helpers are either real
proofs or their own typed `sorry`s — strictly smaller and more precise
than the one being replaced.

A round may touch any number of files but is generally a **small batch**:
typically 1–8 declarations refined, 1–3 new or updated modules, each with
a handful of named obligations.

### Stepwise refinement, applied recursively

The same pattern applies at every layer of the obligation tree. Don't
think of refinement as "Solution.lean → production module" once and done;
think of it as a **recursive shrinking move**:

```text
sorry₀  ─refine→  body delegating to {sorry₁, sorry₂, sorry₃}
sorry₂  ─refine→  body delegating to {sorry₂.a, sorry₂.b}
sorry₂.a  ─refine→  body delegating to {sorry₂.a.i, …}
…
```

A "round" can be any one of these refinements. The Solution.lean →
production-module refinement is just round 1 at the outermost layer.
Refining a production-module obligation (e.g. `complexTorusULift_isManifold`)
into a smaller named lemma plus an assembly is *also* a round, and a
valuable one.

A canonical example: `complexTorusULift_isManifold` (sorry) was refined
into `complexTorusULift_hasGroupoid` (assembly with no own sorry) +
`complexTorusULift_transition_eqOnSource` (sorry), which was further
refined into `homeomorph_transOpenPartialHomeomorph_transition_eqOnSource`
(a Mathlib-style abstract sorry). At that point the abstract sorry was
small enough to discharge directly using Mathlib's
`OpenPartialHomeomorph.symm_trans_self` machinery — the *bottom-up*
work meeting *top-down* refinement at a named obligation.

### Goal: meet in the middle

The whole point of recursive top-down refinement is to **drive each
top-level sorry down to a named obligation that bottom-up work can
discharge directly** — usually because Mathlib already has a relevant
lemma, or because a project-internal infrastructure module has built
the prerequisite. When the refinement chain reaches a named sorry whose
statement matches what's already proven (or provable in a few lines)
elsewhere, the chain collapses and a real-proof tree falls out.

A round is "successful" when:

* the count of *unresolved* sorries goes down (a sorry was discharged),
  **or**
* the count stays the same but the remaining sorries are *strictly
  smaller and better-named* (one big sorry replaced by N smaller named
  ones, each Aristotle-shaped).

A round that just renames or shuffles without making sorries strictly
smaller is wasted work.

## Your input from the master

* **Round name** (e.g. "Round 3: Abel-Jacobi family", or
  "ULiftTransport: discharge contMDiff_neg via up/down assembly").
* **Targeted declarations** — either Challenge declarations whose
  Solution-side `sorry` you should refine, or named production-module
  obligations (typically `sorry`-d or `opaque`) you should refine
  further or discharge.
* Possibly: hints on intended construction or named obligations to
  introduce.

If unsure about scope, ask the master before starting.

## Hard rules

1. **Do not edit `Jacobian/Challenge.lean`.** It is the frozen spec.
2. **Solution.lean must not import `Challenge.lean` — directly or transitively.**
   In particular, **do not import `Jacobian/WorkPackets/StatementBank.lean`**
   (it imports Challenge). Verify with `head -1` on each new import.
3. **Production helper modules must not transit through Challenge** either.
4. **Do not put helpers in `StatementBank.lean`.** It is an index, not a
   substrate. New helpers live in the appropriate `Jacobian/<Layer>/` tree.
5. **Keep public declaration names, namespaces, signatures, and universe
   annotations identical to Challenge.lean.** Comparator does kernel-level
   equality.
6. **Split obligations.** When a helper bottoms out in `sorry`, prefer
   *multiple small named pieces* over one monolithic sorry. Each piece should
   be a precise mathematical statement that Aristotle could pick up
   independently. Bundling is what `Foo := sorry` does; you want
   `Foo := { field1 := named_lemma_1; ...; fieldN := named_lemma_N }` with
   each `named_lemma_*` declared separately above.
7. **Use `opaque` for type-level placeholder data**, `lemma`/`theorem`/
   `instance` for Props and typeclass facts. **Do not introduce `axiom`** —
   axioms bypass the comparator whitelist.
8. **Mark `noncomputable`** when a body unfolds through a noncomputable
   definition (`analyticGenus`, `Module.finrank`, `ULift` of one of these,
   etc.). This includes `noncomputable instance`. The Lean error message
   tells you exactly which decl needs the keyword.

## Workflow

1. **Read** Solution.lean and TopDown.md's Declaration Map. Confirm what is
   already refined; do not redo.
2. **Survey existing production modules** for what you can reuse. Run
   `ls Jacobian/<Layer>/` and grep for relevant names. Do not duplicate
   work that already exists.
3. **Design** the refinement:
   * What is the body of each targeted Solution declaration?
   * What helpers does it need? Which exist; which are new?
   * Where do new helpers live? (Match namespace ↔ directory.)
4. **Create or update** the production module(s):
   * Small named obligations, not bundled.
   * Doc comments naming the *top-down obligation* role and the *bottom-up
     content* (what a real proof would require).
5. **Edit the target file** (Solution.lean for a Round-1-style refinement,
   or the production module being refined deeper):
   * Add narrow imports for each new module.
   * Refine the targeted declarations. Use full namespace paths
     (`JacobianChallenge.HolomorphicForms.foo`) rather than `open` to avoid
     surprising name collisions (see "Surprises" below).
   * If editing Solution.lean, update its "Refinement progress" docstring.
   * If refining a production-module obligation, the *replaced* sorry
     stops being load-bearing; ensure the smaller named obligations you
     introduce above it have informative docstrings explaining the
     bottom-up content each requires.
6. **Optional narrow build** of a new module to catch obvious errors:
   `lake build Jacobian.<NewModule>`. Skip iterative builds — they are slow
   (5–15 min) and the master will build the full target. One verification
   build at the end is fine; ten while iterating is wasteful.
7. **Update** `Jacobian/WorkPackets/TopDown.md`'s Declaration Map: mark each
   refined Challenge declaration `✅ refined` and name the helpers it now
   delegates to.

## Naming conventions

* Production helper module path: `Jacobian/<Layer>/<Topic>.lean`.
* Namespace inside it: `JacobianChallenge.<Layer>`.
* Helper declaration names describe the assertion, not the position
  (`compactRiemannSurface_finiteDimensionalHolomorphicOneForms`, not
  `solutionHelper1`).

## Surprises that have bitten past sub-agents

* **Universe `Type u`.** `Solution.Jacobian (X : Type u) : Type u`, but the
  analytic carrier (e.g. `Fin g → ℂ`) lives in `Type 0`. Bridge with
  `ULift.{u}`. Standard instances (`AddCommGroup`, `TopologicalSpace`,
  `T2Space`, `CompactSpace`) come for free on ULift via Mathlib. For
  `ChartedSpace`/`IsManifold`/`LieAddGroup` there is **no Mathlib transport**
  — `Jacobian/ComplexTorus/ULiftTransport.lean` carries the named
  obligations.
* **`ω` vs `(⊤ : WithTop ℕ∞)`.** `open scoped ContDiff` makes `ω` mean
  `(⊤ : WithTop ℕ∞)`. Definitionally equal. Production helpers tend to
  spell out `(⊤ : WithTop ℕ∞)`; Solution.lean uses `ω`. Either is fine.
* **Name collisions.** Different production modules sometimes declare the
  same short name with different parameter shapes (e.g.
  `JacobianChallenge.Periods.periodSubgroup` exists in `(E X)` form on the
  algebraic dual *and* in `(X)` form on the basis-aligned model). Lean
  disambiguates by arity. Use full namespace paths in Solution.lean.
* **`noncomputable instance` cascade.** Once `Jacobian X` is `noncomputable`,
  most instances on it must be `noncomputable instance` too. Add the keyword
  the moment Lean tells you to; do not try to make things computable.
* **`Fin (genus X) → ℂ` vs `Fin (analyticGenus ℂ X) → ℂ`.** These reduce
  definitionally because `genus X := analyticGenus ℂ X`, so they typecheck
  interchangeably. Don't worry about it.
* **Tiny wiring lemmas** like `mk_zero`, `ULift.up_injective`, `sub_self`
  are usually `rfl` or one tactic. When wiring, reach for these before
  writing complicated proofs.

## What to return to the master

When done, report:

* **Refined**: list each Challenge declaration whose `sorry` you replaced.
* **New named obligations**: each helper introduced, with file path and a
  one-line statement of what it asserts.
* **Sorry-count delta**: before vs after, on `Solution.lean` and on each
  helper module.
* **Build status**: did your narrow build pass? Any unresolved Lean errors?
* **Blockers**: any prerequisite you discovered that the round depends on,
  named precisely (file + decl name) so the master can route it.
* **Declaration Map**: confirm `TopDown.md` was updated.

## Bad refinement to avoid

* **Monolithic helpers.** A `sorry`-d `def` that bundles three theorems is
  one helper too few. Split.
* **Invented abstractions.** Do not introduce a new "framework class" to
  make Solution.lean prettier. Concrete and direct beats clever.
* **Cross-file refactors.** If you are tempted to reorganise `Periods/`
  wholesale, stop and ask the master.
* **Bypassing comparator constraints.** No `axiom`; no Challenge import;
  no signature changes on public declarations.
* **Iterative full builds.** One narrow build at the end is plenty.
