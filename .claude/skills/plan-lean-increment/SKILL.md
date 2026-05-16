---
name: plan-lean-increment
description: Plan the next concrete increment of established proof content on a Lean 4 sorry frontier. Given a target sorry (or set of sorries), identify the lowest-effort substantive move that either eliminates one or more sorries OR decomposes one into ≥ 20 LOC of nontrivial non-sorry proof content where that content is itself established mathematics. Hard-rejects cheating moves (axioms, opaque definitions, trivial placeholder bodies, cosmetic sorry shuffles) and changes that break the Lean build. Use whenever planning the next step on a sorry-bearing Lean file or branch.
---

## Foundational principle

> The amount of distinct established mathematical proof content in
> the world is finite. Every formalization project is, eventually, a
> walk down that fixed quantity: each real proof we write either
> establishes new ground or routes through ground already broken.
> **Progress is the net addition of established proof content** to
> what's available in the project. Operations that don't add content
> — repackaging existing sorries, postulating obligations as axioms,
> hiding work behind opaque definitions, deleting theorems to drop
> sorries — feel like motion but do not shorten the walk.

Every other section of this skill flows from this principle.

## Definition of an "increment of progress"

An increment is one of the following, AND must satisfy the build
clause below.

* **Discharge** — an absolute reduction in the project's sorry count,
  achieved by replacing a sorry with a proof that routes through real
  established content (in the repo or in Mathlib). The sorry is gone
  because we landed a new edge in the "what's established" graph.
* **Decomposition** — replacing an existing sorry's proof body with
  **≥ ~20 LOC of nontrivial non-sorry proof content**, where:
  1. the new connective tissue is itself established mathematics
     (statements + proofs whose content we'd want regardless of this
     particular decomposition); and
  2. the residual sub-sorries that survive the decomposition are
     **strictly more focused statements** that we'd want proved
     regardless of this decomposition — they are named results in
     standard textbooks / Mathlib's planned roadmap, not artifacts of
     the bookkeeping; and
  3. the new non-sorry content is **non-orphaned**: every helper
     lemma, intermediate definition, or auxiliary statement
     introduced must be transitively used by the ultimate target
     (the top-level theorem the increment is aimed at). LOC from
     helpers that are not reachable from the target's transitive
     dependency graph counts as **zero** toward the 20-LOC bar — see
     the non-orphan clause below.

### The non-orphan clause (LOC only counts if transitively used)

Substantive non-proof content only counts toward an increment's LOC
budget if it is **transitively used by the ultimate target**. Concretely:

* Verify reachability with `#print axioms` (or a `#sorries`
  enumerator that walks `getUsedConstants` from the target). A new
  lemma `L` counts toward the increment IFF removing `L` would
  produce an unbuilt downstream of the target — i.e. `L` sits on the
  descent path of the goal.
* Helpers that are sorry-free, mathematically substantial, and even
  individually reusable in *principle* but **not invoked anywhere in
  the descent of the target** count as **zero LOC** for this
  increment's budget. They are orphans relative to the target.
* Common failure mode: salvaging ~150 LOC of chart-local helpers
  that decompose a frontier sorry into a "subdivision residual," with
  the residual still sorry'd and the helpers unreferenced by the
  flagship's descent. The helpers are real mathematics, but they
  contributed zero progress toward closing the flagship.
* Operational consequence: if the planned increment cannot wire its
  new helpers into the descent within the same commit (because the
  consumer proof is too large for one increment), **do not land the
  helpers yet**. Wait until the consumer can be written in the same
  commit (or a tightly-coupled PR series that lands together). An
  orphan-landing-now-consumer-later plan is a cosmetic shuffle even
  when the helpers are mathematically valuable on their own terms.

### Increment tiers

An increment may be planned at one of two tiers — the caller (or the
invocation prompt) picks which:

* **Conservative (default, ~20 LOC)**: minimum substantive content,
  prefer routing through existing Mathlib/repo edges, leave deep
  refactors alone. Sub-sorries (if decomposing) must be tightly
  focused.
* **Ambitious (100-150 LOC, liberal new formalization)**: substantial
  new infrastructure is in scope — new definitions, new files,
  refining placeholder/opaque structures to concrete `def`s. The
  20-LOC bar becomes a floor, not a ceiling. Use when the
  conservative path is exhausted, or when a single ambitious move
  unblocks multiple downstream sorries.

Within each tier the cheating rejection list still applies. What
changes is the LOC budget and willingness to touch foundational
structure, not the principle.

### The build clause (hard, non-negotiable)

**An increment must not break the Lean build.** A proposed change is
only valid progress if, after it lands, `lake build <target>` is
green on the project's primary build target (typically `Jacobian`,
not `Jacobian.Challenge` alone, which misses downstream files). Even
a real proof that introduces a cascade of downstream type errors is
not net progress until those cascades are also patched as part of
the same increment.

Practical implication: every increment plan must end with the build
verification step, and the increment is incomplete until that step
passes. A discharge that produces 50 LOC of real proof content *but
breaks 6 downstream files* is **negative progress** until the
downstream is brought green — those 6 broken files are 6 new sorries-
in-disguise (build errors).

## What counts as cheating

Each rejection below is tagged with what the move FAILS to add to the
established-content graph.

* **Adding new `axiom` declarations** — postulates content without
  proving it; the walk is no shorter, just hidden behind an `axiom`.
  Hard rejection.
* **Refining `opaque` to `noncomputable def` with body `0`,
  `PUnit.unit`, `Classical.choice`, etc.** — postulates a value
  without computing it; adds no content. Hard rejection. (Note:
  legitimate placeholder bodies — e.g., `pathPotentialAsForm := 0`
  during a structural model refactor where the genuine content is
  captured in a separately-stated sorry'd theorem — are fine. The
  rule is about masquerading hard obligations as trivial computations,
  not about temporary structural defaults.)
* **Replacing a sorry'd theorem body with a one-line delegation to a
  single sorry'd helper** (`exact helper`, `⟨helper, helper_spec⟩`,
  etc.) — relocates the obligation without adding connective proof
  content. **Cosmetic shuffle**; hard rejection. (A real decomposition
  that ships ≥ 20 LOC of *non-trivial* connective code, with the new
  sub-sorries each on focused statements one would want proved anyway,
  is fine — it's the bare one-liner shuffle that fails.)
* **Deleting a theorem statement to reduce the sorry count** — the
  sorry was a recorded obligation; deleting it discards the
  obligation, doesn't satisfy it. Hard rejection. Theorems can only
  be removed if they're genuinely subsumed by a stronger statement.
* **"Generalizing" a theorem so its old special case becomes
  trivially provable when only the special case was the real content**
  — same problem, content not added.
* **A change that lands red on the build** — see build clause above.

## Process

1. **Map the frontier.** List every sorry in scope (target sorry +
   transitively dependent sub-sorries — those that the target's proof
   actually invokes, plus those they themselves invoke). For each:
   `file:line`, name, statement (paraphrased), and current proof-
   sketch context.

2. **Classify each candidate by feasibility.** Three buckets:
   * **Dischargeable by routing.** Existing repo or Mathlib lemmas
     chain to a real proof — the established-content graph already
     has the edges we need; we just need to wire them up. Estimate
     proof LOC; estimate risk of intermediate type-bookkeeping (e.g.
     `Bundle.Trivial` casts, `(by exact …)` codomain identifications).
   * **Decomposable with insight.** No direct discharge route, but
     the proof can be broken into named sub-statements whose combined
     non-sorry connective code is ≥ ~20 LOC of new proof content,
     *and* the new sub-sorries land on statements that are themselves
     established mathematics one would want to prove regardless of
     this decomposition. Estimate connective-tissue LOC and audit
     that the new sub-sorries are "natural" obligations, not
     artifacts.
   * **Deep frontier.** Needs an upstream model change, an external
     Mathlib lemma not in scope, or substantial new infrastructure
     (≫ 100 LOC). Defer.

3. **Predict the blast radius.** Before committing to a candidate,
   trace which downstream files import the file you'll modify and
   which of them lean on the *specific shape* of the sorry being
   discharged or decomposed. If the change risks breaking downstream
   files, either:
   * include the downstream patches as part of the increment (one
     atomic landing); or
   * pick a different candidate whose blast radius is contained.
   A green local file with red downstream files **is not an
   increment**.

4. **Rank candidates.** Prefer:
   a) discharge over decompose (less ambiguity about whether content
      was really added);
   b) decompositions whose new sub-sorries match named results in
      standard textbooks / Mathlib's planned roadmap (obviously
      natural obligations);
   c) shallower frontier (fewer transitively new statements);
   d) localized changes — small blast radius — over wide changes;
   e) discharges with a Mathlib lemma ready and waiting over those
      that require new bridging lemmas;
   f) **for ambitious tier**: prefer single moves that unblock multiple
      downstream sorries (e.g., refining one opaque def that gates 3+
      sorries) over per-sorry decompositions.

5. **Sanity-check the top candidate against the cheating list AND the
   build clause.** Explicitly state how the proposed increment avoids
   each anti-pattern, citing the principle: what proof content is
   added, where does it land in the "what's established" graph, and
   what's the predicted blast radius?

6. **Emit the plan** with the output format below.

## Anti-patterns to flag during planning

Each tagged with what it FAILS to add to the established-content graph:

* "Add a sorry'd helper that the target delegates to via `exact h`"
  → relocates the obligation; adds no content edge. Cosmetic shuffle;
  reject.
* "Refine `opaque` to `def := 0`" → no new computed value; no content.
  Placeholder collapse; reject.
* "Define a new structure / class and `Classical.choice` an inhabitant"
  → postulates inhabitant without proof; no content. Axiom in disguise;
  reject.
* "Adapt to the new model by sorrying the post-refactor theorem"
  (when the theorem is genuinely false in the new model) → flag as
  model-induced casualty rather than progress; counted as 0 yield
  toward established content. May still be the right move for
  hygiene, but don't claim it as an increment.
* "Delete a theorem to drop a sorry" → obligation is discarded, not
  satisfied. Not progress; reject.
* "Decompose A into A' and B where B's body is identical to A's and
  A's proof is `exact B`" → same content, same sorry, just two names.
  Cosmetic; reject.
* "Discharge that breaks 4 downstream files" → red build is negative
  progress; bring downstream green within the same increment, or pick
  a different target.
* **"Land 150 LOC of sorry-free chart-local / scaffolding helpers now,
  consumer next session"** → if the helpers are not transitively
  invoked by the ultimate target in the same increment, every line is
  orphan LOC: zero progress against the target's transitive sorry
  count. The salvaged content may be mathematically valuable, but the
  increment fails the non-orphan clause. Wait until the consumer can
  be written in the same commit (or a tightly-coupled PR series).
  See the non-orphan clause under "Definition of an increment of
  progress."
* **Treating an existing `noncomputable opaque` declaration as
  immovable infrastructure when its docstring or the project plan
  explicitly identifies it as the bottleneck** → mistakenly
  conservative. The cheating rule is about *hiding* obligations
  behind opacity (postulate without proof); refining an existing
  opaque to compute its content does the opposite — it adds an
  established edge to the graph. Conservative-tier plans may defer;
  ambitious-tier plans should make this a primary candidate.

## Output format

A structured plan with:

* **Target**: `file:line` + theorem name.
* **Type**: discharge / decompose.
* **Substantive content**: bullet sketch of the proof / decomposition.
  State explicitly which existing proved content (repo or Mathlib)
  the increment routes through (the "edges" we reuse) and which new
  edges we add.
* **Residual sorries**: names + statements of any new sub-sorries
  (decompose case). For each, one-line justification: why is this a
  "natural" obligation (i.e., a statement in established mathematics
  one would want to prove regardless of this particular
  decomposition)?
* **Estimated non-sorry LOC**: rough count. **Only LOC that is
  transitively used by the ultimate target counts** (non-orphan
  clause). State explicitly: which helper lemmas / definitions
  introduced by the increment are reachable from the target's
  `#print axioms` / `getUsedConstants` descent? If any helper is not
  reachable, redesign — either bundle the consumer into the same
  increment or drop the helper.
* **Predicted blast radius**: which files transitively depend on the
  modified definitions, and which need patching as part of the
  same increment.
* **Verification**: which `lake build` target should pass after the
  change (default: `lake build Jacobian` — the full library, not a
  single file), and which sorries should be present afterwards.
* **Anti-cheat check**: one-paragraph self-audit against the
  rejection list, citing the principle: what specific established-
  content edges does the increment add to the project's graph, and
  what is the build-clause status?

## Verification: `#print axioms` for transitive sorry detection

After landing a discharge, use Lean 4's `#print axioms <theorem>` to
verify the proof's closure is genuinely free of sorries:

```lean
#print axioms closedForm_pathIntegral_primitive_exists
```

Read the output:
* `sorryAx` present → the proof transitively depends on at least one
  sorry somewhere in its dependency graph. **Not done.**
* Only `propext`, `Classical.choice`, `Quot.sound` (and similar
  Mathlib-standard axioms) → genuinely closed proof. **Done.**

One-liner for shell:

```bash
echo "import <Module>
#print axioms <theorem_name>" > /tmp/check.lean
lake env lean /tmp/check.lean | grep -E "sorryAx|^\s*$"
```

Caveats:
* The output flags whether ANY sorry is reached, but not *which* one.
  To enumerate specific reachable sorries, use the `#sorries` elab
  block below.
* `noncomputable opaque` declarations without a body have no proof to
  walk — `#print axioms` cannot inspect their content. They are
  opaque, not sorry-bearing.
* A theorem whose body is locally sorry-free but whose lemma
  dependencies contain sorries WILL surface `sorryAx`. This is the
  "is my flagship REALLY proved" check that the project's sorry
  ledger cannot directly answer.

### Enumerating specific reachable sorries: `#sorries`

`#print axioms` answers "is there any sorry in the closure?" but not
"which decls carry them?" — the latter is what the **non-orphan
clause** needs: to verify that a newly introduced helper is reachable
from the target's transitive descent, you list the descent and check
whether the helper appears (or whether the residual sorries are
exactly the ones you intended).

Drop this elab into a scratch file in the project:

```lean
import <Your.Module.Containing.Target>

open Lean Elab in
elab "#sorries " n:ident : command => do
  let env ← getEnv
  let target := n.getId
  let mut sorries : Array Name := #[]
  let mut visited : Lean.NameHashSet := {}
  let mut queue : List Name := [target]
  while !queue.isEmpty do
    let next := queue.head!
    queue := queue.tail!
    if visited.contains next then continue
    visited := visited.insert next
    let some info := env.find? next | continue
    if let some v := info.value? then
      let mut hasSorry := false
      for c in v.getUsedConstants do
        if c = ``sorryAx then hasSorry := true
        if !visited.contains c then queue := c :: queue
      if hasSorry then sorries := sorries.push next
  for s in sorries do Lean.logInfo m!"SORRY: {s}"

#sorries Namespace.targetTheoremName
```

Run with `lake env lean <scratch>.lean`. Output: one line per
declaration whose *value* syntactically references `sorryAx` and that
is reachable from the target via `getUsedConstants` BFS.

**Soundness guarantee.** Every reported name is genuinely a sorry-
bearing declaration reachable from the target's transitive call graph
through declaration values. No false positives.

**Completeness — what it sees.**

* Sorries inside the value of any decl reachable via
  `getUsedConstants` from the target's value (or any decl in its
  transitive closure). This is the "is the proof body actually
  sorried" question.

**Completeness — what it does NOT see.**

* Sorries inside **types** (e.g., a `Prop`-valued field of a structure
  used in the target's type signature). The walk is over `info.value?`,
  not `info.type`. Edge case for normal theorem content, but real for
  type-level shenanigans.
* `noncomputable opaque` declarations with no body: no value to walk,
  so they are invisible — same opacity blind spot as `#print axioms`.
* Sorries hidden behind unusual reducibility tricks where
  `getUsedConstants` doesn't surface the sorry-bearing decl
  syntactically.

**Why it's the right tool for the non-orphan clause.**

Given a planned increment that introduces helpers `H₁, …, Hₙ` and
aims at target `T`:

1. After landing the increment, run `#sorries T`.
2. Confirm the reported sorry list shrank by the discharge you
   expected (or that no new orphan sorry-bearing names appeared).
3. For each new helper `Hᵢ`, confirm reachability from `T` with the
   `#reachable` elab below — if `Hᵢ` is not reachable, it is an
   orphan and the increment fails the clause regardless of how
   substantial `Hᵢ` is internally.

### Checking orphan status directly: `#reachable`

`#sorries` enumerates sorry-bearing decls reachable from a target;
`#reachable` answers the dual question — given a specific helper or
definition (the "needle"), is it reachable from the target's
transitive descent?  This is the **operational test for the
non-orphan clause**: a planned helper that is `NOT REACHABLE` from
the target counts as zero LOC toward the increment's budget.

Drop this elab into a scratch file alongside `#sorries`:

```lean
import <Your.Module.Containing.Target>

open Lean Elab in
elab "#reachable " n:ident " from " m:ident : command => do
  let env ← getEnv
  let target := m.getId
  let needle := n.getId
  let mut visited : Lean.NameHashSet := {}
  let mut queue : List Name := [target]
  let mut found := false
  while !queue.isEmpty && !found do
    let next := queue.head!; queue := queue.tail!
    if visited.contains next then continue
    visited := visited.insert next
    if next = needle then found := true
    let some info := env.find? next | continue
    if let some v := info.value? then
      for c in v.getUsedConstants do
        if !visited.contains c then queue := c :: queue
  if found then Lean.logInfo m!"REACHABLE: {needle} from {target}"
  else Lean.logInfo m!"NOT REACHABLE: {needle} from {target}"

#reachable Namespace.helperLemmaName from
  Namespace.targetTheoremName
```

Run with `lake env lean <scratch>.lean 2>&1 | grep REACHABLE` to see
just the verdicts. Typical batch usage:

```lean
#reachable Namespace.helper1 from Namespace.target
#reachable Namespace.helper2 from Namespace.target
#reachable Namespace.helper3 from Namespace.target
```

The output's a one-line `REACHABLE: …` or `NOT REACHABLE: …` per
query.

**Soundness.** A `REACHABLE` verdict is genuine: there exists a chain
of `getUsedConstants` references from `target` through declaration
values that reaches `needle`. A `NOT REACHABLE` verdict means no such
value-side chain exists — which, modulo the caveats below, means the
needle is an orphan w.r.t. the target.

**Same blind spots as `#sorries`.**

* Value-side walk only. If the needle is reached only through the
  *type* of an intermediate decl (e.g., a `Prop` field whose value
  doesn't mention the needle but whose type does), `#reachable` will
  say `NOT REACHABLE`. For ordinary helper lemmas used by name in
  proof bodies this is fine; for type-level constructions it can lie.
* `noncomputable opaque` declarations have no body to walk — the
  walk can't traverse through them.
* Definitional unfolding tricks where `getUsedConstants` doesn't
  surface the needle name syntactically.

**Workflow for the non-orphan clause.**

When planning an increment introducing helpers `H₁, …, Hₙ` aimed at
target `T`:

1. Sketch the planned consumer chain (what calls `Hᵢ`, transitively
   up to `T`).
2. After landing the increment, run `#reachable Hᵢ from T` for each
   `i`.
3. Every `Hᵢ` must come back `REACHABLE`. If any returns `NOT
   REACHABLE`, that helper is orphan LOC: either wire it into the
   consumer chain in the same commit, or drop it from the increment.

This is the test that catches the chart-local Stokes salvage failure
mode — landing 150 LOC of sorry-free helpers whose only intended
consumer is still sorry'd will return `NOT REACHABLE` for every
helper, exposing the increment as orphan-bearing.

## Usage

Invoke this skill when planning the next step on a sorry-bearing Lean
branch. Provide the target sorry's `file:line` + name, or the broader
sorry frontier; the skill emits a ranked plan of the next 1–3
increments, each of which provably adds established proof content to
the project AND keeps the build green.
