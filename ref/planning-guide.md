# Formalization Planning Guide

This guide describes how to turn large mathematical blockers into work packets
that actually shrink the dependency graph.

The core rule:

> Do not keep reshaping the same frontier. If a proof is blocked, introduce the
> exact missing provider theorem, prove the current route from it, and leave
> that provider as the new direct `sorry`.

## 1. Close The Current Graph

For any assignment, identify the current target theorem and make it a
sorry-free assembly whenever possible.

Bad pattern:

```text
broad theorem sorry
→ slightly smaller record
→ projection theorem
→ another record
→ same downstream theorem still depends on the same broad idea
```

Good pattern:

```text
target theorem
→ exact missing provider theorem
→ target theorem proved from provider
→ provider becomes the new root sorry
```

Success is not just "the theorem moved." Success means the original target no
longer has a direct `sorry`, and the remaining direct `sorry` is strictly
smaller, reusable, and schedulable.

## 2. Provider Theorem Discipline

When blocked, state the missing mathematical input as a provider theorem with a
precise Lean type.

A good provider theorem:

- exposes the real mathematical data needed downstream;
- has hypotheses close to the classical theorem it represents;
- is reusable by more than one downstream assembly;
- does not mention high-level public wrappers unless unavoidable;
- is visibly smaller than the theorem it replaces.

A bad provider theorem:

- merely renames the original target;
- returns an opaque record containing every downstream conclusion;
- hides local data that future proofs will need;
- mentions the final public theorem's objects instead of the local
  mathematical mechanism.

## 3. Prove Everything Below The Provider

After introducing a provider theorem, immediately prove all downstream
projection and assembly theorems from it.

Do not leave both:

```lean
theorem public_target ... := by sorry
theorem provider ... := by sorry
```

The public target must become:

```lean
theorem public_target ... := by
  obtain ⟨data⟩ := provider ...
  exact assemble_from data
```

If the assembly itself is nontrivial, split and prove helper lemmas until the
only remaining `sorry` is the provider.

## 4. Judge Progress By Graph Shape

Total sorry count can temporarily increase if a broad blocker is split into
local leaves with real mathematical content. That is acceptable only when the
graph improves.

A split is progress if:

- the old target is direct-sorry-free;
- each new leaf is strictly local;
- each new leaf can be assigned independently;
- at least some new leaves are routine algebra/bookkeeping;
- the new leaves do not each imply the old target by themselves.

A split is not progress if:

- the new leaf is equivalent to the old theorem;
- the old theorem still has a direct `sorry`;
- the new statements are vague records with no inspectable fields;
- every downstream theorem still points to the same conceptual blocker.

## 5. Prompt Template For Blocked Workers

Use this block in worker prompts:

```text
If you cannot prove the target directly, introduce the exact missing provider
theorem with the narrowest mathematically precise statement. Then prove the target and all
downstream wrappers from that provider. Do not stop with both the original
target and the provider as direct sorries.

The provider must expose the local mathematical data needed by downstream
proofs. It must not simply package all downstream conclusions in an opaque
record.

In result.md, report:
1. the original target;
2. whether it is now direct-sorry-free;
3. the new provider theorem, if any;
4. why the provider is strictly smaller;
5. which downstream theorems now close from it;
6. axiom-check output for the original target and provider.
```

## 6. Examples

### Genus-Zero Simple Pole

Bad provider:

```lean
theorem genusZero_fixedPole_simplePoleRRSection_nonempty ... :
    Nonempty (SimplePoleRRSection X P) := by
  sorry
```

This is still the full analytic route input.

Better provider:

```lean
theorem genusZero_exists_RR_section_not_constant
    ... :
    Nonempty (RiemannRochSectionAtPoint X P) := by
  sorry
```

Then prove:

```lean
RiemannRochSectionAtPoint.toSimplePoleRRSection
genusZero_fixedPole_simplePoleRRSection_nonempty
```

from actual section/order data.

### Trace Composition

Bad provider:

```lean
theorem traceFormsBundledLM_comp ... := by
  sorry
```

This is still a global form-level functoriality theorem.

Better provider:

```lean
theorem traceAtRegularValue_comp
    ... :
    traceAtRegularValue (g ∘ f) ... =
      traceAtRegularValue g ... (traceAtRegularValue f ...) := by
  sorry
```

Then prove `traceFormsBundledLM_comp`, `traceFormsCoord_comp`, and
`traceDualPullbackLift_comp` from it.

### Polygon H1

Bad provider:

```lean
theorem edgeBasisMap_surjective ... := by
  sorry
```

Better providers:

```lean
theorem polygon4g_partial_side_arc_homologous_to_edge_chain ... := by
  sorry

theorem finite_projected_endpoint_boundary_zero_pairs ... := by
  sorry

theorem polygon4g_quotient_path_finite_lift_subdivision ... := by
  sorry
```

Then prove endpoint repair, endpoint-pair extraction, cycle repair, and
surjectivity from those local inputs.

## 7. Work Ordering

Prefer closing routine leaves before attacking hard topology or analysis.

Recommended order:

1. Algebra/bookkeeping leaves.
2. Local analytic or local topological lemmas.
3. Finite-support pairing/subdivision lemmas.
4. Classical global provider theorems.
5. Public wrapper theorems and axiom checks.

If a worker exposes both a hard geometric leaf and a routine algebra leaf, the
next prompt should usually close the routine algebra leaf first. This creates
visible progress and prevents the graph from accumulating avoidable sorries.

## 8. Result Report Standard

Every `result.md` should answer these questions:

- What was the target theorem?
- Is the target theorem direct-sorry-free now?
- What direct sorries remain?
- For each remaining sorry, is it a provider, a local lemma, or still a broad
  route theorem?
- Which downstream theorems now close from the provider?
- Does `#print axioms` show `sorryAx` for the target? If yes, through which
  provider?
- Did the total sorry count go up or down, and why?

Do not describe a theorem as "proved" without distinguishing:

- direct-sorry-free;
- transitively `sorryAx`-free;
- direct-sorry-free but depending on a provider sorry.
