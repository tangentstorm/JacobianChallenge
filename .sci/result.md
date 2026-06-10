# Result — carrier representative ⟹ element + AnalyticData (statement-level)

Executed per manager triage resolution (pivot to statement-level hypotheses;
wrapper NOT imported; duplicate-decl reconciliation queued upstream).

## Exact `#print axioms` output (all four new decls — fully CLEAN, no sorryAx)

The pivot moved the taint to the future instantiation site as predicted; the
review's conditional-taint expectation (§2 of the adjusted task) turned out
PESSIMISTIC — statement-level decls carry no taint at all, so `\leanok` is
legitimate on the new node (per triage resolution §1).

```
'JacobianChallenge.HolomorphicForms.MeromorphicFunctionWithDivisors.memRiemannRochSpace_mapToSphere_of_principal_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'JacobianChallenge.HolomorphicForms.MeromorphicFunctionWithDivisors.analyticData_mapToSphere_of_simple_pole_order_one' depends on axioms: [propext, Classical.choice, Quot.sound]
'JacobianChallenge.HolomorphicForms.genusZeroPointRiemannRochElement_of_carrier_representative' depends on axioms: [propext, Classical.choice, Quot.sound]
'JacobianChallenge.HolomorphicForms.genusZeroPointRiemannRochElement_with_analyticData_of_carrier_representative' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Mathlib-search note (unblocking protocol §4.1)

No Mathlib search was required this leaf: all content is project-local
(carrier/germ/RR-element API). The one genuinely missing fact
(order-soundness) is documented as underivable (edffe9ae counter-model) and
taken as the named hypothesis.
