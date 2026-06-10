# Germ-to-map bridge Phase 0: paper proof of the representation step

## Problem Statement

The open bridge is:

```lean
genusZero_pointRiemannRochElement_of_germSpace_outside_constants
```

Its input is:

```lean
F : RiemannRochGermSpace X (Divisor.point P)
hF : (F : MeromorphicGermFamily X) ∉ constantGermFamilyLine X
```

and its output is:

```lean
Nonempty (GenusZeroPointRiemannRochElement X P h)
```

where `GenusZeroPointRiemannRochElement` packages a
`MeromorphicMapToSphere X`, its `Nonconstant` proof, and its membership in
`L([P])`:

```lean
structure GenusZeroPointRiemannRochElement ... where
  meromorphicMap : MeromorphicMapToSphere X
  nonconstant : meromorphicMap.Nonconstant
  mem_L_point : meromorphicMap.MemRiemannRochSpace (Divisor.point P)
```

The key representation issue is that

```lean
RiemannRochGermSpace X D
```

is not a space of concrete functions. It is the submodule

```lean
Submodule.span ℂ
  (Set.range fun s : RiemannRochBoundedSection X D =>
    s.toMeromorphicFunctionWithDivisors.germs)
```

inside `MeromorphicGermFamily X`. Thus an arbitrary `F` is only known as a
finite `ℂ`-linear combination of germ families of bounded sections. The bridge
must realize that finite germ-family sum as an honest divisor-compatible
meromorphic function/map. The hard point is pole cancellation: the sum is
valid in local `Filter.Germ`s, but pointwise `OnePoint ℂ` addition cannot be
used to construct the global map because it sends any summand equal to `∞` to
`∞` and loses cancellation.

## Construct-First Route

The implementation should construct a representative first, then reuse the
existing transfer lemmas.

### 1. Extract a finite span expression

Unfold only the carrier definition enough to obtain a finite expression for
`F` as a `ℂ`-linear combination of generators

```lean
sᵢ.toMeromorphicFunctionWithDivisors.germs
```

where each

```lean
sᵢ : RiemannRochBoundedSection X (Divisor.point P)
```

comes with

```lean
sᵢ.memRiemannRochSpace :
  sᵢ.toMeromorphicFunctionWithDivisors.MemRiemannRochSpace (Divisor.point P)
```

Existing declarations:

- `RiemannRochGermSpace`
- `RiemannRochBoundedSection`
- `RiemannRochBoundedSection.germs_mem_RiemannRochGermSpace`
- `RiemannRochBoundedSection.toRiemannRochGermSpace`
- `RiemannRochBoundedSection.toRiemannRochGermSpace_val`

Routine packaging needed:

```lean
RiemannRochGermSpace.exists_finset_sum_generators
```

or an equivalent lemma over `Submodule.mem_span` that exposes a `Finset`,
coefficients, and bounded-section generators. This is routine linear-algebra
packaging, not the analytic obstruction.

### 2. Normalize scalar multiples

For each nonzero coefficient, use the existing nonzero scalar constructors:

```lean
MeromorphicFunctionWithDivisors.smulNonzero
RiemannRochBoundedSection.smulNonzero
MeromorphicFunctionWithDivisors.smulNonzero_memRiemannRochSpace_iff
```

Zero coefficients can be removed from the finite support before the analytic
construction. Nonzero scalar multiplication is already sound because it
preserves zero, pole, principal, and order data and has the correct germ-family
equation.

Routine packaging needed:

```lean
RiemannRochBoundedSection.smulNonzero_toRiemannRochGermSpace_val
```

or a small rewrite lemma identifying the generator after scalar multiplication.

### 3. Build the finite sum by iterated divisor-compatible addition

The available addition interface is conditional:

```lean
MeromorphicFunctionWithDivisors.AddData
RiemannRochBoundedSection.AddData
RiemannRochBoundedSection.AddData.result
RiemannRochBoundedSection.AddData.germs_eq_add
MeromorphicFunctionWithDivisors.AddData.result_memRiemannRochSpace
```

These declarations are consumers of an already-constructed sum. They are not
constructors for the sum. The missing analytic step is therefore:

```lean
MeromorphicFunctionWithDivisors.addData_of_germ_sum
```

with a shape like:

```lean
theorem MeromorphicFunctionWithDivisors.addData_of_same_bound
    (f g : MeromorphicFunctionWithDivisors X)
    (D : Divisor X)
    (hf : f.MemRiemannRochSpace D)
    (hg : g.MemRiemannRochSpace D) :
    Nonempty (MeromorphicFunctionWithDivisors.AddData f g)
```

or, more narrowly for the current task:

```lean
theorem RiemannRochBoundedSection.addData_point
    (s t : RiemannRochBoundedSection X (Divisor.point P)) :
    Nonempty (RiemannRochBoundedSection.AddData s t)
```

The proof cannot use pointwise `OnePoint` addition. It must construct the
finite lift of the sum locally from the meromorphic germ representatives,
prove the local definitions agree on overlaps, glue them to a global
`MeromorphicFunctionType`, and then construct compatible divisor fields for
the resulting `MeromorphicFunctionWithDivisors`. Its required fields are
visible in `MeromorphicFunctionWithDivisors.AddData`:

- `germs_eq_add`, the exact germ-level sum;
- `order_le_result`, where strict inequality records pole cancellation;
- `toFun_eq_on_common_regular`, only at points where both summands are finite;
- `memRiemannRochSpace_of_mem`, preserving the chosen divisor bound.

This is the main NEW ANALYTIC WORK.

### 4. Fold the finite expression

Once pairwise addition data exists, define an iterated sum over the finite span
expression by induction on the `Finset`. Each induction step uses
`RiemannRochBoundedSection.AddData.result` and
`RiemannRochBoundedSection.AddData.germs_eq_add`. The final bounded section

```lean
sF : RiemannRochBoundedSection X (Divisor.point P)
```

should satisfy

```lean
sF.toMeromorphicFunctionWithDivisors.germs = (F : MeromorphicGermFamily X)
```

and still has

```lean
sF.memRiemannRochSpace
```

by the additive membership-preservation fields.

Routine packaging needed:

```lean
RiemannRochGermSpace.exists_boundedSection_representative
```

with target shape:

```lean
∃ s : RiemannRochBoundedSection X (Divisor.point P),
  s.toMeromorphicFunctionWithDivisors.germs = (F : MeromorphicGermFamily X)
```

This lemma is routine once Step 3 is available.

### 5. Convert the bounded-section representative to a sphere map

From

```lean
g := sF.toMeromorphicFunctionWithDivisors
```

construct a `MeromorphicMapToSphere X` with

```lean
toMap := g.toFunction.toFun
```

and transfer the divisor and `L([P])` membership fields. The forward lane in
the repository currently goes from a `MeromorphicMapToSphere` with analytic
data to a `MeromorphicFunctionWithDivisors`:

```lean
MeromorphicMapToSphere.toMeromorphicFunctionWithDivisors
MeromorphicMapToSphere.memRiemannRochSpace_toMeromorphicFunctionWithDivisors
MeromorphicMapToSphere.toRiemannRochBoundedSection
MeromorphicMapToSphere.toRiemannRochBoundedSection_coe
genusZero_riemannRochBoundedSection_of_nonconstant_mem_L_point
genusZero_riemannRochBoundedSection_of_GenusZeroPointRiemannRochElement
```

The bridge needs the reverse packaging direction:

```lean
MeromorphicFunctionWithDivisors.toMeromorphicMapToSphere
```

or a narrower constructor:

```lean
RiemannRochBoundedSection.toMeromorphicMapToSphere
```

This should be mostly packaging if `MeromorphicFunctionWithDivisors.toFunction`
already satisfies the fields required by `MeromorphicMapToSphere`. Its
membership field follows from `sF.memRiemannRochSpace`.

### 6. Transfer nonconstancy from the outside-constant hypothesis

This part is supplied by commit `111ff1df`. The exact declarations are:

```lean
MeromorphicFunctionType.germAt_eq_constant_of_forall_toFun_eq
MeromorphicFunctionWithDivisors.germs_mem_constantGermFamilyLine_of_forall_toFun_eq
MeromorphicFunctionWithDivisors.nonconstant_of_germs_notMem_constantGermFamilyLine
```

After Step 4 gives

```lean
sF.toMeromorphicFunctionWithDivisors.germs = (F : MeromorphicGermFamily X)
```

the hypothesis `hF` rewrites to

```lean
sF.toMeromorphicFunctionWithDivisors.germs ∉ constantGermFamilyLine X
```

and
`MeromorphicFunctionWithDivisors.nonconstant_of_germs_notMem_constantGermFamilyLine`
gives the `MeromorphicMapToSphere.Nonconstant`-shaped proof for the map whose
`toMap` is `g.toFunction.toFun`.

### 7. Package the final bridge

With the map `f`, nonconstancy, and membership in `L([P])`, return:

```lean
⟨{ meromorphicMap := f
   nonconstant := ...
   mem_L_point := ... }⟩
```

Then the existing B-RR3f theorem

```lean
genusZero_pointRiemannRochElement_of_germSpaceDimensionInput
```

continues to consume the bridge and needs no redesign.

## Supplied Pieces

Do not redo the following work:

- Linear carrier and constant-line setup:
  `RiemannRochGermSpace`, `constantGermFamilyLine`,
  `constantGermFamilyLine_le_RiemannRochGermSpace`,
  `constantGermFamilyLineInRiemannRoch_finrank`, and
  `genusZero_pointRiemannRochGermSpace_exists_outside_constants`.
- Conditional extraction above this bridge:
  `genusZero_pointRiemannRochElement_of_germSpaceDimensionInput`.
- Forward map-to-carrier membership bookkeeping from jc3:
  `MeromorphicMapToSphere.toMeromorphicFunctionWithDivisors`,
  `MeromorphicMapToSphere.memRiemannRochSpace_toMeromorphicFunctionWithDivisors`,
  `MeromorphicMapToSphere.toRiemannRochBoundedSection`, and
  `genusZero_riemannRochBoundedSection_of_nonconstant_mem_L_point`.
- Nonconstancy transfer from commit `111ff1df`:
  `MeromorphicFunctionWithDivisors.nonconstant_of_germs_notMem_constantGermFamilyLine`
  and its constant-line precursor
  `MeromorphicFunctionWithDivisors.germs_mem_constantGermFamilyLine_of_forall_toFun_eq`.

## NEW ANALYTIC WORK

Genuinely hard missing content:

1. `MeromorphicFunctionWithDivisors.addData_of_same_bound` or the narrower
   `RiemannRochBoundedSection.addData_point`: construct the actual meromorphic
   sum of two divisor-compatible representatives with the same RR bound. This
   is where pole cancellation must be proved at the function level.
2. A local-to-global gluing lemma for finite-lift representatives of compatible
   meromorphic germs. A likely target is:

   ```lean
   MeromorphicGermFamily.exists_meromorphicFunctionWithDivisors_of_finite_sum
   ```

   or the more local

   ```lean
   MeromorphicGermAt.add_representatives_compatible_on_overlaps
   ```

   feeding the `AddData` constructor.
3. Divisor/order extraction for the constructed sum: prove the sum has finite
   zero and pole divisors, prove `principalDivisor = zeroDivisor - poleDivisor`,
   prove disjointness of zero/pole supports, and prove the `L([P])` membership
   preservation field.
4. Reverse packaging:

   ```lean
   MeromorphicFunctionWithDivisors.toMeromorphicMapToSphere
   ```

   or

   ```lean
   RiemannRochBoundedSection.toMeromorphicMapToSphere
   ```

   if not already derivable from `MeromorphicFunctionWithDivisors.toFunction`.

Routine packaging after those hard leaves:

1. Expose finite span expressions from `Submodule.span`.
2. Fold a finite list of bounded sections using pairwise `AddData`.
3. Rewrite the final representative's germs to the original `F`.
4. Apply the supplied nonconstancy transfer and package
   `GenusZeroPointRiemannRochElement`.

## Carrier Decision

Choose to add an order-`orderAt` compatibility field to
`MeromorphicFunctionWithDivisors`, but only as a separate micro task. The
current carrier records `order : X → WithTop ℤ` and derives divisor
coefficients from it, yet it does not assert that this order is the analytic
order of the recorded germ or finite lift. jc2's counter-model shows that the
germ-order bridge is unsound without such a field: a carrier could have correct
shape fields while lying about analytic order. Adding the field is the right
long-term choice because the addition constructor must prove exactly how pole
cancellation changes order. It should not be bundled into the representation
bridge proof, because every existing constructor for
`MeromorphicFunctionWithDivisors` must migrate.

---

# jc3 appendix — recorded verification outputs (kept per task instructions)

## Carrier-representative pipeline (d7b91877): exact `#print axioms` output

All four statement-level decls fully clean (no sorryAx):

```
'JacobianChallenge.HolomorphicForms.MeromorphicFunctionWithDivisors.memRiemannRochSpace_mapToSphere_of_principal_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'JacobianChallenge.HolomorphicForms.MeromorphicFunctionWithDivisors.analyticData_mapToSphere_of_simple_pole_order_one' depends on axioms: [propext, Classical.choice, Quot.sound]
'JacobianChallenge.HolomorphicForms.genusZeroPointRiemannRochElement_of_carrier_representative' depends on axioms: [propext, Classical.choice, Quot.sound]
'JacobianChallenge.HolomorphicForms.genusZeroPointRiemannRochElement_with_analyticData_of_carrier_representative' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Span-expression extraction package (this commit): exact `#print axioms` output

```
'JacobianChallenge.HolomorphicForms.RiemannRochGermSpace.exists_finset_sum_generators' depends on axioms: [propext, Classical.choice, Quot.sound]
'JacobianChallenge.HolomorphicForms.RiemannRochGermSpace.exists_finset_sum_generators'' depends on axioms: [propext, Classical.choice, Quot.sound]
'JacobianChallenge.HolomorphicForms.RiemannRochBoundedSection.smulNonzero_germs' depends on axioms: [propext, Classical.choice, Quot.sound]
'JacobianChallenge.HolomorphicForms.RiemannRochBoundedSection.smulNonzero_toRiemannRochGermSpace_val' depends on axioms: [propext, Classical.choice, Quot.sound]
```
