# Plan for the Jacobian Challenge

This project should be treated as a Mathlib infrastructure project, not as a
single-file proof exercise. The target API in `Jacobian/Challenge.lean` is small,
but honest definitions require substantial missing theory around compact Riemann
surfaces, complex tori, holomorphic forms, integration, and degree theory.

## Current Target

The challenge asks for:

- `genus X` for a compact Riemann surface `X`;
- `Jacobian X` as a compact complex Lie additive group of dimension `genus X`;
- the Abel-Jacobi map `Jacobian.ofCurve`;
- pushforward and pullback maps on Jacobians induced by holomorphic maps;
- the degree of a holomorphic map of compact Riemann surfaces;
- functoriality and the identity `pushforward f (pullback f P) = degree f • P`.

The important constraint is that the definitions should be mathematically real,
not an abstract axiom layer that merely makes the file compile.

## Recommended Construction

Use the analytic period-lattice construction:

```text
Jacobian X = H0(X, Omega1)^dual / H1(X, Z)
```

where a homology class maps into the dual of holomorphic 1-forms by integrating
forms over cycles.

This is the most natural route for the requested API:

- `genus X` can be `finrank C H0(X, Omega1)`;
- the Jacobian is visibly a complex torus;
- the Abel-Jacobi map is defined by integrating from a base point;
- pullback is induced by pullback of holomorphic forms;
- pushforward is induced by homology pushforward or trace;
- `pushforward_pullback` follows from the trace/pullback degree identity.

## Phase 0: Project Hygiene

1. Keep `Jacobian/Challenge.lean` as the public target file.
2. Keep `Jacobian.lean` as the root export module.
3. Pin Lean and Mathlib through `lean-toolchain`, `lakefile.toml`, and
   `lake-manifest.json`.
4. Add new files only when they correspond to reusable theory, for example:

```text
Jacobian/ComplexTorus.lean
Jacobian/RiemannSurface.lean
Jacobian/HolomorphicForms.lean
Jacobian/Periods.lean
Jacobian/AbelJacobi.lean
Jacobian/Degree.lean
```

## Phase 1: Complex Tori

Build the reusable theory of quotients of finite-dimensional complex vector
spaces by full lattices.

Needed API:

- lattices in finite-dimensional real or complex vector spaces;
- quotient additive groups by discrete subgroups;
- topological group structure on `V / Lambda`;
- compactness for full-rank lattices;
- complex manifold structure on the quotient;
- Lie additive group structure;
- maps induced by continuous linear maps preserving lattices.

This phase supports the group, topology, compactness, manifold, and Lie group
instances for `Jacobian X`.

## Phase 2: Compact Riemann Surfaces and Holomorphic Forms

Define the vector space of holomorphic 1-forms on a compact Riemann surface.

Needed API:

- cotangent spaces and smooth differential 1-forms on complex manifolds;
- holomorphicity condition for 1-forms;
- vector space structure over `C`;
- finite dimensionality for compact Riemann surfaces;
- definition of genus as the dimension of this space.

The theorem `genus_eq_zero_iff_homeo` is deep with this definition. It likely
depends on classification/uniformization or serious Riemann surface theory.

## Phase 3: Integration and Periods

Develop integration of differential forms over paths and cycles on manifolds.

Needed API:

- integration of 1-forms along smooth paths;
- chain-level or homology-level integration;
- closedness of holomorphic 1-forms;
- invariance of integrals under homology;
- the period pairing

```text
H1(X, Z) -> H0(X, Omega1)^dual
```

- proof that the image is a full lattice.

This is probably the central technical bottleneck.

## Phase 4: Define the Jacobian

Once phases 1-3 exist:

```text
Jacobian X := H0(X, Omega1)^dual / periodLattice X
```

Then prove:

- additive commutative group instance;
- topological space, Hausdorff, compact space instances;
- complex charted-space and manifold instances;
- Lie additive group instance;
- dimension equals `genus X`.

## Phase 5: Abel-Jacobi Map

For a base point `P : X`, define:

```text
ofCurve P Q = class of (omega |-> integral from P to Q of omega)
```

The key proof obligation is path-independence modulo periods.

Then prove:

- `ofCurve_self`;
- holomorphicity of `ofCurve P`;
- injectivity when `0 < genus X`.

The injectivity theorem is not a small local calculation. It is a substantial
classical theorem about Abel-Jacobi maps.

## Phase 6: Degree of Holomorphic Maps

Define the degree of a holomorphic map of compact Riemann surfaces.

The intended behavior:

- constant maps have degree `0`;
- nonconstant maps have positive finite degree;
- degree is computed by generic fiber cardinality with ramification
  multiplicity.

Needed API:

- local normal form for nonconstant holomorphic maps between Riemann surfaces;
- isolated zeros and local multiplicity;
- finite fibers for nonconstant maps between compact Riemann surfaces;
- branched covering behavior;
- functoriality of degree under composition.

## Phase 7: Pushforward and Pullback

For `f : X -> Y` holomorphic:

- pullback of forms gives `H0(Y, Omega1) -> H0(X, Omega1)`;
- dualizing gives a linear map in the opposite direction;
- compatibility with period lattices gives `Jacobian Y -> Jacobian X`;
- pushforward comes from homology pushforward or the trace map on forms.

Then prove:

- `pushforward_id_apply`;
- `pushforward_comp_apply`;
- `pullback_id_apply`;
- `pullback_comp_apply`;
- holomorphicity of both maps;
- `pushforward_pullback`.

The final identity should be proved from the trace-pullback theorem:

```text
trace_f (pullback_f omega) = degree(f) * omega
```

or the equivalent statement on homology/period pairings.

## Phase 8: Mathlib Integration Strategy

Do not try to PR the entire challenge as one contribution. Split into reusable
layers:

1. quotient complex tori;
2. differential forms and holomorphic 1-forms on complex manifolds;
3. path and cycle integration for 1-forms;
4. compact Riemann surface facts;
5. period lattices;
6. Jacobian definition and basic API;
7. Abel-Jacobi map;
8. pushforward, pullback, and degree.

Each layer should have independent examples and tests before being used in the
challenge file.

## Main Risks

- The quotient manifold theory for lattices may not be complete enough in
  Mathlib yet.
- Integration of forms on manifolds may require a large amount of foundational
  work.
- Finite-dimensionality of holomorphic 1-forms is a serious theorem.
- The genus-zero classification theorem is not just an API lemma.
- Abel-Jacobi injectivity and `pushforward_pullback` depend on deep classical
  Riemann surface theory.

## First Concrete Milestone

The first useful milestone is not to solve any sorry in `Challenge.lean`.

Instead, build a standalone file proving that a finite-dimensional complex
vector space modulo a full lattice is a compact complex Lie additive group, with
maps induced by lattice-preserving continuous linear maps. That result is
reusable, reviewable, and directly needed for the eventual Jacobian definition.
