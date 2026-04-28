import Mathlib

/-!
# Reconnaissance: `OnePoint ℂ` as a complex manifold (ℂℙ¹)

This file is a recon document surveying the Mathlib v4.28.0 API relevant
to constructing a *complex* manifold structure on `OnePoint ℂ`, the
one-point compactification of `ℂ`, which as a topological space is
homeomorphic to the Riemann sphere `S²`.

This is step (1) of the 3-step plan from the integrated `aadb7721`
survey for the genus-zero classification's HARD direction, and is also
useful for step (1') of the easy direction's plan (`027bb9d7`).  Both
are currently off the critical path.

**Status**: documentation-only recon. No production declarations.

Pinned commit: `leanprover/lean4:v4.28.0`; Mathlib commit
`8f9d9cff6bd728b17a24e163c9402775d9e6a365`.

---

## 1. What Mathlib v4.28.0 has

### 1.1 `OnePoint` topology

All API lives in `Mathlib/Topology/Compactification/OnePoint/Basic.lean`
(plus the `Sphere.lean` and `ProjectiveLine.lean` siblings; see below).

| Declaration | Path | Notes |
|---|---|---|
| `OnePoint X` | `Topology/Compactification/OnePoint/Basic.lean` | `Option X` with the one-point-compactification topology |
| `OnePoint.instTopologicalSpace` | same | Open sets: either `(↑) '' s` for open `s : Set X`, or complements of `(↑) '' K` for compact closed `K` |
| `OnePoint.some : X → OnePoint X` | same | The coercion; also accessible via `↑` / `CoeTC` |
| `OnePoint.infty : OnePoint X` | same | The point at infinity, notation `∞` |
| `CompactSpace (OnePoint X)` | same (line 498) | Always an instance (the whole point of one-point compactification) |
| `T1Space (OnePoint X)` | same (line 513) | Requires `[T1Space X]` |
| `T4Space (OnePoint X)` | same (line 538, as `example`) | Requires `[WeaklyLocallyCompactSpace X] [T2Space X]`; `T2Space` follows |
| `ConnectedSpace (OnePoint X)` | same (line 541) | Requires `[PreconnectedSpace X] [NoncompactSpace X]` |
| `NormalSpace (OnePoint X)` | same (line 522) | Requires `[WeaklyLocallyCompactSpace X] [R1Space X]` |
| `OnePoint.isOpenEmbedding_coe` | same (line 271) | `IsOpenEmbedding ((↑) : X → OnePoint X)` |
| `OnePoint.isOpenMap_coe` | same (line 269) | `IsOpenMap ((↑) : X → OnePoint X)` |
| `OnePoint.continuous_coe` | same (line 266) | `Continuous ((↑) : X → OnePoint X)` |
| `OnePoint.isOpen_range_coe` | same (line 274) | The finite part `range (↑)` is open |
| `OnePoint.isClosed_infty` | same (line 277) | `{∞}` is closed |

**For `X = ℂ`**: since `ℂ` is a locally compact T₂ (in fact T₄) space, the
following all hold by typeclass inference:

```
CompactSpace (OnePoint ℂ)      -- ✓
T1Space (OnePoint ℂ)           -- ✓
T2Space (OnePoint ℂ)           -- ✓ (from T4Space)
T4Space (OnePoint ℂ)           -- ✓
NormalSpace (OnePoint ℂ)       -- ✓
ConnectedSpace (OnePoint ℂ)    -- ✓
```

All verified via `inferInstance` against this Mathlib version.

### 1.2 `OnePoint ↔ ℙ¹(K)` (set-theoretic)

`Mathlib/Topology/Compactification/OnePoint/ProjectiveLine.lean`:

| Declaration | Notes |
|---|---|
| `OnePoint.equivProjectivization K` | `OnePoint K ≃ ℙ K (K × K)` for any division ring `K` |
| `GL(2,K)` action on `OnePoint K` | Möbius transformations; `smul_infty_eq_ite`, `smul_some_eq_ite` |

The TODO in that file notes: "Add the extension of this equivalence to
a homeomorphism in the case `K = ℝ`."  There is **no** topology on
`ℙ K (K × K)` that would make the equivalence a homeomorphism, and no
complex-analytic structure is defined here.

### 1.3 `OnePoint V ≃ₜ S^n` (topological)

`Mathlib/Topology/Compactification/OnePoint/Sphere.lean`:

| Declaration | Notes |
|---|---|
| `onePointHyperplaneHomeoUnitSphere` | `OnePoint (ℝ ∙ v)ᗮ ≃ₜ sphere (0 : E) 1` for unit `v` |
| `onePointEquivSphereOfFinrankEq` | `OnePoint V ≃ₜ sphere (0 : EuclideanSpace ℝ ι) 1` when `finrank ℝ V + 1 = card ι` |

For `V = ℂ` (with `finrank ℝ ℂ = 2`), we get:

```
noncomputable def onePointCxHomeoS2 :
    OnePoint ℂ ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 :=
  onePointEquivSphereOfFinrankEq (by simp [Complex.finrank_real_complex])
```

This compiles cleanly.  The homeomorphism is built via stereographic
projection: `stereographic_symm` embeds `(ℝ ∙ v)ᗮ` into the sphere as an
open set whose complement is `{⟨v, …⟩}`, then `OnePoint.equivOfIsEmbeddingOfRangeEq`
extends this to a homeomorphism from `OnePoint` to the sphere.

### 1.4 Sphere `ChartedSpace` and `IsManifold` (real, not complex)

`Mathlib/Geometry/Manifold/Instances/Sphere.lean`:

| Declaration | Notes |
|---|---|
| `EuclideanSpace.instChartedSpaceSphere` | `ChartedSpace (EuclideanSpace ℝ (Fin n)) (sphere (0 : E) 1)` when `finrank ℝ E = n + 1` |
| `EuclideanSpace.instIsManifoldSphere` | `IsManifold (𝓡 n) ω (sphere (0 : E) 1)` |
| `stereographic hv` | `OpenPartialHomeomorph (sphere (0 : E) 1) (ℝ ∙ v)ᗮ` — stereographic projection from unit vector `v` |

**Important**: These are **real** manifold structures.  For `S²`, the
model space is `EuclideanSpace ℝ (Fin 2) ≅ ℝ²`, **not** `ℂ`.  There
is no `ChartedSpace ℂ (sphere ...)` instance in Mathlib.

For `Circle` (`S¹ ⊂ ℂ`), there are:
- `ChartedSpace (EuclideanSpace ℝ (Fin 1)) Circle`
- `IsManifold (𝓡 1) ω Circle`
- `LieGroup (𝓡 1) ω Circle`

Again, these are real manifold structures.

### 1.5 `ChartedSpace` / `IsManifold` infrastructure

`Mathlib/Geometry/Manifold/ChartedSpace.lean` and
`Mathlib/Geometry/Manifold/IsManifold/Basic.lean`:

| Declaration | Notes |
|---|---|
| `ChartedSpace H M` | Atlas of `OpenPartialHomeomorph M H` covering `M` |
| `IsManifold I n M` | `HasGroupoid M (contDiffGroupoid n I)` — chart transitions `C^n` |
| `OpenPartialHomeomorph.singletonChartedSpace` | One-chart atlas from `e.source = univ` |
| `IsOpenEmbedding.singletonChartedSpace` | Atlas from an open embedding `M ↪ H` |
| `contDiffGroupoid n I` | Structure groupoid of `C^n` partial homeomorphisms |
| `HasGroupoid.mk` | Verify chart transitions are in the groupoid |
| `modelWithCornersSelf ℂ ℂ` | The model `𝓘(ℂ, ℂ)` for complex 1-manifolds |
| `chartedSpaceSelf : ChartedSpace H H` | Model space is trivially charted over itself |

**No two-chart atlas construction exists in Mathlib.** All existing
`ChartedSpace` instances are either:
- `chartedSpaceSelf` (identity),
- `singletonChartedSpace` (one chart covering everything),
- the sphere atlas (stereographic from each pole), or
- `Icc` (boundary charts).

The sphere atlas (`instChartedSpaceSphere`) is the closest analogue to
what we need, but it uses `stereographic` (a real-analytic chart) and
the charts are indexed by points of the sphere, not by a fixed two-element set.

### 1.6 `OpenPartialHomeomorph` API

`Mathlib/Topology/OpenPartialHomeomorph/Defs.lean` and siblings:

| Declaration | Notes |
|---|---|
| `OpenPartialHomeomorph X Y` | Partial homeomorphism with open source and target |
| `OpenPartialHomeomorph.mk` | Constructor: `PartialEquiv` + open source + open target + continuity proofs |
| `OpenPartialHomeomorph.refl` | Identity |
| `OpenPartialHomeomorph.symm` | Inverse |
| `OpenPartialHomeomorph.trans` | Composition (on overlaps) |
| `OpenPartialHomeomorph.restr` | Restriction to an open set |

These are the building blocks for constructing charts by hand.

### 1.7 Smoothness of inversion

| Declaration | Path | Notes |
|---|---|---|
| `contDiffAt_inv 𝕜` | `Analysis/Calculus/ContDiff/NormedField.lean` | `ContDiffAt 𝕜 n Inv.inv x` for `x ≠ 0` |
| `AnalyticAt.inv` | `Analysis/Analytic/Constructions.lean` | `AnalyticAt 𝕜 f⁻¹ x` when `f x ≠ 0` |

These give `C^∞` (in fact analytic) smoothness of `z ↦ 1/z` on `ℂ \ {0}`,
which is the key ingredient for the chart-transition proof.

---

## 2. What's missing / needs to be built

### 2.1 `ChartedSpace ℂ (OnePoint ℂ)` — **MISSING**

This is the core missing piece. There is **no** `ChartedSpace ℂ X`
instance for `OnePoint ℂ` (or any one-point compactification) in Mathlib.
Building this requires two charts:

- **Chart 1 (identity near 0)**: the open embedding
  `(↑) : ℂ → OnePoint ℂ` gives a partial homeomorphism
  `OnePoint ℂ ⊇ range (↑) → ℂ` with source `{∞}ᶜ` (which is open by
  `OnePoint.isOpen_range_coe`). This is essentially
  `OnePoint.isOpenEmbedding_coe.toOpenPartialHomeomorph` restricted or
  extended.

- **Chart 2 (inversion near ∞)**: a partial homeomorphism
  `OnePoint ℂ ⊇ {0}ᶜ → ℂ` sending `∞ ↦ 0` and `↑z ↦ 1/z`. The source
  is `{↑0}ᶜ`, which is open (since `{↑0}` is closed in a T₁ space).
  The target is all of `ℂ`. Building this chart requires more work:
  one must show that `z ↦ 1/z` is a homeomorphism from `ℂ \ {0}` to
  itself, then extend it to send `∞ ↦ 0`.

### 2.2 The inversion chart as `OpenPartialHomeomorph (OnePoint ℂ) ℂ` — **MISSING**

This is the main technical construction.  Strategy:

1. Define `invChart : OnePoint ℂ → ℂ` by `∞ ↦ 0`, `↑z ↦ z⁻¹`
   (with the convention `(0 : ℂ)⁻¹ = 0` in Lean/Mathlib).
2. Show `invChart` is continuous at `∞` (filter argument: `z⁻¹ → 0`
   as `z → ∞`).
3. Show `invChart` is continuous at every `↑z ≠ ↑0` (from `contDiffAt_inv`
   or direct continuity of `Inv.inv`).
4. Show `invChart` restricted to `{↑0}ᶜ` is injective (separate cases
   `∞` and `↑z` with `z ≠ 0`).
5. Show the image is `ℂ` (surjectivity: `0` is hit by `∞`, every
   nonzero `w` is hit by `↑(w⁻¹)`).
6. Show the inverse map is continuous (same argument, reversed).
7. Package as `OpenPartialHomeomorph (OnePoint ℂ) ℂ` with
   `source = {↑0}ᶜ`, `target = Set.univ`.

Note: the convention `(0 : ℂ)⁻¹ = 0` means `invChart (↑0) = 0`, which
coincides with `invChart ∞ = 0`, so `invChart` is **not** injective on
all of `OnePoint ℂ`. This is fine — the chart's source is `{↑0}ᶜ`, which
excludes `↑0`.

### 2.3 `IsManifold (modelWithCornersSelf ℂ ℂ) ⊤ (OnePoint ℂ)` — **MISSING**

After constructing `ChartedSpace ℂ (OnePoint ℂ)`, one needs to verify
chart transitions are `C^∞` (or `C^ω`).  The only nontrivial transition
is the overlap of Chart 1 and Chart 2 on `{∞}ᶜ ∩ {↑0}ᶜ ≅ ℂ \ {0}`:

```
  Chart1⁻¹ ∘ Chart2 : ℂ \ {0} → ℂ \ {0},  z ↦ z⁻¹
  Chart2⁻¹ ∘ Chart1 : ℂ \ {0} → ℂ \ {0},  z ↦ z⁻¹
```

Both are `z ↦ z⁻¹`, which is `C^∞` on `ℂ \ {0}` by
`contDiffAt_inv ℂ (hx : x ≠ 0)`.

For `n = ⊤` (smooth), the `IsManifold` obligation is exactly
`ContDiffOn ℂ ⊤ Inv.inv (Set.univ \ {0})`, which follows from
`contDiffAt_inv`.

### 2.4 No existing `ChartedSpace ℂ` for `S²` — **MISSING**

The sphere `S²` has `ChartedSpace (EuclideanSpace ℝ (Fin 2))` and
`IsManifold (𝓡 2)`, but **not** `ChartedSpace ℂ`.  To get a
*complex* manifold structure on `S²`, one would need to:

1. Identify `EuclideanSpace ℝ (Fin 2) ≃ₗ[ℝ] ℂ` (as real vector spaces),
2. Replace the model with `𝓘(ℂ, ℂ)` (which is `modelWithCornersSelf ℂ ℂ`),
3. Verify the (now complex) chart transitions are holomorphic.

This is nontrivial because the stereographic charts from `Sphere.lean`
are defined using real inner-product geometry, and their transitions
involve the real formula for stereographic projection, not complex
inversion.  The direct route via `OnePoint ℂ` is cleaner.

---

## 3. Three-step Mathlib API plan for implementation

### Step 1a: Build the inversion chart

**Goal**: Construct `inversionChart : OpenPartialHomeomorph (OnePoint ℂ) ℂ`.

**Source**: `{(0 : ℂ)}ᶜ` (as a subset of `OnePoint ℂ`, i.e., the set of
all points except `↑0`).
**Target**: `Set.univ` (all of `ℂ`).
**Forward map**: `∞ ↦ 0`, `↑z ↦ z⁻¹`.
**Inverse map**: `0 ↦ ∞`, `w ↦ ↑(w⁻¹)` for `w ≠ 0`.

Key lemmas needed:
- Continuity of `invChart` at `∞`: use `OnePoint.nhds_infty` filter
  characterization and the fact that `Inv.inv` sends complements of
  compact sets in `ℂ` to neighborhoods of `0`.
- Continuity of `invChart` at `↑z` for `z ≠ 0`: from
  `Continuous.continuousAt` applied to `OnePoint.isOpenEmbedding_coe`
  and `continuous_inv₀` (or `continuousAt_inv₀`).
- Openness of `source = {↑0}ᶜ`: from `T1Space` giving `{↑0}` closed.

**Dependencies**:
- `OnePoint.isOpenEmbedding_coe`
- `OnePoint.nhds_infty` / `OnePoint.hasBasis_nhds_infty`
- `continuousAt_inv₀` / `contDiffAt_inv`
- `T1Space (OnePoint ℂ)` (available)

**Estimated effort**: ~80–120 lines.

### Step 1b: Package into `ChartedSpace ℂ (OnePoint ℂ)`

**Goal**: `instance : ChartedSpace ℂ (OnePoint ℂ)`.

**Atlas**: `{identityChart, inversionChart}` where:
- `identityChart` is the open embedding chart from
  `OnePoint.isOpenEmbedding_coe`, with source `{∞}ᶜ` and target `Set.univ`.
- `inversionChart` is from Step 1a.

**`chartAt`**: for `x = ∞`, use `inversionChart`; for `x = ↑z`, use
`identityChart`.

**Coverage**: every point is in at least one chart source:
- `∞ ∈ inversionChart.source` (since `∞ ≠ ↑0`).
- `↑z ∈ identityChart.source` (since `↑z ≠ ∞`).

**Estimated effort**: ~30–50 lines (assuming Step 1a is done).

### Step 1c: Prove `IsManifold` for the complex structure

**Goal**: `instance : IsManifold 𝓘(ℂ, ℂ) ⊤ (OnePoint ℂ)`.

**Obligation**: show all chart transitions are in
`contDiffGroupoid ⊤ 𝓘(ℂ, ℂ)`.

There are four transition maps to check (atlas has 2 charts):
1. `id.symm.trans id` = identity on `ℂ` — trivially smooth.
2. `inv.symm.trans inv` = identity on `ℂ` — trivially smooth.
3. `id.symm.trans inv` = `z ↦ z⁻¹` on `ℂ \ {0}` — smooth by
   `contDiffAt_inv`.
4. `inv.symm.trans id` = `z ↦ z⁻¹` on `ℂ \ {0}` — smooth by
   `contDiffAt_inv`.

The key Mathlib lemma is:

```
contDiffAt_inv (𝕜 := ℂ) (hx : x ≠ 0) : ContDiffAt ℂ n Inv.inv x
```

which gives `ContDiffOn ℂ ⊤ Inv.inv (· ≠ 0)` and hence membership in
`contDiffGroupoid ⊤ 𝓘(ℂ, ℂ)`.

**Note on analyticity**: For `n = ω` (analytic), one would use
`AnalyticAt.inv` instead.  Getting `IsManifold 𝓘(ℂ, ℂ) ω` would be
slightly stronger and equally easy.

**Estimated effort**: ~40–60 lines.

### Non-obvious dependencies

1. **Filter API for `nhds ∞`**: The continuity of `invChart` at `∞`
   requires working with `OnePoint.nhds_infty`, which describes
   neighborhoods of `∞` as complements of compact subsets of `X`.
   One needs to show: for every compact `K ⊂ ℂ`, there exists `ε > 0`
   such that `z⁻¹ ∈ Metric.ball 0 ε` whenever `z ∉ K`.  This is a
   basic complex analysis fact but may not have a canned Mathlib lemma.

2. **`continuousAt_inv₀`**: The function `Inv.inv : ℂ → ℂ` is
   continuous at every `x ≠ 0`.  This should be available via
   `NormedField` or `NormedDivisionRing` instances.

3. **`OnePoint.rec` / `OnePoint.elim`**: Pattern matching on `OnePoint`
   (distinguishing `∞` from `↑z`) is done via `Option.rec` or
   `OnePoint.rec`.  Lean's equation compiler handles this, but
   continuity proofs need explicit filter arguments.

4. **`T1Space (OnePoint ℂ)`**: needed to show `{↑0}` is closed (hence
   its complement is open).  Available as an instance.

---

## 4. Connection to `Metric.sphere` homeomorphism

### 4.1 Existing homeomorphism

Mathlib provides (in `Topology/Compactification/OnePoint/Sphere.lean`):

```
onePointEquivSphereOfFinrankEq :
    (h : finrank ℝ V + 1 = Fintype.card ι) →
    OnePoint V ≃ₜ sphere (0 : EuclideanSpace ℝ ι) 1
```

For `V = ℂ` and `ι = Fin 3`, since `finrank ℝ ℂ = 2`, we get:

```
OnePoint ℂ ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1
```

This compiles and is verified.

### 4.2 What's NOT connected

There is **no** existing lemma transferring the *complex manifold*
structure from `OnePoint ℂ` to `S²` or vice versa.  The sphere
`S² = Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1` has:

- `ChartedSpace (EuclideanSpace ℝ (Fin 2)) S²` — a *real* 2-manifold
- `IsManifold (𝓡 2) ω S²` — *real* analytic manifold

But it does **not** have `ChartedSpace ℂ S²` or
`IsManifold 𝓘(ℂ, ℂ) n S²`.

### 4.3 What would be needed for the connection

To transport a complex structure from `OnePoint ℂ` to `S²` via the
homeomorphism, one would need:

1. **`OnePoint ℂ ≃ₜ S²`** — already exists (§4.1).
2. **`ChartedSpace ℂ (OnePoint ℂ)`** — to be built (§3, Step 1b).
3. **Transport of `ChartedSpace` along homeomorphisms** — Mathlib has
   `Homeomorph.chartedSpace` (or more precisely, one can use
   `OpenPartialHomeomorph` composition to push charts through the
   homeomorphism).  However, the resulting charts on `S²` would be
   `stereographic⁻¹ ∘ z⁻¹ ∘ stereographic`, which is not obviously
   useful.

Alternatively, one could:
- Define `ChartedSpace ℂ S²` directly using stereographic projection
  composed with the real-linear isomorphism
  `EuclideanSpace ℝ (Fin 2) ≃ₗ[ℝ] ℂ`.
- This would require showing the stereographic chart transitions are
  holomorphic (not just smooth), which involves relating the real
  stereographic formula to complex inversion.

**Recommendation**: For the genus-zero classification, work directly with
`OnePoint ℂ` as the complex manifold.  The homeomorphism to `S²` is
available for topological arguments, but the complex structure should
live natively on `OnePoint ℂ`.

---

## 5. Summary: what implementation packets this unlocks

### Packet A: `Jacobian/HolomorphicForms/OnePointCxChartedSpace.lean`
- Build `inversionChart : OpenPartialHomeomorph (OnePoint ℂ) ℂ`
- Build `instance : ChartedSpace ℂ (OnePoint ℂ)`
- Estimated effort: 100–150 lines
- Dependencies: only Mathlib (no project-internal deps)

### Packet B: `Jacobian/HolomorphicForms/OnePointCxIsManifold.lean`
- Build `instance : IsManifold 𝓘(ℂ, ℂ) ⊤ (OnePoint ℂ)`
- Key lemma: `ContDiffOn ℂ ⊤ Inv.inv {z : ℂ | z ≠ 0}`
- Estimated effort: 50–80 lines
- Dependencies: Packet A

### Packet C: `Jacobian/HolomorphicForms/OnePointCxHomeo.lean`
- State and (optionally) prove
  `OnePoint ℂ ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1`
  (one-liner from `onePointEquivSphereOfFinrankEq`)
- Add convenience API
- Estimated effort: 20–30 lines
- Dependencies: only Mathlib

### Packet D: Integration with genus-zero classification
- Use `ChartedSpace ℂ (OnePoint ℂ)` and `IsManifold` to make
  `OnePoint ℂ` a valid target for `CompactRiemannSurface`
- Show `analyticGenus (OnePoint ℂ) = 0` (no nonzero holomorphic
  1-forms on ℂℙ¹)
- This is the HARD direction of `analyticGenus_eq_zero_iff_homeomorphic_sphere`
- Dependencies: Packets A + B + cotangent bundle infrastructure

---

## 6. Alternative approaches considered

### 6.1 Transfer from `S²`'s real manifold structure

One could try to:
1. Use the existing `ChartedSpace (EuclideanSpace ℝ (Fin 2)) S²`
2. Replace the model with `ℂ` via the isomorphism `ℝ² ≅ ℂ`
3. Verify holomorphicity of transitions

This is more complex than the direct approach because:
- The stereographic chart formula involves real inner products
- Verifying that stereographic transitions are holomorphic (not just
  smooth) requires nontrivial algebraic manipulation
- The homeomorphism `OnePoint ℂ ≃ₜ S²` would need to be threaded through

### 6.2 Using `ℙ ℂ (ℂ × ℂ)` (projective line)

Mathlib has `OnePoint.equivProjectivization : OnePoint K ≃ ℙ K (K × K)`.
One could try to define the complex manifold structure on `ℙ ℂ (ℂ × ℂ)`
and transport.  However:
- `ℙ ℂ (ℂ × ℂ)` has no topology in Mathlib
- The equivalence is set-theoretic only
- Building topology + manifold structure on `ℙ ℂ (ℂ × ℂ)` is
  strictly harder than the direct `OnePoint ℂ` approach

**Verdict**: The direct two-chart atlas on `OnePoint ℂ` (§3) is the
simplest and most self-contained approach.
-/

namespace JacobianChallenge.HolomorphicForms.OnePointCxRecon

/-- Reconnaissance marker. This file intentionally contains no public
declarations beyond this token, which exists to make the module
non-empty for the build system. -/
def reconStub : Unit := ()

end JacobianChallenge.HolomorphicForms.OnePointCxRecon
