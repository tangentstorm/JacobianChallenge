# Plan: `lem:primitive-on-polygon`

Blueprint label: `lem:primitive-on-polygon`
Lean handle: `JacobianChallenge.Blueprint.primitive_on_polygon`
File: `Jacobian/Blueprint/Sec03/PrimitiveOnPolygon.lean`
Class: **DECOMPOSE**

## 1. Mathematical statement

On the open polygon `P° := interior of Polygon4g g` (a topological subspace
of `Polygon4g g`, equivalently the open unit disk in `ℂ` before
side-identification), every holomorphic 1-form `ω` admits a holomorphic
primitive `F : P° → ℂ` with `dF = ω`.

## 2. Choice of route

Two textbook proofs:

- **Path-integration / Poincaré-lemma route.** `P°` is simply connected, so
  the line integral `F(z) := ∫_{γ_z} ω` from a fixed basepoint along any path
  to `z` is well-defined (path-independence by simple connectedness +
  closedness `dω = 0`). `F` is `C^∞` with `dF = ω` by the standard
  Poincaré-lemma argument; holomorphicity follows because `ω` is of type
  `(1,0)`.

- **Direct power-series route.** Since `ω = h(z)\,dz` locally with `h` holomorphic,
  set `F(z) := ∫_0^z h(ζ)\,dζ` along the radial path. Cauchy's theorem on the
  disk gives path-independence (one-line), and `F` is then the antiderivative
  of `h` in the standard complex-analysis sense.

**This plan adopts the direct power-series route.** Reasons:

1. `P°` (the open unit disk) is convex, hence trivially simply connected.
   The simple-connectedness machinery is irrelevant — every closed 1-form on
   a convex open subset of `ℂ` has a primitive by direct radial integration.
2. Mathlib v4.28.0 has Cauchy's theorem on the disk and `HasDerivAt`-flavoured
   primitives for holomorphic functions. The general Poincaré lemma on
   simply-connected domains is more abstract and requires more glue.
3. The polygon-quotient lift is the only project-side step; everything below
   the lift is one-variable complex analysis on `ℂ`.

The Poincaré-lemma route remains valid and should be revisited once we need
primitives on non-convex (but still simply connected) regions; for `P°` it is
strictly heavier than necessary.

## 3. Mathlib v4.28.0 inventory (power-series route)

| prerequisite | status | path |
|---|---|---|
| Open unit disk `Metric.ball (0 : ℂ) 1` is convex | PRESENT | `Mathlib.Analysis.NormedSpace.Convex` (general balls in normed spaces) |
| Holomorphic primitive on a disk | PRESENT | `Mathlib.Analysis.Complex.Convex` / `DifferentiableOn.exists_primitive_on_convex` (effective lemma name varies) |
| `HasDerivAt` ⇔ Cauchy-Riemann equations | PRESENT | `Mathlib.Analysis.Complex.RealDeriv` |
| Cauchy's integral theorem on disk | PRESENT | `Mathlib.Analysis.Complex.Cauchy*` |
| `Polygon4g` interior as a subspace of `ℂ` | PRESENT (this project) | `Jacobian/Periods/Polygon4g.lean` (`Polygon4g.mk` is a quotient of `DiskC`) |
| `HolomorphicOneForm` → chart-local coefficient `h(z)` | PRESENT (this project) | `Jacobian/HolomorphicForms/*` (`holomorphicOneForm_coeff` and friends) |

## 4. Decomposition (4 sub-leaves)

Each leaf gets a stable Lean handle in `Jacobian/Periods/PrimitiveOnPolygon.lean`
(new file). Sub-leaf 4 is the umbrella; leaves 1–3 are the inputs.

| # | Lean handle | Class | Sketch | Deps |
|---|---|---|---|---|
| 1 | `Polygon4g.diskInteriorEquiv` | SHORT | The quotient map `Polygon4g.mk g` restricts to a homeomorphism between the open unit disk `Metric.ball (0 : ℂ) 1` (interior of `DiskC`) and an open subset `P°` of `Polygon4g g` (the side-pairing relation `SideRel g` only equates boundary points, so the quotient is injective on the interior). | `Polygon4g.SideRel`, `Quotient.injective_iff` |
| 2 | `holomorphicOneForm_diskCoeff` | SHORT | For a holomorphic 1-form `ω` on `Polygon4g g`, lifted along `Polygon4g.diskInteriorEquiv.symm`, the chart-local coefficient `h : Metric.ball (0:ℂ) 1 → ℂ` is holomorphic on the open disk. Pure unfolding of the `HolomorphicOneForm` definition. | `HolomorphicOneForm`, leaf 1 |
| 3 | `disk_holomorphic_has_primitive` | MEDIUM | Every holomorphic function `h : Metric.ball (0:ℂ) 1 → ℂ` admits a holomorphic primitive `F` with `F'(z) = h(z)` on the open disk. Mathlib lemma (Cauchy + radial-path integration) — at most a project wrapper. | Mathlib's complex analysis on disks |
| 4 | `primitive_on_polygon` (umbrella) | SHORT | Combine 1–3: lift `ω` to a holomorphic 1-form on the disk's interior, extract its coefficient via leaf 2, primitivise via leaf 3, push the primitive forward along leaf 1's homeomorphism. Output: `F : P° → ℂ` holomorphic with `dF = ω`. | leaves 1, 2, 3 |

## 5. Assembly order

1. Leaf 1 (interior-of-quotient is homeomorphic to the open disk).
2. Leaf 2 (lift of `ω` extracts a holomorphic disk-coefficient `h`).
3. Leaf 3 (Mathlib primitive on the disk).
4. Leaf 4 (assemble).

## 6. Poincaré-lemma route — recorded for completeness

For non-convex simply-connected regions one would use:

P1. Path-integral function `F(z) := ∫_{γ_z} ω` from a fixed basepoint.
P2. Path-independence: `∫_{γ₁ - γ₂} ω = 0` whenever `γ₁ - γ₂` is a
    boundary in `H_1`. Equivalent to `dω = 0` on a simply-connected
    domain.
P3. `dF = ω` and holomorphicity: same chart-local Cauchy-Riemann argument.

Not needed here because `P° = Metric.ball 0 1` is convex.

## 7. LOC estimate

- Leaf 1: ~50 LOC (`SideRel`-injectivity on the open disk + `Quotient` API
  for the homeomorphism).
- Leaf 2: ~40 LOC (`HolomorphicOneForm` → chart coefficient unfold).
- Leaf 3: ~80 LOC (Mathlib wrapper).
- Leaf 4: ~30 LOC (assembly).

Total ≈ 200 LOC.

## 8. What is genuinely blocked

Nothing on this route. Every leaf reduces to either project-local
infrastructure (`Polygon4g`, `HolomorphicOneForm`) or pinned Mathlib
v4.28.0 (complex analysis on disks). Each leaf is independently
Aristotle-attackable.

## 9. Aristotle packet plan (per leaf)

| Leaf | File | Risk | Notes |
|------|------|------|-------|
| 1 | `Jacobian/Periods/PrimitiveOnPolygon.lean` | low | Quotient injectivity proof; pure topology over a ready `SideRel`. |
| 2 | same file | low | Definitional unfold + holomorphicity propagation. |
| 3 | same file | low–medium | Risk is just finding the right Mathlib lemma name; structurally trivial. |
| 4 | same file | low | One-line composition. |

All four can be submitted as separate Aristotle packets in parallel — no
inter-leaf serial dependency once the file scaffold (with all four named
sorries) lands.
