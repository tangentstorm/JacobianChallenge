import Mathlib

/-!
# Construction Recon: Banach-space data on holomorphic 1-forms

This file is a construction-recon document for the obligation

```lean
theorem holomorphicOneForm_normedSpace_uniformOnCompact (X : Type) [...] :
    Nonempty (HolomorphicOneFormBanachData X) := sorry
```

from `Jacobian/HolomorphicForms/CompactRiemannSurface.lean` (step (a)
of the Riesz finite-dimensionality route). It surveys Mathlib v4.28.0
for the tools needed to equip `ContMDiffSection (cotangentBundle ...) ω`
with a complete normed-space structure, identifies what's missing, and
lays out a concrete multi-step construction plan.

**Companion recon**: the earlier `SectionTopologyRecon.lean` (packet
`b782c387`) is a *general* stub asking "what topology should
`ContMDiffSection` carry?" This file is a *concrete construction* recon:
it pins down the specific Banach-space data for holomorphic 1-forms on a
**compact** base, using the sup-norm.

**Pinned versions**: Lean 4.28.0; Mathlib commit
`8f9d9cff6bd728b17a24e163c9402775d9e6a365`.

---

## 1. Background: the data structure to fill

`HolomorphicOneFormBanachData X` (defined in
`CompactRiemannSurface.lean`, lines ~65–90) carries five fields atop
the *existing* `ContMDiffSection`-derived `AddCommGroup` /
`Module ℂ`:

| Field | Type | Purpose |
|---|---|---|
| `toNorm` | `Norm (HolomorphicOneForm ℂ X)` | The norm function |
| `toMetricSpace` | `MetricSpace (HolomorphicOneForm ℂ X)` | Metric topology |
| `dist_eq` | `∀ x y, dist x y = ‖x - y‖` | Norm-induced metric |
| `norm_smul_le` | `∀ c x, ‖c • x‖ ≤ ‖c‖ * ‖x‖` | Scalar bound |
| `complete` | `CompleteSpace (HolomorphicOneForm ℂ X)` | Banach |

The design ensures no typeclass diamond: `toNormedAddCommGroup.toAddCommGroup`
and `toNormedSpace.toModule` are *definitionally* the existing
`ContMDiffSection.instAddCommGroup` / `ContMDiffSection.instModule`.

---

## 2. Specialisation: `HolomorphicOneForm ℂ X` fibers

For a Riemann surface (`E = ℂ`), the abbreviations from
`CotangentBundle.lean` and `Defs.lean` give:

```text
HolomorphicOneForm ℂ X
  = ContMDiffSection 𝓘(ℂ, ℂ) (ℂ →L[ℂ] ℂ) ⊤ (CotangentSpace ℂ X)
```

Each fiber `CotangentSpace ℂ X x = TangentSpace 𝓘(ℂ, ℂ) x →L[ℂ] ℂ`
is a `NormedAddCommGroup` via the operator norm. Since `ℂ →L[ℂ] ℂ`
is 1-dimensional (`≃ₗᵢ[ℂ] ℂ` via evaluation at `1`), the fiber norm
reduces to an absolute value. This simplification is useful but not
essential — the construction works for any normed model fiber `F`.

---

## 3. What Mathlib v4.28.0 has

### 3.1 Continuous-function Banach spaces (compact domain)

| Declaration | Module | Notes |
|---|---|---|
| `ContinuousMap.instNorm` | `Topology.ContinuousMap.Compact` | `Norm C(α, E)` for `[CompactSpace α] [SeminormedAddCommGroup E]` |
| `ContinuousMap.norm_eq_iSup_norm` | same | `‖f‖ = ⨆ x, ‖f x‖` |
| `ContinuousMap.instNormedAddCommGroup` | same | Full `NormedAddCommGroup C(α, E)` for compact `α` |
| `ContinuousMap.instMetricSpace` | same | `MetricSpace C(α, β)` for compact `α`, `MetricSpace β` |
| `ContinuousMap.equivBoundedOfCompact` | same | `C(α, β) ≃ BoundedContinuousFunction α β` for compact `α` |
| `BoundedContinuousFunction.instNormedAddCommGroup` | `Topology.ContinuousMap.Bounded.Basic` | `NormedAddCommGroup (α →ᵇ E)` |
| `BoundedContinuousFunction.instNormedSpace` | same | `NormedSpace 𝕜 (α →ᵇ E)` |
| `BoundedContinuousFunction.instCompleteSpace` | same | `CompleteSpace (α →ᵇ E)` for `CompleteSpace E` |

**Key point**: `C(α, E)` for compact `α` and normed `E` is a
Banach space with `‖f‖ = ⨆ x, ‖f x‖`.

### 3.2 `ContMDiffSection` algebraic instances

| Declaration | Module | Notes |
|---|---|---|
| `ContMDiffSection.instAddCommGroup` | `Geometry.Manifold.VectorBundle.SmoothSection` | Pointwise addition |
| `ContMDiffSection.instModule` | same | Pointwise scalar multiplication |
| `ContMDiffSection.instZero` | same | Zero section |
| `ContMDiffSection.instNeg` | same | Pointwise negation |

**No topology, norm, or metric** on `ContMDiffSection` exists.

### 3.3 Smooth section → continuous total-space map

| Declaration | Notes |
|---|---|
| `ContMDiffSection.contMDiff_toFun` | `ContMDiff I (I.prod 𝓘(𝕜, F)) n (fun x => ⟨x, σ x⟩)` |
| `ContMDiff.continuous` | Every `ContMDiff` map is continuous |

The total-space map `x ↦ Bundle.TotalSpace.mk' F x (σ x)` is
continuous, but this is a map into the *total space*, not `M → F`.

### 3.4 Trivialization API

| Declaration | Notes |
|---|---|
| `Trivialization F (π F V)` | Local trivialization of a fiber bundle |
| `FiberBundle.isLocalTriv` | Every point has a trivialization |
| `Trivialization.continuousOn` / `.continuousOn_symm` | Continuity |
| `Trivialization.apply_mk_proj` | `e ⟨x, v⟩ = (x, e.linearEquivAt x v)` |

In a trivialization `e`, the section `σ` becomes a continuous map
`x ↦ e.linearEquivAt x (σ x) : F` (non-dependent).

### 3.5 Cauchy integral / complex analysis

| Declaration | Status | Module |
|---|---|---|
| `Complex.hasFPowerSeriesOnBall` | ✅ | `Analysis.Complex.CauchyIntegral` |
| `DiffContOnCl.circleIntegral_eq` | ✅ | same |
| `DifferentiableOn.hasFPowerSeriesOnBall` | ✅ | same |
| Weierstrass uniform limit theorem | ❌ NOT in Mathlib | — |

---

## 4. What's missing / needs to be built

### 4.1 Fiberwise norm function — **MISSING**

No `x ↦ ‖σ x‖` function is bundled for smooth sections. Define:

```lean
noncomputable def ContMDiffSection.fiberNorm
    (σ : ContMDiffSection I F n V) (x : M) : ℝ := ‖σ.toFun x‖
```

This typechecks because each fiber `V x` has a `NormedAddCommGroup`.

### 4.2 Continuity of `x ↦ ‖σ x‖` — **NEEDS PROOF**

The key technical lemma. For the `E = ℂ` specialisation:
- The fiber `ℂ →L[ℂ] ℂ ≅ ℂ` via `f ↦ f 1`.
- Under this identification, `‖σ x‖_op = |(σ x) 1|`.
- The map `x ↦ (σ x) 1` is continuous (smooth section composed with
  a continuous linear map), so `x ↦ ‖σ x‖` is continuous.

For general fibers, the argument goes through total-space continuity
and the fact that `VectorBundle` gives continuous dependence of the
trivialization on the base point.

### 4.3 Sup-norm finiteness — **NEEDS PROOF**

For compact `X` and continuous `x ↦ ‖σ x‖`, the sup is finite.
Key Mathlib lemmas: `IsCompact.exists_isMaxOn`,
`CompactSpace.isCompact_univ`, `Continuous.bddAbove_range`.

### 4.4 Completeness — **NEEDS PROOF** (hardest step)

A Cauchy sequence `(σₙ)` in the sup-norm converges pointwise (each
fiber is complete). The limit `σ∞ x := lim σₙ x` must be shown:
1. **Continuous**: by `TendstoUniformly.continuous` (uniform limit
   of continuous functions).
2. **Smooth**: requires Weierstrass's theorem — uniform limit of
   holomorphic functions is holomorphic. **NOT in Mathlib**.

**Strategy for Weierstrass**: provable from Mathlib's Cauchy integral
formula:
1. The limit `f` satisfies the Cauchy integral formula (pass limit
   through the integral via dominated convergence).
2. A continuous function satisfying the Cauchy integral formula is
   holomorphic (power series representation from
   `DiffContOnCl.circleIntegral_eq`).
Estimated: ~50–80 lines of new Lean.

**Alternative**: work with `BoundedContinuousFunction` completeness
(`BoundedContinuousFunction.instCompleteSpace`) and prove the space
of holomorphic sections is *closed* in `C(X, F)`. Closedness follows
from the same Weierstrass argument.

### 4.5 Summary of gaps

| Gap | Difficulty | Est. lines |
|---|---|---|
| Fiberwise norm function | Easy | 5 |
| Continuity of `x ↦ ‖σ x‖` | Medium | 20–40 |
| Sup-norm is a norm | Medium | 30–50 |
| Completeness (Weierstrass) | Hard | 60–100 |
| Weierstrass: uniform limit of holo = holo | Hard | 50–80 |

---

## 5. Multi-step plan for implementation

### Step 1: Fiberwise norm and continuity (30–50 lines)

Define `ContMDiffSection.fiberNorm` and prove
`ContMDiffSection.continuous_fiberNorm`. For `E = ℂ`, use the
fiber identification `ℂ →L[ℂ] ℂ ≅ ℂ` to reduce to continuity of
`x ↦ |(σ x) 1|`.

### Step 2: Sup-norm properties (40–60 lines)

Define and verify:
```lean
noncomputable def ContMDiffSection.supNorm
    [CompactSpace M] (σ : ContMDiffSection I F n V) : ℝ :=
  ⨆ x : M, ‖σ.toFun x‖
```

Key properties:
- `norm_zero : ‖(0 : …)‖ = 0` — `⨆ x, ‖0 x‖ = 0`
- `norm_eq_zero_iff : ‖σ‖ = 0 ↔ σ = 0` — uses `Nonempty M`
- `norm_add_le : ‖σ + τ‖ ≤ ‖σ‖ + ‖τ‖` — `ciSup` manipulation
- `norm_smul : ‖c • σ‖ ≤ ‖c‖ * ‖σ‖`
- `norm_neg : ‖-σ‖ = ‖σ‖`

All routine using `ciSup_le`, `le_ciSup`, `ciSup_le_ciSup`.

### Step 3: MetricSpace construction (20–30 lines)

Define `dist σ τ := ‖σ - τ‖` and verify the `MetricSpace` axioms.
Crucially, construct the `MetricSpace` *without* going through
`NormedAddCommGroup.mk` (to avoid the diamond). Instead, build the
fields of `HolomorphicOneFormBanachData` directly.

### Step 4: Completeness (80–150 lines)

**Recommended approach for `E = ℂ`**: embed `HolomorphicOneForm ℂ X`
into `C(X, ℂ)` (via the fiber identification `ℂ →L[ℂ] ℂ ≅ ℂ`)
and show the image is closed. Then completeness follows from
`BoundedContinuousFunction.instCompleteSpace` + closedness.

Closedness requires the Weierstrass theorem: build from Mathlib's
`DiffContOnCl.circleIntegral_eq` (Cauchy integral formula) +
dominated convergence.

### Step 5: Assembly (10–15 lines)

```lean
noncomputable def holomorphicOneFormBanachData_of_compact
    (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ, ℂ) ⊤ X] :
    HolomorphicOneFormBanachData X where
  toNorm := ⟨fun σ => ⨆ x : X, ‖σ.toFun x‖⟩
  toMetricSpace := ‹Step 3›
  dist_eq := ‹Step 3›
  norm_smul_le := ‹Step 2›
  complete := ‹Step 4›
```

---

## 6. Connection to existing infrastructure

### 6.1 `HolomorphicOneFormBanachData` (CompactRiemannSurface.lean)

Designed for this construction. Fields mirror the five normed-space
properties, deliberately avoiding `NormedAddCommGroup` packaging.

### 6.2 `ContMDiffSection` (Mathlib)

Provides `AddCommGroup` and `Module ℂ`. The sup-norm respects
pointwise operations: `‖σ + τ‖ := ⨆ x, ‖σ x + τ x‖`.

### 6.3 `CotangentBundle` / `CotangentSpace` (project-local)

Defined in `CotangentBundle.lean` via `Bundle.ContinuousLinearMap`.
`VectorBundle` instance is automatic. Fiber norm (operator norm on
`E →L[ℂ] ℂ`) is automatic from Mathlib.

### 6.4 Downstream consumers

| Consumer | Uses |
|---|---|
| `holomorphicOneForm_montel` (step b) | Metric for closedBall compactness |
| `holomorphicOneForm_locallyCompact_of_compactRiemannSurface` (step c) | Local compactness from (b) |
| `compactRiemannSurface_finiteDimensionalHolomorphicOneForms` | Riesz via `FiniteDimensional.of_locallyCompactSpace` |

---

## 7. `E = ℂ` simplification (recommended first target)

For Riemann surfaces the construction simplifies significantly:

1. **Fiber identification**: `ℂ →L[ℂ] ℂ ≅ ℂ` via `f ↦ f 1`, so
   sections ≈ functions `X → ℂ`, norm = absolute value.
2. **Embed into `C(X, ℂ)`**: the Banach structure on `C(X, ℂ)` is
   already in Mathlib (compact `X`, complete `ℂ`).
3. **Pull back**: define `‖σ‖ := ‖embed σ‖_C(X,ℂ)`.
4. **Closedness**: uniform limit of holomorphic = holomorphic
   (Weierstrass, from Cauchy integral formula).
5. **Assembly**: package into `HolomorphicOneFormBanachData`.

Estimated total: **140–215 lines** (vs 180–305 for general fibers).

---

## 8. Estimated effort summary

| Step | Description | Lines | Difficulty | Blocks on |
|---|---|---|---|---|
| 1 | Fiberwise norm + continuity | 30–50 | Medium | — |
| 2 | Sup-norm properties | 40–60 | Medium | Step 1 |
| 3 | MetricSpace construction | 20–30 | Easy | Step 2 |
| 4 | Completeness (Weierstrass) | 80–150 | Hard | Steps 1–3 |
| 5 | Assembly | 10–15 | Easy | Steps 1–4 |
| **Total** | | **180–305** | | |

---

## 9. Risk assessment

| Risk | Likelihood | Mitigation |
|---|---|---|
| Weierstrass theorem too hard | Medium | Use Cauchy integral formula (in Mathlib) + dominated convergence |
| Diamond in `AddCommGroup`/`Module` | Low | `HolomorphicOneFormBanachData` design handles this |
| Dependent-type friction in `ContMDiffSection.toFun` | Medium | Work with `E = ℂ` specialisation |
| Missing `Nonempty X` | Low | `CompactSpace + ConnectedSpace` gives `Nonempty` |

---

## 10. Key Mathlib lemmas for the implementation

```text
-- Sup-norm on continuous maps (compact domain)
ContinuousMap.norm_eq_iSup_norm  : ‖f‖ = ⨆ x, ‖f x‖
ContinuousMap.instNormedAddCommGroup : NormedAddCommGroup C(α, E)
ContinuousMap.instMetricSpace    : MetricSpace C(α, β)

-- Bounded continuous functions (Banach completion)
BoundedContinuousFunction.instCompleteSpace : CompleteSpace (α →ᵇ E)
ContinuousMap.equivBoundedOfCompact : C(α, β) ≃ α →ᵇ β

-- iSup manipulation
ciSup_le           : (∀ i, f i ≤ a) → ⨆ i, f i ≤ a
le_ciSup           : BddAbove (range f) → f i ≤ ⨆ i, f i
ciSup_le_ciSup     : BddAbove (range g) → (∀ i, f i ≤ g i) → ⨆ f ≤ ⨆ g

-- Compactness / continuity
IsCompact.exists_isMaxOn         : compact + continuous → attains max
CompactSpace.isCompact_univ      : IsCompact (univ : Set X)

-- Smooth section structure
ContMDiffSection.instAddCommGroup : AddCommGroup
ContMDiffSection.instModule       : Module 𝕜
ContMDiffSection.contMDiff_toFun  : section is smooth

-- Finite-dimensionality (downstream)
FiniteDimensional.of_locallyCompactSpace : locally compact normed → fin-dim

-- Cauchy integral (for Weierstrass)
Complex.hasFPowerSeriesOnBall     : holomorphic → power series
DiffContOnCl.circleIntegral_eq    : Cauchy integral formula
```
-/

namespace JacobianChallenge.HolomorphicForms.SectionTopologyConstructionRecon

/-- Reconnaissance marker. This file is a construction-recon document
and intentionally contains no production declarations beyond this
token, which exists to make the module non-empty for the build system. -/
def reconStub : Unit := ()

end JacobianChallenge.HolomorphicForms.SectionTopologyConstructionRecon
