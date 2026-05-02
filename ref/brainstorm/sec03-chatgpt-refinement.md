# sec03 chain — ChatGPT refinement (cross-validation of Grok sketch)

Source: ChatGPT JC project chat 69f4bed4-d1f8-83ea-a0ce-1b2b3c650993
Received: 2026-05-01

## Verdict (vs. Grok)

Grok's priority is **wrong**. `hermitian-positivity` is NOT immediate
— it requires a global integration of `i ω ∧ ω̄` over X, which Mathlib
v4.28.0 does not expose for compact Riemann surfaces. Don't open with
`polygonal_homeo` or `stokes_on_half_plane`; open with an **abstract
algebra API** + opaque global identities, and the linear algebra falls
out for free.

**Highest-leverage opaque input:** `riemann_bilinear_identity`. Plus
one small `hermitian_positive_definite` axiom. With those two, nodes
4, 5, 6, 7 all become small.

## Refined opaque-input shapes

### `polygonal_homeo` — DON'T USE YET
`X ≃ₜ Polygon g` and `Nonempty (X ≃ₜ Polygon g)` are too thin and force
"transport hell." If we ever need it, prefer a structure carrying the
homeomorphism + the induced symplectic basis. **For this week, skip it
entirely** — downstream only needs the resulting symplectic basis.

Better immediate shape: `opaque exists_symplectic_basis (X) (g) :
Nonempty (SymplecticBasis (H1Z X) g)`.

### `stokes_on_half_plane` — DON'T USE YET
Realistic polymorphic statement requires `HasPiecewiseSmoothBoundary`,
`integral_boundary`, manifold form integration — too many project
abstractions. Skip.

### Use this instead — `stokes_cut_polygon_identity`

```lean
opaque stokes_cut_polygon_identity
    {X : Type u}
    [TopologicalSpace X] [CompactSpace X] [T2Space X]
    [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    {g : ℕ}
    (S : SymplecticBasis (H1Z X) g)
    (ω η : HolomorphicOneForm X) :
    wedgeIntegral X ω η =
      ∑ i : Fin g,
        (period X (S.a i) ω * period X (S.b i) η
        - period X (S.b i) ω * period X (S.a i) η)
```

This bypasses Stokes entirely as the right "opaque Stokes" boundary.

## Recommended order

1. Define abstract sec03 algebra API (`H1Z`, `HolomorphicOneForm`, `period`, `wedgeIntegral`, `hermitianPairing`, `SymplecticBasis`).
2. Opaque global bilinear identity (replaces polygonal model + Stokes + primitive-on-polygon + telescoping in one stroke).
3. Opaque Hermitian positivity (replaces global integration of `i ω ∧ ω̄`).
4. Pure linear algebra — full real rank / injectivity of period map from RBI + positivity.
5. Umbrella theorem `riemann_bilinear_relations`.
6. **Later:** polygonal model, Stokes on surfaces with boundary, primitive-on-polygon, derivation of bilinear identity.

## What ships TODAY without new opaque inputs

| Node                                 | Today? | Notes                                |
|--------------------------------------|--------|--------------------------------------|
| polygonal-model                      | no     | classification/cutting/intersection  |
| stokes-on-rs-with-boundary           | no     | manifold integration                 |
| primitive-on-polygon                 | no     | Poincaré + holomorphic primitive     |
| bilinear-from-stokes                 | no     | needs polygon + Stokes               |
| hermitian-positivity                 | no     | global 2-form integration            |
| period-vectors-full-real-rank        | **yes (conditional)** | pure linear algebra given RBI + positivity as hypotheses |
| riemann-bilinear umbrella            | **yes** | trivial wrapper around the others   |

Plus shippable today: `SymplecticBasis` structure, `period_vector` def, `wedgeIntegral` / `hermitianPairing` abstract API, theorem wrappers around opaque identities, finite-rank/injectivity lemmas.

## Three Aristotle packets

### Packet 1 — Abstract sec03 API (`Sec03API.lean`)

File: `Jacobian/Periods/Sec03API.lean`

Imports:
```lean
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Topology.Manifold
import Jacobian.Periods.Basic
```

Declarations:
```lean
namespace JacobianChallenge.Periods
open scoped BigOperators
universe u
variable (X : Type u)
variable [TopologicalSpace X] [CompactSpace X] [T2Space X]
variable [ChartedSpace ℂ X]
variable [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]

structure SymplecticBasis (g : ℕ) where
  a : Fin g → H1Z X
  b : Fin g → H1Z X
  basis_complete : Prop := True
  intersection_standard : Prop := True

opaque wedgeIntegral : HolomorphicOneForm X → HolomorphicOneForm X → ℂ
opaque hermitianPairing : HolomorphicOneForm X → HolomorphicOneForm X → ℂ
opaque period : H1Z X → HolomorphicOneForm X → ℂ

def periodVector {g : ℕ} (S : SymplecticBasis X g) (ω : HolomorphicOneForm X) :
    (Fin g × Bool) → ℂ :=
  fun j =>
    match j with
    | (i, false) => period X (S.a i) ω
    | (i, true)  => period X (S.b i) ω

end JacobianChallenge.Periods
```

LOC: 40–70. Definitions only — no proofs to discharge.

### Packet 2 — Riemann bilinear identity (`RiemannBilinearIdentity.lean`)

File: `Jacobian/Periods/RiemannBilinearIdentity.lean`

```lean
namespace JacobianChallenge.Periods
open scoped BigOperators
universe u
variable (X : Type u)
variable [TopologicalSpace X] [CompactSpace X] [T2Space X]
variable [ChartedSpace ℂ X]
variable [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]

opaque riemann_bilinear_identity
    {g : ℕ} (S : SymplecticBasis X g) (ω η : HolomorphicOneForm X) :
    wedgeIntegral X ω η =
      ∑ i : Fin g,
        (period X (S.a i) ω * period X (S.b i) η
        - period X (S.b i) ω * period X (S.a i) η)

theorem bilinear_from_stokes
    {g : ℕ} (S : SymplecticBasis X g) (ω η : HolomorphicOneForm X) :
    wedgeIntegral X ω η =
      ∑ i : Fin g,
        (period X (S.a i) ω * period X (S.b i) η
        - period X (S.b i) ω * period X (S.a i) η) := by
  exact riemann_bilinear_identity X S ω η

end JacobianChallenge.Periods
```

LOC: 30–50. One opaque + a one-line wrapper.

### Packet 3 — Conditional zero-of-vanishing-periods (`PeriodRank.lean`)

File: `Jacobian/Periods/PeriodRank.lean`

```lean
namespace JacobianChallenge.Periods
universe u
variable (X : Type u)
variable [TopologicalSpace X] [CompactSpace X] [T2Space X]
variable [ChartedSpace ℂ X]
variable [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]

opaque hermitian_positive_definite :
    ∀ ω : HolomorphicOneForm X,
      ω ≠ 0 → 0 < Complex.re (hermitianPairing X ω ω)

opaque hermitian_eq_zero_of_zero_periods
    {g : ℕ} (S : SymplecticBasis X g) (ω : HolomorphicOneForm X)
    (hper : ∀ i : Fin g, period X (S.a i) ω = 0 ∧ period X (S.b i) ω = 0) :
    hermitianPairing X ω ω = 0

theorem zero_of_all_periods_zero
    {g : ℕ} (S : SymplecticBasis X g) (ω : HolomorphicOneForm X)
    (hper : ∀ i : Fin g, period X (S.a i) ω = 0 ∧ period X (S.b i) ω = 0) :
    ω = 0 := by
  by_contra hω
  have hpos := hermitian_positive_definite X ω hω
  have hzero := hermitian_eq_zero_of_zero_periods X S ω hper
  rw [hzero] at hpos
  norm_num at hpos

end JacobianChallenge.Periods
```

LOC: 40–80.

## Final dispatch ranking

1. `Sec03API.lean` (no opaque deps)
2. `RiemannBilinearIdentity.lean` (depends on 1)
3. `PeriodRank.lean` (depends on 1 + 2)
4. Umbrella `RiemannBilinearPackage.lean` later
5. **Much later:** replace `hermitian_eq_zero_of_zero_periods`, `riemann_bilinear_identity`, then polygonal model + Stokes + primitive-on-polygon.
