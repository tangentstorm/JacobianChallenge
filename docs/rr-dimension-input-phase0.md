# Phase 0: pricing the Path B dimension-input kernel (`dim L([P]) = 2` from genus zero)

> Companion to jc1's Phase 0.5 (`docs/montel-phase05-stage-construction.md`).
> Tracking #232 Path B. Prose-only pricing: what does an honest proof of the
> dimension input actually require, and is it cheaper, comparable, or more
> expensive than the Perron/Koebe engine Path A needs?

## Executive Conclusion

The Path B kernel is the single open provider

```lean
genusZero_pointRiemannRochGermSpaceDimensionInput   -- RiemannRoch.lean:574, sorry at :582
```

whose load-bearing field is

```lean
point_finrank_eq_two :
  Module.finrank ℂ (RiemannRochGermSpace X (Divisor.point P)) = 2
```

under `analyticGenus ℂ X = 0`.

The honest verdict: **the lower bound `≥ 2` is cheap; the upper bound `≤ 2` is
engine-scale.** The substrate already supplies, green, everything the lower
bound needs *except one nonconstant section in `L([P])`* — and the only
non-circular source of that section is itself a genus-zero existence theorem of
the same analytic depth as the Path A engine. The upper bound `≤ 2` is strictly
worse: it is the Riemann–Roch / `H¹`-vanishing direction, and **this repository
contains no proven Riemann–Roch theorem, no `H¹(X, 𝒪)`-vanishing theorem, and no
Serre-duality bridge** — only definitional sheaf-cohomology and Hodge
scaffolding with no analytic comparison theorem. Both bounds bottom out in a
classical analytic input (existence of a degree-1 meromorphic function on a
genus-0 surface, equivalently `H¹(X,𝒪)=0`) that is **not** in the substrate and
is of the **same Perron/Koebe/Riemann-existence scale** as the Path A engine.

**Path B is not the cheaper escape.** It relocates the same hard analytic
content from "construct a global uniformizing sequence" to "prove the
genus-zero Riemann–Roch dimension count," but the irreducible input — a
nonconstant meromorphic function with a single simple pole, which *is* the
sphere uniformizer up to packaging — is the same theorem wearing a different
hat. Picking Path B over Path A on cost grounds would be shading the estimate;
the comparison below is laid out so the manager can confirm this directly.

## Target Payload

The provider returns a `GenusZeroPointRiemannRochGermSpaceDimensionInput X P h`
(`RiemannRoch.lean:555`, a `Prop`-valued structure) with two fields:

```lean
point_finrank_eq_two :
  Module.finrank ℂ (RiemannRochGermSpace X (Divisor.point P)) = 2
residual_dim_zero : ∃ ℓKP : ℕ, ℓKP = 0
```

- `point_finrank_eq_two` is the entire analytic content priced here.
- `residual_dim_zero` is a **placeholder shape** (`∃ ℓKP, ℓKP = 0` is trivially
  `⟨0, rfl⟩`); it stands in for a future `ℓ(K−[P]) = 0` once a `K−[P]`
  germ-space carrier exists. It carries no analytic obligation in the current
  statement and is not priced.

Downstream, everything is green **conditional on this provider**:

- `genusZero_riemannRoch_difference_eq_two_of_germSpaceDimensionInput`
  (`RiemannRoch.lean:584`, GREEN-from-input) — reads off `ℓP − ℓKP = 2`.
- `genusZero_pointRiemannRochGermSpace_exists_outside_constants`
  (`RiemannRoch.lean:602`, GREEN-from-input) — produces an `F` outside the
  constant line. **Note the direction:** this *consumes*
  `point_finrank_eq_two`, so it cannot help prove it.
- `genusZero_pointRiemannRochElement_of_germSpaceDimensionInput`
  (`RiemannRoch.lean:667`, GREEN modulo a *separate* open sorry at :661, the
  germ-to-map bridge jc0 owns).

So the dimension input is the root analytic sorry of the entire Path B spine.

## 1. Substrate survey (green vs open)

### Green algebra — the module-theoretic frame is complete

- **`RiemannRochGermSpace X D`** (`RiemannRoch.lean:307`, GREEN def):
  ```lean
  Submodule.span ℂ
    (Set.range fun s : RiemannRochBoundedSection X D =>
      s.toMeromorphicFunctionWithDivisors.germs)
  ```
  a `Submodule ℂ (MeromorphicGermFamily X)`. `finrank` is taken in this module.
  The carrier is *germ families*, not concrete functions — the dimension is the
  ℂ-dimension of the span of bounded-section germs.

- **`RiemannRochBoundedSection X D`** (`RiemannRoch.lean:50`, GREEN structure):
  fields `toMeromorphicFunctionWithDivisors : MeromorphicFunctionWithDivisors X`
  and `memRiemannRochSpace : …MemRiemannRochSpace D`, where
  `MemRiemannRochSpace f D := Divisor.Effective (f.principal + D)`
  (`MeromorphicFunctionVector.lean:576`) — the classical `(f) + D ≥ 0`. Helper
  `constantNonzero` (`RiemannRoch.lean:103`) gives the nonzero constants as
  elements of `L(D)` for effective `D`.

- **Constant line, finrank 1 (GREEN):**
  - `constantGermFamilyLine` (`RiemannRoch.lean:352`) `= LinearMap.range
    (constantGermFamilyLinearMap X)`;
  - `constantGermFamilyLine_finrank` (`:381`) `= 1` (for `Nonempty X`);
  - `constantGermFamilyLine_le_RiemannRochGermSpace` (`:433`) for effective `D`;
  - `constantGermFamilyLineInRiemannRoch_finrank` (`:519`) `= 1` — the constant
    line as a finrank-1 *submodule of the germ space itself*.

- **Span extraction (jc3, GREEN):**
  `RiemannRochGermSpace.exists_finset_sum_generators` and `…'`
  (`RRNonconstantPoleDivisor.lean:847, 872`) expose any `F` as a finite ℂ-linear
  combination of bounded-section germ generators (the `'` form with nonzero
  coefficients, re-enumerated). **What this does NOT give:** any *bound* on the
  dimension. It is a representation tool (used by jc0's germ-to-map bridge), not
  a dimension argument. It says nothing about how many independent generators
  exist.

### What genus zero actually buys (and what it does not)

- **`analyticGenus ℂ X := Module.finrank ℂ (HolomorphicOneForm ℂ X)`**
  (`FiniteDimensional.lean:27`, GREEN), where `HolomorphicOneForm ℂ X` is the
  ℂ-module of `C^∞` (analytic) sections of the cotangent bundle (`Defs.lean:23`).
- `analyticGenus ℂ X = 0` is characterized, GREEN, by:
  - `analyticGenus_eq_zero_iff_finrank_zero` (`AnalyticGenus.lean:28`):
    `finrank ℂ (HolomorphicOneForm ℂ X) = 0`;
  - `analyticGenus_eq_zero_iff_subsingleton` (`AnalyticGenus.lean:33`):
    `Subsingleton (HolomorphicOneForm ℂ X)` — **the only holomorphic 1-form is
    zero.**

  This is genuinely all genus zero buys *in this substrate*: the space of global
  holomorphic 1-forms is trivial. Classically this is one face of
  `H⁰(X, Ω¹) = 0`, dual (Serre) to `H¹(X, 𝒪) = 0`, which is what forces
  `ℓ([P]) = 2`. **But the bridge from `H⁰(X,Ω¹)=0` to `H¹(X,𝒪)=0` to the
  dimension count is exactly the missing analytic content** (see §3).

### Sheaf-cohomology / Hodge scaffolding — present but inert for this count

`SheafCohomologyRS.lean` (0 sorries) defines `RSAbSheaf`, `RSSheafCohomology`,
`RSSheafCohomologyGroup`, `RSCechComplex`, `RSLineBundleSheaf`,
`RSLineBundleCohomology` — but its own header records **"No Čech-derived
comparison theorem (i.e. quasi-iso to derived global sections)."** Likewise
`HodgeDecomposition.lean` (0 sorries) is definitional/structural. There is:

- **no proven Riemann–Roch theorem** in the repo (grep for `riemann_roch` /
  `euler_characteristic` finds only Period/AbelJacobi-side and statement-level
  hits, none a proven `ℓ(D) − ℓ(K−D) = deg D + 1 − g`);
- **no `H¹(X, 𝒪) = 0` theorem**;
- **no Serre-duality theorem** connecting `H⁰(Ω¹)` to `H¹(𝒪)`.

The 0-sorry status of those files means they are *honest scaffolding*, not
hidden engines. Nothing there discharges the dimension count.

## 2. Classical proof routes, priced per step

### Route (a) — full Riemann–Roch

Classical statement: `ℓ(D) − ℓ(K−D) = deg D + 1 − g`. With `g = 0`,
`D = [P]` (`deg = 1`): `ℓ([P]) − ℓ(K−[P]) = 1 + 1 − 0 = 2`. The canonical
divisor `K` on a genus-0 surface has `deg K = 2g − 2 = −2`, so
`deg(K−[P]) = −3 < 0`, hence `ℓ(K−[P]) = 0` (no nonzero section with
negative-degree pole bound). Therefore `ℓ([P]) = 2`.

Per-step cost:

| Step | Substrate status | Cost |
|---|---|---|
| The RR theorem `ℓ(D)−ℓ(K−D)=deg D+1−g` for this surface notion | **ABSENT** — no RR theorem in repo, none in Mathlib | NEW ANALYTIC WORK, **engine-scale**: requires either sheaf-cohomology Euler characteristic + comparison (the missing `RSCechComplex` quasi-iso) or a full classical analytic RR proof |
| `deg(K−[P]) < 0 ⇒ ℓ(K−[P]) = 0` (negative-degree vanishing) | partial: `Divisor.Effective` + degree arithmetic are green; the *implication* (no holomorphic section of a negative-degree bundle) is **ABSENT** | NEW ANALYTIC WORK, routine-to-moderate *once* a degree/`MemRiemannRochSpace` incompatibility lemma is stated; but it presupposes the carrier knows analytic order = divisor degree, which is jc2's open germ-order bridge |
| `deg [P] = 1`, `deg K = −2` | degree API green; `deg K = 2g−2` needs the canonical-degree theorem (**ABSENT**) | the `K`-side is entirely unbuilt — there is no `K−[P]` germ-space carrier (cf. the `residual_dim_zero` placeholder) |

Route (a) is **not viable cheaply**: it imports the entire Riemann–Roch
machinery the project is trying to avoid, plus a canonical-divisor theory that
does not exist here. The repo's `residual_dim_zero` placeholder is precisely the
unbuilt `ℓ(K−[P])` half.

### Route (b) — direct genus-zero argument

Two classical sub-routes, both ultimately the same input:

- **(b1) Mittag-Leffler / residue construction.** Build, by hand, a meromorphic
  function with a single simple pole at `P` and no other poles. On a genus-0
  surface this exists iff the residue obstruction in `H¹(X, 𝒪)` vanishes. So
  (b1) ≡ producing the nonconstant section directly.
  - Existence of the local principal part (a simple pole in a chart): green
    chart substrate (`ChartBallPowerSeries`, local meromorphic data) suffices.
  - Globalizing it (killing the `H¹` obstruction): **ABSENT**, engine-scale.
    This is the Mittag-Leffler theorem on a compact surface, equivalent to
    `H¹(X,𝒪)=0`.

- **(b2) `H¹(X, 𝒪) = 0` vanishing argument.** Via Serre duality
  `H¹(X,𝒪) ≅ H⁰(X,Ω¹)^*`, and `H⁰(X,Ω¹)=0` IS available (it is exactly
  `analyticGenus = 0`, green). So `H¹(X,𝒪)=0` would follow **if Serre duality
  were proved.** It is not: there is no duality theorem in the repo (§1). The
  long exact sequence `0 → H⁰(𝒪) → H⁰(𝒪([P])) → ℂ_P → H¹(𝒪) → …` then gives
  `ℓ([P]) = h⁰(𝒪) + 1 = 2` once `H¹(𝒪)=0`.
  - `H⁰(X,Ω¹)=0`: GREEN (`analyticGenus_eq_zero_iff_subsingleton`).
  - Serre duality `H¹(𝒪) ≅ H⁰(Ω¹)^*`: **ABSENT**, engine-scale.
  - The skyscraper long-exact-sequence count: needs the `RSCechComplex`
    comparison theorem the substrate explicitly lacks — **ABSENT**.

Route (b2) is the *cleanest* mathematically because its one green input
(`H⁰(Ω¹)=0`) is already the genus hypothesis — but its single missing step
(Serre duality + the cohomology long exact sequence over the inert
`SheafCohomologyRS` scaffolding) is a full sheaf-cohomology development.

## 3. Lower and upper bounds priced separately

### Lower bound `finrank ≥ 2`

Needs: the finrank-1 constant line (**GREEN**,
`constantGermFamilyLineInRiemannRoch_finrank`) **plus one section of `L([P])`
linearly independent from the constants** — i.e. one nonconstant
`RiemannRochBoundedSection X (Divisor.point P)` whose germ family is outside
`constantGermFamilyLine`. Given such a section `s`, `finrank ≥ 2` is **green
linear algebra**: `{1, s}` independent in a module ⇒ `finrank ≥ 2` (Mathlib
`finrank` lemmas on independent families; the span is inside the germ space by
`…le_RiemannRochGermSpace`).

So the **entire** cost of the lower bound is the *existence of one nonconstant
function in `L([P])`*. In this substrate that nonconstant section does not
exist green and cannot be borrowed non-circularly:

- The fixed-pole chain `genusZero_pointRRSection_meromorphic_getD_exists`
  (`RiemannRoch.lean:921`) and `genusZero_fixedPole_*_nonempty`
  (`:1103`, `MeromorphicToBranchedCover.lean:4502/4526`) **do** produce such a
  section — but they depend on open sorries and, per goal.md, **consume the very
  root** (they are downstream of the dimension/biholomorphism content). Routing
  through them is the forbidden circular chain.
- The honest non-circular source is a genus-0 existence theorem (a degree-1
  meromorphic function), i.e. exactly route (b1) — **engine-scale**.

**Lower-bound verdict:** trivial linear algebra over **one** missing existence
theorem that is itself engine-scale. Cheaper than the upper bound only in that
it needs the section to *exist*, not to be *unique-up-to-2*.

### Upper bound `finrank ≤ 2`

Needs: **no third independent section** — every `L([P])` section is a ℂ-combination
of `1` and the one pole function. Classically this is the `ℓ(K−[P])=0` /
`H¹(X,𝒪)=0` direction (routes (a) tail, (b2)). The span-extraction package
(jc3) lets one *write* an arbitrary `F` as a finite generator sum, but gives **no
upper bound** on independent generators. There is no green path; the input is:

- negative-degree vanishing `ℓ(K−[P])=0` (route a), **or**
- `H¹(X,𝒪)=0` via Serre duality from the green `H⁰(Ω¹)=0` (route b2).

Both **ABSENT**, both engine-scale, and (b2) additionally needs the
`SheafCohomologyRS` comparison theorem the file says it lacks.

**Upper-bound verdict:** strictly the harder half. It is the genus-zero
Riemann–Roch upper bound and has no shortcut in this substrate.

## 4. Anti-circularity audit

The priced route avoids all three forbidden sources:

- **No fixed-pole chain.** The lower bound's nonconstant section must come from a
  *fresh* genus-0 existence theorem (route b1), **not** from
  `genusZero_pointRRSection_meromorphic_getD_exists` /
  `genusZero_fixedPole_*_nonempty` — which are sorry-dependent and downstream of
  this root. The pricing explicitly flags those as the circular trap and does
  not count them as substrate.
- **No biholomorphism / Path A output.** Neither bound uses #232/#233/#234
  outputs or any Montel/uniformization construction. (Indeed Path A *consumes*
  genus-0 facts; using its output here would be circular twice over.)
- **No `True`-stubs.** The six `CompactRiemannSurface.lean` stubs
  (`chart_local_equicontinuous`, `chart_local_arzela_ascoli`,
  `global_totally_bounded_via_chart_cover`, `lebesgue_number_chart_cover`,
  `chart_diagonal_extraction`, `global_sup_via_chart_max`) prove only `True` and
  are not cited.

The only green inputs used are: the finrank-1 constant line, the germ-space
module structure, `analyticGenus = 0 ⇒ H⁰(Ω¹)=0`, and (for the lower bound)
elementary independent-family `finrank` lemmas. Every remaining step is named
NEW ANALYTIC WORK.

## 5. Comparative conclusion vs the Perron/Koebe engine

jc1's Phase 0.5 found Path A needs an analytic engine that *constructs* a
normalized holomorphic/meromorphic map on an exhaustion from topological
genus-zero data (Perron/Dirichlet/Koebe scale), which the green Montel substrate
can only compactify and package *after* it exists.

Path B's kernel, priced here, needs:

1. (lower bound) **one** nonconstant meromorphic function with a single simple
   pole — i.e. a degree-1 meromorphic map, which **is** the genus-0 sphere
   uniformizer up to packaging; and
2. (upper bound) the genus-0 Riemann–Roch upper bound `ℓ([P]) ≤ 2`
   (`H¹(𝒪)=0` / `ℓ(K−[P])=0`), needing Serre duality or the absent sheaf-Čech
   comparison.

**These are the same analytic mountain.** The function in (1) is exactly what
the Path A engine constructs; (2) adds a second, independent classical theorem
(Serre duality / RR vanishing) with no substrate support. So:

> **Path B is comparable-to-more-expensive than the Path A engine, not
> cheaper.** Its lower bound is one engine-scale existence theorem (the same
> object Path A builds); its upper bound is a *second* engine-scale input
> (Riemann–Roch vanishing / Serre duality) with even less scaffolding than Path
> A's Montel substrate provides.

The single largest missing classical input, shared by both bounds in spirit, is
**the genus-zero existence/vanishing theorem** (`H¹(X,𝒪)=0`, equivalently the
degree-1 meromorphic function / Mittag-Leffler solvability). Its scale is
Riemann-existence / Perron-Koebe — multi-week analytic development, exactly as
jc1 found for Path A.

**Recommendation framing (manager-level, not a decision):** if the manager hoped
Path B would sidestep the analytic engine, this pricing says it does not. The
realistic options mirror jc1's: (i) build the genus-zero existence/vanishing
engine once (it then feeds *both* paths — Path A's sequence and Path B's lower
bound), accepting it as the project's central analytic frontier; or (ii) keep
both kernels parked as honest open providers and pursue a different non-circular
route to the genus-0 biholomorphism. There is no third, cheap door on Path B.

## Explicit non-substrate

Not cited as support anywhere above (open / circular / stub):

- `genusZero_pointRiemannRochGermSpaceDimensionInput` (the root being priced),
  `genusZero_pointRiemannRochElement_of_germSpace_outside_constants`
  (separate open bridge, jc0).
- `genusZero_pointRRSection_meromorphic_getD_exists`,
  `genusZero_fixedPole_meromorphicData_nonempty`,
  `genusZero_fixedPole_*_nonempty` (sorry-dependent, circular).
- The six `CompactRiemannSurface.lean` `True`-stubs listed in §4.
- `RSSheafCohomology` / `RSCechComplex` / `HodgeDecomposition` decls — present
  and 0-sorry, but definitional scaffolding with no comparison/vanishing
  theorem, hence not analytic support for the count.
