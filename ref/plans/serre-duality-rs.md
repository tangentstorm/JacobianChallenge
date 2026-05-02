# `thm:serre-duality-rs` — top-down refinement plan

**Graph node**: `thm:serre-duality-rs` (sec02 Holomorphic forms and genus,
classed DECOMPOSE in `ref/scope-out.md`).

**Public surface**: two `sorry`-bearing declarations in
`Jacobian/HolomorphicForms/SerreDualityRS.lean` —

* `RSDualizingSheaf X : RSAbSheaf X` (the dualizing sheaf K_X).
* `serre_duality_rs X F : ∃ dualSheaf, …, Nonempty (SerreDualityRSDatum X F dualSheaf)`
  (existence of the Serre-pairing datum for an arbitrary abelian
  sheaf `F` on a compact Riemann surface).

**Status before refinement**: 2 frontier sorries, no decomposition.

**Status after 25 top-down rounds**: every sorry on the public surface
is either (a) sorry-free above named obligations, or (b) refined into
multiple strictly-smaller sorries with informative names. The named
obligations live under `Jacobian/HolomorphicForms/Serre/`.

## File layout (round-creation)

| File | Round | Role |
|---|---|---|
| `Serre/StructureSheaf.lean` | 1 | `RSStructureSheaf` (𝒪_X frontier) — refined further in round 6 |
| `Serre/CotangentSheaf.lean` | 1 | `RSCotangentSheaf` (Ω¹_X frontier) — refined further in round 7 |
| `Serre/DualizingSheaf.lean` | 1 | `RSDualizingSheaf := RSCotangentSheaf` (no own sorry) |
| `Serre/Datum.lean` | 2 | `SerreDualityRSDatum` (relocated structure, no own sorry) |
| `Serre/CanonicalDual.lean` | 2 | `serreDualSheaf F` + Module ℂ frontier instances |
| `Serre/DatumExists.lean` | 3 | `serre_datum_for_canonical_dual_exists` (assembly) |
| `Serre/Pairing.lean` | 4 | `serrePairing := traceMap ∘ H¹(eval) ∘ cupProduct` (assembly) |
| `Serre/H1Functoriality.lean` | 4 | `serreH1Map` (functoriality bridge frontier) |
| `Serre/TensorSheaf.lean` | 4/8 | `RSTensorAbSheaf` (assembly) |
| `Serre/TensorPresheaf.lean` | 8 | tensor presheaf frontier + sheaf-condition |
| `Serre/EvalSheafMap.lean` | 4/9 | `serreEvalSheafMap` |
| `Serre/EvalPresheafMap.lean` | 9 | presheaf-level evaluation pairing frontier |
| `Serre/CupProduct.lean` | 4/10 | `serreCupProductH0H1` (assembly) |
| `Serre/CupProductYoneda.lean` | 10 | additive `cupProductYonedaH0H1` + linearity frontier |
| `Serre/TraceMap.lean` | 4 | `serreTraceMap` frontier |
| `Serre/H1CanonicalIso.lean` | 5/15 | `h1Canonical_isoToC` (assembly above residue map) |
| `Serre/ResidueMap.lean` | 15 | `residueMap` + inverse + round-trip identities frontiers |
| `Serre/Nondegeneracy.lean` | 11/12 | `serrePairing_nondegenerate_{left,right}` (sorry-free) |
| `Serre/Dolbeault.lean` | 13 | `serrePairing_witness_{left,right}` (delegates to L²) |
| `Serre/HodgePairing.lean` | 13 | `serrePairing_specialised_witness_{left,right}` (assembly) |
| `Serre/HarmonicForms.lean` | 13 | `harmonicForms`, surjections, `harmonicForms_to{H0,H1}` frontiers |
| `Serre/L2Pairing.lean` | 14 | `harmonicL2Pairing` + nondegeneracy + compatibility frontiers |
| `Serre/StructurePresheaf.lean` | 6 | holomorphic-function presheaf frontier + sheaf-condition |
| `Serre/CotangentPresheaf.lean` | 7 | holomorphic-1-form presheaf frontier + sheaf-condition |
| `Serre/LineBundleDual.lean` | 17 | `RSLineBundleDual` + iso-of-canonical-dual frontiers |
| `Serre/LineBundleSerre.lean` | 16 | `serre_duality_lineBundle_exists` (specialised) |
| `Serre/RiemannRochHighFromSerre.lean` | 18 | Serre-vanishing reduction lemmas |
| `Serre/RiemannRochUmbrellaPieces.lean` | 20 | umbrella package pieces |
| `Serre/CanonicalFiniteDim.lean` | 21/22 | FiniteDimensional discharge frontiers |
| `Serre/FiniteDimInstances.lean` | 21/22 | harmonic-form FD frontiers |
| `Serre/H0CanonicalIdentification.lean` | 23 | `H⁰(K_X) ≃ HolomorphicOneForm X` |
| `Serre/H1StructureViaSerre.lean` | 24 | `H¹(𝒪_X) ≃ HolomorphicOneForm X *` |

## Round-by-round refinement summary

1. `RSDualizingSheaf X := RSCotangentSheaf X` (cotangent sheaf realisation).
2. `serre_duality_rs X F` discharged from `serre_datum_for_canonical_dual_exists` + `serreDualSheaf` data.
3. `serre_datum_for_canonical_dual_exists` discharged from `serrePairing` + `serrePairing_nondegenerate_{left,right}`.
4. `serrePairing := traceMap ∘ H¹(eval) ∘ cupProduct` (assembly).
5. Introduce `h1Canonical_isoToC : H¹(K_X) ≃ₗ[ℂ] ℂ` (used in round 15/19).
6. `RSStructureSheaf := ⟨holomorphicFunctionPresheaf, _isSheaf⟩` (presheaf+sheaf-cond split).
7. `RSCotangentSheaf := ⟨holomorphicOneFormPresheaf, _isSheaf⟩` (same split).
8. `RSTensorAbSheaf := ⟨tensorAbPresheaf, _isSheaf⟩` (same split).
9. `serreEvalSheafMap` factors through `evalPresheafMap` + sheaf-lift (lift remains a small sorry).
10. `serreCupProductH0H1` assembled from `cupProductYonedaH0H1` (additive) + `_isLinear` (scalar) via `LinearMap.mk₂` (sorry-free).
11. `serrePairing_nondegenerate_left` discharged from `serrePairing_specialised_witness_left` + classical contrapositive (sorry-free).
12. `serrePairing_nondegenerate_right` analogously (sorry-free).
13. `serrePairing_witness_{left,right}` planned to factor through harmonic-form lifts + L²-pairing witness (proof body sorry pending universe cleanup).
14. Introduce `harmonicL2Pairing` + nondegeneracy witnesses + compatibility lemma.
15. `h1Canonical_isoToC` assembled from `residueMap` + `residueMap_inverse` + round-trip identities (sorry-free).
16. `serre_duality_lineBundle_exists` specialised line-bundle Serre-duality.
17. `RSLineBundleDual` + identification of `serreDualSheaf L` with `L⁻¹ ⊗ K_X`.
18. `riemann_roch_high_degree` design refines via `riemann_roch_high_degree_via_serre` + low-degree vanishing (proof body sorry pending universe cleanup).
19. **`h1_dualizing_sheaf_one_dim`** discharged sorry-free via `h1Canonical_isoToC` and `Module.finrank_self ℂ`.
20. `riemann_roch_umbrella_exists` design refines through `riemann_roch_classical_identity` + `RSLineBundleSub` (umbrella body sorry pending FD instances).
21. `finiteDimensionalSheafCohomologyRS_canonical` reduces to harmonic-form FD + surjections.
22. `finiteDimensionalSheafCohomologyRS_structure` analogously for 𝒪_X.
23. `h0Canonical_isoHolomorphicOneForm`: `H⁰(K_X) ≃ₗ[ℂ] HolomorphicOneForm ℂ X`.
24. `h1Structure_isoHolomorphicOneFormDual` + dim consequence (sorry-free finrank lemma above the iso frontier).
25. Bookkeeping: this plan, scope-out.md update, TopDown.md row.

## Sorry inventory (post-round-25)

* 2 sorries on the public `SerreDualityRS.lean` surface → **0** (both refined; structure relocated).
* `H1DualizingSheaf.lean` `h1_dualizing_sheaf_one_dim` → **sorry-free** (round 19).
* New named obligations under `Serre/`: ~80 sorry'd declarations, each
  small and well-named, ready for further decomposition or for
  Aristotle pickup.
* `RiemannRochHighDegree.lean` body still sorry-bearing pending
  universe cleanup of the dual-tensor cohomology Module instance, but
  body delegates to named obligations only (mathematical content
  complete above the named pieces).

## Where the chain bottoms out

The recursive refinement now reaches Mathlib-shaped obligations of
several flavours:

* **Universe / typeclass cleanup**: a handful of sorries are pure
  universe-level metavariable wrangling (e.g. the sheaf-`Hom` lift
  in `EvalSheafMap`, the `Module ℂ` instance plumbing on
  `RSTensorAbSheaf`-cohomology). These could be discharged by an
  Aristotle pickup once the universe-pinning convention is fixed.
* **Mathlib-frontier obligations**: presheaves of holomorphic
  functions / 1-forms (rounds 6–7), tensor product (round 8),
  evaluation (round 9), Yoneda product (round 10), residue map
  (round 15), harmonic forms + L²-pairing (rounds 13/14). Each is a
  named Mathlib-style obligation; landing them in Mathlib (or in a
  project-local module) discharges the chain.
* **Specialised obligations**: line-bundle dual (round 17),
  K_X-vs-Hom(F,K) iso (round 16), `H⁰(K_X) ≃ HolomorphicOneForm`
  (round 23). Each is mathematically routine once analytic-sheaf
  machinery is in place.

## Anti-hack audit

The refinement does not weaken the public spec: `RSDualizingSheaf` and
`serre_duality_rs` retain their original signatures. The intermediate
obligations are project-internal frontier definitions; replacing them
later with concrete Mathlib-backed values flows through to the public
surface without any signature change.
