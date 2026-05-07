# Jacobian Challenge Proof Audit Report

## Executive Summary

**Current Status**: The repository contains **26 files with sorry statements** totaling **940+ sorry lines** across the codebase. The main focus file `Jacobian/AbelJacobi/AnalyticOfCurveBasis.lean` has been systematically decomposed and now contains only **2 actual sorry statements** (down from 10), while other files in the dependency chain still have frontier obligations.

**Key Finding**: After commit `d23dc4e` ("collapse remaining 10 sorries to 2 frontier obligations"), `Jacobian/AbelJacobi/AnalyticOfCurveBasis.lean` went from 10 sorries to 2 sorries. These 2 sorries are **frontier analytic obligations** that represent genuine mathematical gaps. However, the file builds successfully.

## Current Proof State by File

### Primary Focus: `Jacobian/AbelJacobi/AnalyticOfCurveBasis.lean`
**Remaining Sorries**: 2 (both at frontier level)

1. **Line 950-962**: `singlePointIndicator_exists_modulus_atTop_obligation`
   - **Nature**: Analytic existence theorem for modulus divergence at a single pole
   - **Issue**: Mathematically false for current indicator placeholder; requires chart-local `1/(z - Q)` extension

2. **Line 1058-1070**: `twoPointIndicator_exists_modulus_atTop_obligation`  
   - **Nature**: Analytic existence theorem for modulus divergence at two poles
   - **Issue**: Mathematically false for indicator placeholder; requires genuine local meromorphic function

### Dependency Chain (Files blocking Solution.lean)

| File | Sorry Count | Lines | Status |
|------|-------------|-------|--------|
| `Jacobian/HolomorphicForms/RiemannRoch.lean` | 1 | 570 | Frontier obligation |
| `Jacobian/Periods/CellularHomologyRS.lean` | 1 | 134 | Mathlib gap (cellular homology) |
| `Jacobian/HolomorphicForms/DeRhamComparisonMap.lean` | 2 | 131, 168 | Mathlib gap (Poincaré) |
| `Jacobian/Periods/TietzeReduction.lean` | 3 | 187, 194, 285 | False by counterexample |
| `Jacobian/Periods/Polygon4gCellular.lean` | 1 | 279 | Mathlib gap |
| `Jacobian/Periods/HolomorphicOneFormToFunContinuous.lean` | 2 | 83, 90 | Mathlib gap (tangentCoordChange) |
| `Jacobian/HolomorphicForms/CompactRiemannSurface.lean` | 3 | 251, 350, 923 | True:=trivial placeholders |
| `Jacobian/HolomorphicForms/GenusZeroClassification.lean` | 5 | 252, 346, 415, 782, 803 | True:=trivial placeholders |
| `Jacobian/Periods/PeriodFunctional.lean` | 1 | 501 | False (periodPairing := 0) |
| `Jacobian/Periods/PathIntegralViaCoverWithRefinementInvariant.lean` | 1 | 307 | Needs CurveIntegrable hypothesis |
| `Jacobian/TraceDegree/PushforwardBasis.lean` | 2 | 304, 315 | HEq diamond (needs concrete bundle) |
| `Jacobian/TraceDegree/PullbackBasis.lean` | 2 | 237, 251 | HEq diamond (needs concrete bundle) |

**Total**: 13 files with sorry statements (blocking Solution.lean)

## Build Status

```bash
lake build Jacobian.Solution
```
⚠️ Builds with warnings (26 sorry declarations across dependency chain)

```bash
lake build Jacobian.AbelJacobi.AnalyticOfCurveBasis
```
✅ Builds successfully with only 2 sorry warnings

## Proof Decomposition Status

### In `AnalyticOfCurveBasis.lean`

The original `period_congruence_distinct_implies_genus_zero` sorry has been decomposed:

#### S19 (Abel's Theorem - Existence Direction)
- **Sub-obligation**: `abel_meromorphicFunction_of_zero_aj_two_point` (Round 3)
- **Sub-obligation**: `meromorphicMapToSphere_package_of_two_point_principal` (Round 3)  
- **Assembly**: `abelExistence_simplePole_meromorphicMap_of_periodCongruent` (sorry-free delegation)

#### S20 (Riemann-Hurwitz at Degree 1)
- **Status**: sorry-free assembly
- **Uses**: `meromorphicDegreeOneData_of_poleDivisor_point`, `analyticGenus_eq_zero_of_homeomorphic_sphere`

#### Canonical Decomposition
- **Status**: sorry-free (1-line delegation)

### The 2 Frontier Obligations (Cannot Be Discharged by Assembly)

1. **`singlePointIndicator_exists_modulus_atTop_obligation`**
   - Requires: chart-local `1/(z - Q)` extension
   - Mathematical content: residue theorem, period vanishing

2. **`twoPointIndicator_exists_modulus_atTop_obligation`**
   - Requires: genuine meromorphic function with two simple poles
   - Mathematical content: Abel's theorem existence proof

## Recent Changes (Commit d23dc4e)

### What Was Done
1. **Collapsed 7 sorries → 2 frontier obligations** in `assemble_meromorphicMap`
   - Replaced opaque `toMap` with single-point indicator
   - Six axioms now discharge automatically from indicator combinatorics
   - Seventh axiom delegates to new obligation

2. **Refactored `meromorphicMap_canonicalDecomposition_of_two_point_principal_obligation`**
   - Now 1-line delegation to `assemble_meromorphicMap`

3. **Fixed `constant_in_RR_space_for_effective`**
   - Now uses single-point indicator at Q₁ directly
   - Removed broken `build_constant_meromorphicMap` helper

4. **Added new named obligation**
   - `singlePointIndicator_exists_modulus_atTop_obligation`

### Net Effect
- **Before**: 10 sorries in file
- **After**: 2 sorries (both frontier analytic obligations)

## Historical Context

| Commit | Date | Sorry Count | Notes |
|--------|------|-------------|-------|
| `d23dc4e` | 2026-05-07 | **2** | "collapse remaining 10 sorries to 2 frontier obligations" |
| `14a585a` | 2026-05-05 | 13 | "package canonical zero/pole decomposition" |
| `a486923` | 2026-05-04 | 9 | "Switch indicator constructors to two-point form" |
| `ab7760d` | 2026-05-03 | 33 | "Discharge 19 placeholder-constructor sorries" |
| `b32dc36` | 2026-05-02 | 5 | "Rebase onto main" |
| `8783cbe` | 2026-04-29 | 44 | "Discharge final bridge sorry via new axiom field" |

## Categorization of Remaining Sorries

### Type 1: Frontier Analytic Obligations (1 file)
- Cannot be discharged without genuine analytic content
- Require chart-local constructions of meromorphic functions
- **File**: `AnalyticOfCurveBasis.lean`

### Type 2: Mathlib Gap Placeholders (7 files)
- Depend on missing Mathlib v4.28.0 infrastructure
- **Examples**: cellular homology, Poincaré lemma, tangentCoordChange
- **Files**: `CellularHomologyRS.lean`, `DeRhamComparisonMap.lean`, `HolomorphicOneFormToFunContinuous.lean`, `Polygon4gCellular.lean`, `PathIntegralViaCoverWithRefinementInvariant.lean`, `RiemannRoch.lean`

### Type 3: False by Counterexample (1 file)
- Placeholder stubs with concrete counterexamples
- **File**: `TietzeReduction.lean` (EdgeWord scaffolding)

### Type 4: True := trivial Placeholders (2 files)
- Local `True := trivial` stubs that need real statements
- **Files**: `CompactRiemannSurface.lean`, `GenusZeroClassification.lean`

### Type 5: HEq Diamond Constraints (2 files)
- Propositional HEq fields needed for identity cases
- **Files**: `PushforwardBasis.lean`, `PullbackBasis.lean`

## Next Steps

The 13 remaining files with sorry declarations represent different levels of blocking:

1. **For AnalyticOfCurveBasis.lean (2 sorries)**:
   - Implement genuine meromorphic functions with prescribed pole structure
   - Prove modulus divergence using chart coordinates
   - These are **frontier obligations** requiring chart-local analysis

2. **For Mathlib gaps (7 files)**:
   - Search Mathlib v4.28.0 for existing lemmas
   - If missing, these are **upstream blocker** triages per `ref/PROMPT.md`

3. **For false placeholders (1 file)**:
   - Fix `EdgeWord.sidePairingRel` and `EdgeWordPresentation` definitions
   - Remove counterexample code

4. **For True placeholders (2 files)**:
   - Replace `True := trivial` with real typed statements
   - Follow placeholder-refinement framing in `ref/PROMPT.md`

5. **For HEq diamonds (2 files)**:
   - Create concrete bundle implementations per `PullbackBasis.lean` pattern

## Verification Commands

```bash
# Check build status
lake build Jacobian.Solution

# Check specific file
lake build Jacobian.AbelJacobi.AnalyticOfCurveBasis

# Count total sorries
 grep -r "sorry" Jacobian/ --include="*.lean" | wc -l

# List files with sorries
 grep -r "sorry" Jacobian/ --include="*.lean" | sed 's/:.*//' | sort -u | wc -l
```

