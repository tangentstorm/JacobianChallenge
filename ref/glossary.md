# Glossary

## Boundary

The formal edge of a chain. For example, the boundary of an oriented path is
its endpoint minus its starting point, and the boundary of a filled triangle is
the signed sum of its three edges.

## Closed Chain

A chain whose boundary is zero. In degree 1, this is the algebraic version of a
closed loop, or an integer combination of loops, with no loose endpoints.

## Closed Form

A differential form whose exterior derivative is zero. For a 1-form, this means
it has no local obstruction to being a derivative; informally, it has no curl.

## Cohomology

A dual way to measure holes, often by studying functions or forms that evaluate
on cycles. In de Rham theory, cohomology is represented by closed forms modulo
exact forms.

## Curl

For a vector field or 1-form, curl measures local circulation around tiny loops.
Saying a 1-form has zero curl is an informal way to say it is locally closed or
locally conservative.

## Cycle

A closed chain. For first homology, cycles are loops or formal integer
combinations of loops.

## de Rham Cohomology

The cohomology theory built from differential forms. In degree 1, it is closed
1-forms modulo exact 1-forms.

## de Rham Theorem

The theorem saying de Rham cohomology agrees with singular cohomology. In degree
1, it says closed forms modulo exact forms match linear functionals on
homology classes of loops.

## Differential Form

An object that can be integrated over geometric pieces. A 1-form integrates
along paths; a 2-form integrates over surfaces.

## Exact Form

A form that is the exterior derivative of another object. A 1-form is exact if
it is `dF` for some function `F`.

## H1

The first homology group. It records independent loops in a space.

## H^1

The first cohomology group. It records linear functionals on independent loops,
or equivalently closed 1-forms modulo exact 1-forms in de Rham theory.

## Homology

A way to measure holes using chains and boundaries. Homology classes are cycles
modulo cycles that are themselves boundaries of higher-dimensional chains.

## Locally Conservative

A 1-form or vector field is locally conservative if, near every point, it is the
derivative of a local potential function. For 1-forms, this is the local
intuition behind being closed.

## Omega

In this project, `ω` (omega) usually denotes a differential form, often a
holomorphic 1-form or a closed smooth 1-form. It is the object being integrated
over paths or cycles.

## Path Independence

The property that an integral from one point to another depends only on the
endpoints, not on the chosen path. For closed 1-forms, this follows when all
periods over closed loops vanish.

## Period

The integral of a differential form over a cycle.

## Periods

The collection of all period values of a form over a chosen family of cycles,
or over all cycles in homology.

## Primitive

A function whose derivative is a given 1-form. If `dF = ω`, then `F` is a
primitive of `ω`.

## Singular Homology

A homology theory built from formal sums of maps from standard simplices into a
space. It is a flexible topological way to define cycles, boundaries, and holes.

## Stokes' Theorem

The theorem saying that the integral of a derivative over a region equals the
integral of the original form over the boundary. In degree 1, it implies exact
forms have zero periods around closed loops.
