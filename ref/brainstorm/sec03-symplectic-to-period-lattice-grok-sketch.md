# sec03 chain (symplectic-basis → period-lattice) — Grok sketch

Source: Grok project chat 653235e4-8ce6-442b-ba31-91b6f6680b4d
Received: 2026-05-01

## Node-by-node sketch

### thm:polygonal-model
**(a)** Surface classification: any compact oriented surface admits a CW/triangulation; via Morse theory or handle decompositions, X is a sphere with g handles ≅ 4g-gon with edges identified `a₁b₁a₁⁻¹b₁⁻¹⋯a_g b_g a_g⁻¹ b_g⁻¹`. Fundamental group: free on 2g generators / single relation `∏[a_i,b_i]=1`. Boundary 1-cycles → basis for H₁(X,ℤ) ≅ ℤ^{2g}; intersection form is standard symplectic J because transverse intersections only occur at glued vertices in standard way.
**(b)** `Mathlib.Topology.Manifold.Basic`, `Mathlib.AlgebraicTopology.FundamentalGroupoid`, `Mathlib.LinearAlgebra.BilinearForm`, `Mathlib.Topology.Homotopy`.
**(c)** `opaque polygonal_homeo : X ≃ₜ Polygon g` + `opaque induces_symplectic_basis`.
**(d)** Splittable: `lem:existence_polygonal_model`, `lem:induced_basis`, `lem:intersection_form_standard`. <300 LOC each.

### thm:stokes-on-rs-with-boundary
**(a)** RS-with-boundary = 2-real manifold with boundary + holomorphic atlas on interior. Triangulate / finite atlas (disks + half-disks near ∂). On each chart reduce to Stokes on ℂ-domains or upper half-plane (classical multi-var calc + Green). Glue via partition of unity; boundary terms match because orientations compatible & holomorphic transitions are orientation-preserving. Compactness ⇒ finite sum.
**(b)** `Mathlib.MeasureTheory.Integral`, `Mathlib.Geometry.Manifold` (charts/atlases/tangent), `Mathlib.Analysis.Calculus` (d on forms), `Mathlib.Topology.PartitionOfUnity`.
**(c)** `opaque stokes_on_half_plane`, `opaque rs_with_boundary : Type` (ManifoldWithBoundary + holomorphic interior atlas).
**(d)** Sub-leaves: `lem:local_stokes_in_charts` [needs Stokes], `lem:glue_via_partitions` [needs Stokes], `lem:holomorphic_transitions_preserve`.

### lem:primitive-on-polygon
**(a)** Open interior of 4g-gon is simply connected (star-shaped/contractible). For closed C^∞ 1-form, integral from basepoint defines C^∞ primitive F with dF=ω (Poincaré). Since ω is (1,0) in local charts, ∂̅F=0 ⇒ F holomorphic (Weyl's lemma / CR).
**(b)** `Mathlib.Analysis.Complex`, `Mathlib.MeasureTheory.Integral`, `Mathlib.Analysis.Calculus.PoincareLemma` (if present).
**(c)** `opaque poincare_lemma_on_polygon_interior : ∀ {ω : Ω¹ (PolygonInterior g)} (h : dω=0), ∃ F holomorphic, dF=ω`.
**(d)** Sub-leaves: `lem:poincare_Cinfty_primitive`, `lem:type_10_implies_holomorphic`. Neither needs Stokes.

### thm:bilinear-from-stokes
**(a)** Cut X along symplectic basis curves to get polygon-with-boundary. Apply Stokes to ω∧η (closed since both holomorphic): integral over polygon = boundary integral. Boundary = 2g pairs of edges; telescoping gives the Σ cross-terms.
**(b)** Bilinear forms on homology, path integrals.
**(c)** Polygonal homeo (node 1) + Stokes on RS-with-boundary (node 2).
**(d)** `lem:cut_and_stokes` [needs Stokes + polygonal], `lem:telescoping_boundary`.

### thm:hermitian-positivity
**(a)** Locally ω = f dz, ω̄ = f̄ dz̄, so iω∧ω̄ = |f|² dz∧dz̄·(i) = positive multiple of area form. Integrate: strictly positive unless f≡0 (continuity + connectedness).
**(b)** `Mathlib.Analysis.InnerProductSpace`, wedge in exterior algebra.
**(c)** `opaque local_positivity` (or local holomorphic-coordinate wedge expression).
**(d)** `lem:local_positivity_in_charts`, `lem:global_integral_strict`. **No Stokes.**

### thm:period-vectors-full-real-rank
**(a)** Suppose Σ c_i Π(a_i) + d_i Π(b_i) = 0 with c,d ∈ ℝ. Pair both sides with bilinear form (node 4) and use positivity (node 5) to force coefficients zero.
**(b)** Linear independence in vector spaces.
**(c)** Bilinear/positivity inputs (umbrella).
**(d)** `lem:period_matrix_nondegenerate` via umbrella.

### input:riemann-bilinear (umbrella)
Aggregates 4+5+6.

## Priority order (Grok)

1. **thm:hermitian-positivity** — purely local + compactness; ships immediately
2. **lem:primitive-on-polygon** — Poincaré + holomorphic; independent of Stokes
3. **thm:polygonal-model** — topology already strong in Mathlib
4. **thm:period-vectors-full-real-rank** — depends on umbrella but mostly linear algebra
5–7. bilinear-from-stokes + stokes-on-rs-with-boundary + sub-leaves — Stokes is the bottleneck; do last
