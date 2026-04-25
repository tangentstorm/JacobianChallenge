import Jacobian.Challenge

/-!
# Complex torus core definitions

This file owns the core complex-torus declarations:
`FullComplexLattice`, `quotient`, `mk`, `map`, the
quotient instances (`AddCommGroup`, `TopologicalSpace`, `T2Space`,
`CompactSpace`), and the supporting `compactSpace_quotient_of_cover`
lemma.

The declarations originally lived in
`Jacobian/WorkPackets/StatementBank.lean`, but as the lower-layer
quotient/lattice work has stabilized they have been promoted here so
that `StatementBank` can import this file rather than the reverse —
matching the natural dependency direction (completed work feeds the
work-packet bank, not vice versa).

`StatementBank.lean` keeps only the not-yet-implemented placeholder
target statements (charted-space, manifold, Lie-group) and the higher
queue contents (Periods, AnalyticJacobian, AbelJacobi, TraceDegree,
AntiHack), all of which depend on this file.
-/

namespace JacobianChallenge

noncomputable section

/-! ## Complex torus infrastructure -/

namespace ComplexTorus

variable (V W U : Type*) [NormedAddCommGroup V] [NormedAddCommGroup W] [NormedAddCommGroup U]
  [NormedSpace ℂ V] [NormedSpace ℂ W] [NormedSpace ℂ U]

/--
A full complex lattice in a finite-dimensional complex vector space.

The structure carries the analytic content needed for the quotient
`V ⧸ subgroup` to be a complex torus:
- `isClosed` gives Hausdorff/T2 on the quotient (via Mathlib's
  closed-subgroup → T1 instance plus the topological-group upgrade);
- `fundamentalDomain` together with `fundamentalDomain_isCompact` and
  `fundamentalDomain_covers` gives compactness on the quotient
  (cocompact lattice ⇒ compact quotient);
- `isDiscrete` is needed for the manifold-layer chart construction:
  closed cocompact additive subgroups of finite-dim normed real spaces
  are *not* discrete in general (counterexample `ℝ × ℤ ⊂ ℝ²`), so
  discreteness has to be witnessed explicitly. Together with
  `IsolationAtZero.exists_pos_le_norm_of_discreteTopology` and
  `MkInjOnSmallBall.mk_injOn_ball_of_isolation` it gives the
  small-ball injectivity property needed for chart construction.

A more polished implementation could replace these fields with
established Mathlib predicates such as `ZLattice.IsZLattice`; this
shape exposes the dependency surface concretely.
-/
structure FullComplexLattice where
  subgroup : AddSubgroup V
  isClosed : IsClosed (subgroup : Set V)
  /-- The subgroup is discrete in the subspace topology — independent
  of `isClosed`/cocompactness in general. -/
  isDiscrete : DiscreteTopology subgroup
  /-- A subset of `V` whose `subgroup`-translates cover `V`. -/
  fundamentalDomain : Set V
  fundamentalDomain_isCompact : IsCompact fundamentalDomain
  fundamentalDomain_covers :
    ∀ v : V, ∃ g ∈ subgroup, v - g ∈ fundamentalDomain

attribute [instance] FullComplexLattice.isDiscrete

/-- The complex torus associated to a full lattice. -/
abbrev quotient (Λ : FullComplexLattice V) : Type _ := V ⧸ Λ.subgroup

instance quotient_addCommGroup (Λ : FullComplexLattice V) : AddCommGroup (quotient V Λ) :=
  inferInstanceAs (AddCommGroup (V ⧸ Λ.subgroup))

instance quotient_topologicalSpace (Λ : FullComplexLattice V) : TopologicalSpace (quotient V Λ) :=
  inferInstanceAs (TopologicalSpace (V ⧸ Λ.subgroup))

/-- The quotient is `T2`: derived from `isClosed` via Mathlib's
    `QuotientGroup.instT1Space` plus the topological-group machinery. -/
instance quotient_t2Space (Λ : FullComplexLattice V) : T2Space (quotient V Λ) := by
  haveI : IsClosed (Λ.subgroup : Set V) := Λ.isClosed
  exact inferInstance

/-- If `K ⊆ V` is compact and every point of `V` lies in some
`subgroup`-translate of `K`, the quotient `V ⧸ subgroup` is compact.
This is the generic "cocompact lattice ⇒ compact quotient" lemma; the
`quotient_compactSpace` instance below specializes it to the lattice's
own fundamental domain. -/
theorem compactSpace_quotient_of_cover (Λ : FullComplexLattice V)
    {K : Set V} (hK : IsCompact K)
    (hcov : ∀ v : V, ∃ g ∈ Λ.subgroup, v - g ∈ K) :
    CompactSpace (V ⧸ Λ.subgroup) := by
  rw [← isCompact_univ_iff]
  have hsurj : (QuotientAddGroup.mk : V → V ⧸ Λ.subgroup) '' K = Set.univ := by
    ext q
    simp only [Set.mem_image, Set.mem_univ, iff_true]
    obtain ⟨v, hv⟩ := QuotientAddGroup.mk_surjective q
    obtain ⟨g, hg, hvg⟩ := hcov v
    exact ⟨v - g, hvg, by
      rw [show (QuotientAddGroup.mk (v - g) : V ⧸ Λ.subgroup)
            = QuotientAddGroup.mk v from
          QuotientAddGroup.eq.mpr (by simp [hg]), hv]⟩
  rw [← hsurj]
  exact hK.image QuotientAddGroup.continuous_mk

/-- The quotient is `CompactSpace`, derived from the lattice's compact
fundamental domain via `compactSpace_quotient_of_cover`. -/
instance quotient_compactSpace (Λ : FullComplexLattice V) :
    CompactSpace (quotient V Λ) :=
  compactSpace_quotient_of_cover V Λ Λ.fundamentalDomain_isCompact
    Λ.fundamentalDomain_covers

/-- The quotient projection from a vector space to its torus. -/
def mk (Λ : FullComplexLattice V) : V → quotient V Λ :=
  QuotientAddGroup.mk

lemma mk_surjective (Λ : FullComplexLattice V) : Function.Surjective (mk V Λ) :=
  QuotientAddGroup.mk_surjective

variable {V W U}

/-- A continuous additive map preserving lattices descends to a map of complex tori. -/
def map (Λ : FullComplexLattice V) (Γ : FullComplexLattice W) (f : V →+ W)
    (hf : ∀ v ∈ Λ.subgroup, f v ∈ Γ.subgroup) :
    quotient V Λ →+ quotient W Γ :=
  QuotientAddGroup.map Λ.subgroup Γ.subgroup f hf

lemma map_mk (Λ : FullComplexLattice V) (Γ : FullComplexLattice W) (f : V →+ W)
    (hf : ∀ v ∈ Λ.subgroup, f v ∈ Γ.subgroup) (v : V) :
    map Λ Γ f hf (mk V Λ v) = mk W Γ (f v) :=
  rfl

lemma map_id (Λ : FullComplexLattice V) :
    map Λ Λ (AddMonoidHom.id V) (by intro v hv; exact hv) = AddMonoidHom.id (quotient V Λ) :=
  QuotientAddGroup.map_id Λ.subgroup

lemma map_comp (Λ : FullComplexLattice V) (Γ : FullComplexLattice W)
    (Η : FullComplexLattice U) (f : V →+ W) (g : W →+ U)
    (hf : ∀ v ∈ Λ.subgroup, f v ∈ Γ.subgroup)
    (hg : ∀ w ∈ Γ.subgroup, g w ∈ Η.subgroup) :
    map Λ Η (g.comp f) (by
      intro v hv
      exact hg (f v) (hf v hv)) =
      (map Γ Η g hg).comp (map Λ Γ f hf) :=
  (QuotientAddGroup.map_comp_map (I := U) Λ.subgroup Γ.subgroup Η.subgroup f g hf hg).symm

end ComplexTorus

end

end JacobianChallenge
