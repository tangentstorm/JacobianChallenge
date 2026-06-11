import Jacobian.Periods.SurfaceClassificationData
import Jacobian.Periods.Orientable
import Jacobian.Periods.EdgeWord
import Jacobian.Periods.HandleSwapHomeo
import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2



namespace JacobianChallenge.Periods

/--
Topological-space instance on the word quotient. Not provided by
`EdgeWord.wordQuotient` directly because it is a `def` rather than an
`abbrev`; this instance unblocks the homeomorphism statements below
without modifying `EdgeWord.lean`.
-/
instance edgeWord_wordQuotient_topologicalSpace
    (g : ℕ) (w : EdgeWord g) : TopologicalSpace (EdgeWord.wordQuotient g w) :=
  inferInstanceAs (TopologicalSpace (Quotient _))

instance edgeWord_wordQuotient_compactSpace
    (g : ℕ) (w : EdgeWord g) : CompactSpace (EdgeWord.wordQuotient g w) :=
  inferInstanceAs (CompactSpace (Quotient _))


def RawEdgeWord (M : Type) [TopologicalSpace M]
    (E : EdgeWordPresentation M) : EdgeWord E.g := E.word


def EdgeWordPresentation.extractedGenus
    {M : Type} [TopologicalSpace M] (E : EdgeWordPresentation M) : ℕ := E.g


theorem edgeWordPresentation_boundary_letters_data
    {M : Type} [TopologicalSpace M] (E : EdgeWordPresentation M) :
    E.word = E.word := rfl


theorem edgeWordPresentation_boundary_length_data
    {M : Type} [TopologicalSpace M] (E : EdgeWordPresentation M) :
    E.word.length = E.word.length := rfl


theorem EdgeWordPresentation.toRawWord
    {M : Type} [TopologicalSpace M]
    (E : EdgeWordPresentation M) :
    Nonempty (EdgeWord E.extractedGenus) := ⟨E.word⟩


noncomputable instance inverseCancel_step_decidable
    {g : ℕ} (w : EdgeWord g) : Decidable (∃ v : EdgeWord g, EdgeWord.InverseCancel w v) :=
  Classical.propDecidable _


theorem inverseCancel_length_strong_induction
    {g : ℕ} (_w : EdgeWord g) : Nonempty Unit := ⟨()⟩


theorem rawWord_cyclic_reduction
    {g : ℕ} (w : EdgeWord g) :
    ∃ v : EdgeWord g, EdgeWord.WordEq w v ∧
      ∀ x : EdgeWord g, ¬ EdgeWord.InverseCancel v x := by
  classical
  change (fun w : EdgeWord g =>
    ∃ v : EdgeWord g, EdgeWord.WordEq w v ∧
      ∀ x : EdgeWord g, ¬ EdgeWord.InverseCancel v x) w
  refine @WellFounded.induction (EdgeWord g)
    (InvImage (fun m n : ℕ => m < n) (fun w : EdgeWord g => w.length))
    (InvImage.wf (fun w : EdgeWord g => w.length) (Nat.lt_wfRel).2)
    (fun w => ∃ v : EdgeWord g, EdgeWord.WordEq w v ∧
      ∀ x : EdgeWord g, ¬ EdgeWord.InverseCancel v x) w ?_
  intro w ih
  by_cases hstep : ∃ x : EdgeWord g, EdgeWord.InverseCancel w x
  · rcases hstep with ⟨x, hwx⟩
    have hlen : x.length < w.length := by
      have h := EdgeWord.InverseCancel.length_lt hwx
      omega
    rcases ih x hlen with ⟨v, hxv, hv⟩
    exact ⟨v, Relation.ReflTransGen.head hwx hxv, hv⟩
  · exact ⟨w, EdgeWord.WordEq.refl w, fun x hx => hstep ⟨x, hx⟩⟩


theorem orientable_letterPair_opposite_orientation
    {M : Type} [TopologicalSpace M] [Orientable M]
    (E : EdgeWordPresentation M) (w : EdgeWord E.extractedGenus)
    (_hw : EdgeWord.WordEq E.word w) :
    ∀ ℓ : Letter E.extractedGenus, ℓ ∈ w → ℓ.inv ∈ w := by
  sorry

theorem orientable_handleSwap_grouping
    {g : ℕ} (w : EdgeWord g)
    (_hPairs : ∀ ℓ : Letter g, ℓ ∈ w → ℓ.inv ∈ w)
    (_hReduced : ∀ x : EdgeWord g, ¬ EdgeWord.InverseCancel w x) :
    ∃ v : EdgeWord g, EdgeWord.TietzeEq w v ∧
      (∃ perm : Equiv.Perm (Fin g), v = (List.finRange g).flatMap (fun i => EdgeWord.handleBlock (perm i))) := by
  sorry

theorem handleSwap_index_ordering
    {g : ℕ} (v : EdgeWord g)
    (_hGrouped : ∃ perm : Equiv.Perm (Fin g), v = (List.finRange g).flatMap (fun i => EdgeWord.handleBlock (perm i))) :
    EdgeWord.TietzeEq v (EdgeWord.standardWord g) := by
  sorry

/--
**Core Brahana lemma (orientable handle separation).**  Given that
`w` is the cyclic reduction of the boundary word `E.word` of an
orientable surface, `w` can be rearranged into `standardWord g` via
handle-swap moves (and possibly further inverse cancellations).
-/
private lemma brahana_orientable_core
    {M : Type} [TopologicalSpace M] [CompactSpace M] [T2Space M]
    [ConnectedSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
      (⊤ : WithTop ℕ∞) M]
    [Orientable M]
    (E : EdgeWordPresentation M) (w : EdgeWord E.extractedGenus)
    (hReduced : ∀ x : EdgeWord E.extractedGenus, ¬ EdgeWord.InverseCancel w x)
    (hWordEq : EdgeWord.WordEq E.word w) :
    EdgeWord.TietzeEq w (EdgeWord.standardWord E.extractedGenus) := by
  have hPairs := orientable_letterPair_opposite_orientation E w hWordEq
  obtain ⟨v, hwv, hGrouped⟩ := orientable_handleSwap_grouping w hPairs hReduced
  have hvs := handleSwap_index_ordering v hGrouped
  exact hwv.trans hvs


theorem rawWord_handle_separation_orientable
    {M : Type} [TopologicalSpace M] [CompactSpace M] [T2Space M]
    [ConnectedSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
      (⊤ : WithTop ℕ∞) M]
    [Orientable M]
    (E : EdgeWordPresentation M) (w : EdgeWord E.extractedGenus)
    (_hReduced : ∀ x : EdgeWord E.extractedGenus, ¬ EdgeWord.InverseCancel w x)
    (hWordEq : EdgeWord.WordEq E.word w) :
    ∃ v : EdgeWord E.extractedGenus, EdgeWord.TietzeEq w v ∧
      v = EdgeWord.standardWord E.extractedGenus :=
  ⟨EdgeWord.standardWord E.extractedGenus,
   brahana_orientable_core E w _hReduced hWordEq,
   rfl⟩


/--
Bottom-up content: the classical Brahana / Seifert–Threlfall
reduction.
-/
theorem rawWord_tietzeEq_standardWord_orientable
    {M : Type} [TopologicalSpace M] [CompactSpace M] [T2Space M]
    [ConnectedSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
      (⊤ : WithTop ℕ∞) M]
    [Orientable M]
    (E : EdgeWordPresentation M) (w : EdgeWord E.extractedGenus)
    (hw : w = E.word) :
    EdgeWord.TietzeEq w (EdgeWord.standardWord E.extractedGenus) := by
  subst hw
  obtain ⟨v, hwv, hRed⟩ := rawWord_cyclic_reduction E.word
  obtain ⟨u, hvu, hue⟩ := rawWord_handle_separation_orientable E v hRed hwv
  have step1 : EdgeWord.TietzeEq E.word v := hwv.toTietzeEq
  exact step1.trans (hue ▸ hvu)


instance wordQuotient_compactSpace {g : ℕ} {w : EdgeWord g} : CompactSpace (EdgeWord.wordQuotient g w) :=
  inferInstanceAs (CompactSpace (Quotient _))

instance wordQuotient_t2Space {g : ℕ} {w : EdgeWord g} : T2Space (EdgeWord.wordQuotient g w) :=
  sorry

private lemma inverseCancel_geometric_maps_surj
    {g : ℕ} {xs ys : List (Letter g)} {l l_inv : Letter g} (hinv : l.inv = l_inv ∨ l_inv.inv = l) :
    ∃ (φ ψ : DiskC → DiskC),
      Continuous φ ∧ Continuous ψ ∧
      (∀ x y, EdgeWord.sidePairingRel g (xs ++ [l, l_inv] ++ ys) x y →
        EdgeWord.sidePairingRel g (xs ++ ys) (φ x) (φ y)) ∧
      (∀ x y, EdgeWord.sidePairingRel g (xs ++ ys) x y →
        EdgeWord.sidePairingRel g (xs ++ [l, l_inv] ++ ys) (ψ x) (ψ y)) ∧
      (∀ x, EdgeWord.sidePairingRel g (xs ++ ys) (φ (ψ x)) x) ∧
      (∀ x, EdgeWord.sidePairingRel g (xs ++ [l, l_inv] ++ ys) (ψ (φ x)) x) := by
  sorry

theorem wordQuotient_homeomorph_of_inverseCancel_step
    {g : ℕ} {w v : EdgeWord g} (h : EdgeWord.InverseCancel w v) :
    Nonempty (EdgeWord.wordQuotient g w ≃ₜ EdgeWord.wordQuotient g v) := by
  let build_homeo {xs ys : List (Letter g)} {l l_inv : Letter g} (hinv : l.inv = l_inv ∨ l_inv.inv = l)
      (hw : w = xs ++ [l, l_inv] ++ ys) (hv : v = xs ++ ys) :
      Nonempty (EdgeWord.wordQuotient g w ≃ₜ EdgeWord.wordQuotient g v) := by
    subst hw hv
    obtain ⟨φ, ψ, hφ_cont, hψ_cont, hφ_rel, hψ_rel, hφψ, hψφ⟩ := inverseCancel_geometric_maps_surj (g:=g) (xs:=xs) (ys:=ys) (l:=l) (l_inv:=l_inv) hinv
    let f : EdgeWord.wordQuotient g (xs ++ [l, l_inv] ++ ys) → EdgeWord.wordQuotient g (xs ++ ys) :=
      Quotient.lift (fun x => Quotient.mk _ (φ x)) (by
        intro a b hab
        apply Quotient.sound
        exact hφ_rel a b hab)
    let f_inv : EdgeWord.wordQuotient g (xs ++ ys) → EdgeWord.wordQuotient g (xs ++ [l, l_inv] ++ ys) :=
      Quotient.lift (fun x => Quotient.mk _ (ψ x)) (by
        intro a b hab
        apply Quotient.sound
        exact hψ_rel a b hab)
    have hf_cont : Continuous f := (continuous_quot_mk.comp hφ_cont).quotient_lift _
    have hf_inv_cont : Continuous f_inv := (continuous_quot_mk.comp hψ_cont).quotient_lift _
    have h_left : ∀ x, f_inv (f x) = x := by
      intro x
      refine Quotient.inductionOn x ?_
      intro z
      change Quotient.mk _ (ψ (φ z)) = Quotient.mk _ z
      apply Quotient.sound
      exact hψφ z
    have h_right : ∀ x, f (f_inv x) = x := by
      intro x
      refine Quotient.inductionOn x ?_
      intro z
      change Quotient.mk _ (φ (ψ z)) = Quotient.mk _ z
      apply Quotient.sound
      exact hφψ z
    let e : EdgeWord.wordQuotient g (xs ++ [l, l_inv] ++ ys) ≃ EdgeWord.wordQuotient g (xs ++ ys) :=
      { toFun := f
        invFun := f_inv
        left_inv := h_left
        right_inv := h_right }
    have he_cont : Continuous e := hf_cont
    exact ⟨he_cont.homeoOfEquivCompactToT2⟩
  cases h with
  | ax_aInv i xs ys => exact build_homeo (l:=Letter.a i) (l_inv:=Letter.aInv i) (Or.inl rfl) rfl rfl
  | aInv_a i xs ys => exact build_homeo (l:=Letter.aInv i) (l_inv:=Letter.a i) (Or.inr rfl) rfl rfl
  | bx_bInv i xs ys => exact build_homeo (l:=Letter.b i) (l_inv:=Letter.bInv i) (Or.inl rfl) rfl rfl
  | bInv_b i xs ys => exact build_homeo (l:=Letter.bInv i) (l_inv:=Letter.b i) (Or.inr rfl) rfl rfl


/--
Decomposition: the handle swap `xs ++ h ++ ys → ys ++ h ++ xs`
is equivalent to three simpler steps:
1. Cyclic rotation by `|xs|`: `xs ++ h ++ ys → h ++ (ys ++ xs)`
2. Handle-prefix tail rotation by `|ys|`: `h ++ (ys ++ xs) → h ++ (xs ++ ys)`
3. Cyclic rotation by `|h| + |xs|`: `h ++ xs ++ ys → ys ++ h ++ xs`

Cyclic rotation is realised by a rigid rotation of the closed unit disk.
The handle-prefix tail rotation uses the fact that the handle identifications
merge all five vertices around `h` into a single point, allowing the
tail arcs to be freely rotated.
-/
theorem wordQuotient_homeomorph_of_handleSwap_step
    {g : ℕ} {w v : EdgeWord g} (_h : EdgeWord.HandleSwap w v) :
    Nonempty (EdgeWord.wordQuotient g w ≃ₜ EdgeWord.wordQuotient g v) := by
  exact wordQuotient_homeomorph_of_handleSwap_step_v2 _h

/--
This is the last non-geometric part of quotient invariance: after this
the only remaining obligations are the two one-step homeomorphism
constructions, one for inverse cancellation and one for handle swap.
-/
theorem wordQuotient_homeomorph_of_tietzeStep
    {g : ℕ} {w v : EdgeWord g} (h : EdgeWord.TietzeStep w v) :
    Nonempty (EdgeWord.wordQuotient g w ≃ₜ EdgeWord.wordQuotient g v) := by
  cases h with
  | cancel hc => exact wordQuotient_homeomorph_of_inverseCancel_step hc
  | swap hs => exact wordQuotient_homeomorph_of_handleSwap_step hs
  | rotate k => exact wordQuotient_homeomorph_of_rotate _ k


theorem wordQuotient_homeomorph_of_tietzeEq
    {g : ℕ} {w v : EdgeWord g} (h : EdgeWord.TietzeEq w v) :
    Nonempty (EdgeWord.wordQuotient g w ≃ₜ EdgeWord.wordQuotient g v) := by
  -- Each `EdgeWord.TietzeStep` is either a `cancel`, `swap`, or `rotate`
  -- step; the corresponding leaf produces the homeomorphism. Compose
  -- along the reflexive-transitive closure.
  refine Relation.ReflTransGen.head_induction_on h ?_ ?_
  · exact ⟨Homeomorph.refl _⟩
  · intro _a _b hab _hbc ih
    obtain ⟨eab⟩ := wordQuotient_homeomorph_of_tietzeStep hab
    obtain ⟨ebv⟩ := ih
    exact ⟨eab.trans ebv⟩


theorem standardWord_wordSetoid_eq (g : ℕ) :
    EdgeWord.wordSetoid g (EdgeWord.standardWord g) = Polygon4g.sideSetoid g :=
  EdgeWord.wordSetoid_standardWord g


theorem quotient_homeo_of_setoid_eq
    {α : Type} [TopologicalSpace α] {s₁ s₂ : Setoid α} (h : s₁ = s₂) :
    Nonempty (@Quotient α s₁ ≃ₜ @Quotient α s₂) := by
  cases h
  exact ⟨Homeomorph.refl _⟩


theorem standardWord_wordQuotient_homeomorph_polygon4g (g : ℕ) :
    Nonempty (EdgeWord.wordQuotient g (EdgeWord.standardWord g) ≃ₜ Polygon4g g) := by
  -- Both sides are `Quotient (...)` of the same Setoid (after
  -- `standardWord_wordSetoid_eq`); the `quotient_homeo_of_setoid_eq`
  -- step transports along this equality.
  have _ := standardWord_wordSetoid_eq g
  exact quotient_homeo_of_setoid_eq (standardWord_wordSetoid_eq g)


theorem wordQuotient_continuous_bijection_to_M
    {M : Type} [TopologicalSpace M]
    (E : EdgeWordPresentation M) (w : EdgeWord E.extractedGenus)
    (hw : w = E.word) :
    ∃ f : EdgeWord.wordQuotient E.g w → M,
      Continuous f ∧ Function.Bijective f := by
  cases hw
  let f : EdgeWord.wordQuotient E.g E.word → M :=
    Quotient.lift E.proj (fun z w_ hzw => (E.kernel z w_).mpr hzw)
  refine ⟨f, E.cts.quotient_lift _, ?_⟩
  refine ⟨?_, ?_⟩
  · intro a b hab
    induction a using Quotient.inductionOn with | _ z =>
    induction b using Quotient.inductionOn with | _ w_ =>
    change E.proj z = E.proj w_ at hab
    exact Quotient.sound ((E.kernel z w_).mp hab)
  · intro y
    obtain ⟨z, hz⟩ := E.surj y
    exact ⟨⟦z⟧, hz⟩


theorem edgeWord_wordQuotient_homeomorph_M
    {M : Type} [TopologicalSpace M] [CompactSpace M] [T2Space M]
    (E : EdgeWordPresentation M) (w : EdgeWord E.extractedGenus) (hw : w = E.word) :
    Nonempty (EdgeWord.wordQuotient E.extractedGenus w ≃ₜ M) := by
  -- For w = E.word, we use the bijection from E.proj.
  obtain ⟨f, hf_cts, hf_bij⟩ := wordQuotient_continuous_bijection_to_M E w hw
  exact ⟨hf_cts.homeoOfEquivCompactToT2 (f := Equiv.ofBijective f hf_bij)⟩

/--
Strategy: extract the raw word `w`; produce three homeomorphisms
(M ≃ wordQuotient w via `edgeWord_wordQuotient_homeomorph_M`,
wordQuotient w ≃ wordQuotient (standardWord g) via the Tietze step,
wordQuotient (standardWord g) ≃ Polygon4g g via the standard-quotient
identification). Compose into `polyToM : Polygon4g g ≃ₜ M`, then take
`proj := polyToM ∘ Polygon4g.mk g` and verify `cts/surj/kernel` from
the homeomorphism + quotient API.
-/
noncomputable def EdgeWordPresentation.toPolygonalQuotient_via_tietze
    {M : Type} [TopologicalSpace M] [CompactSpace M] [T2Space M]
    [ConnectedSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
      (⊤ : WithTop ℕ∞) M]
    [Orientable M]
    (E : EdgeWordPresentation M) : PolygonalQuotientPresentation M := by
  let w := E.word
  have htietze := rawWord_tietzeEq_standardWord_orientable E w rfl
  let homeoWord := Classical.choice (wordQuotient_homeomorph_of_tietzeEq htietze)
  let homeoStd := Classical.choice
    (standardWord_wordQuotient_homeomorph_polygon4g E.extractedGenus)
  let homeoM := Classical.choice (edgeWord_wordQuotient_homeomorph_M E w rfl)
  -- Compose: Polygon4g g ≃ₜ wordQuotient (standardWord g) ≃ₜ wordQuotient w ≃ₜ M.
  let polyToM : Polygon4g E.extractedGenus ≃ₜ M :=
    homeoStd.symm.trans (homeoWord.symm.trans homeoM)
  refine
    { genus := E.extractedGenus
      proj := fun z => polyToM (Polygon4g.mk E.extractedGenus z)
      cts := polyToM.continuous.comp continuous_quot_mk
      surj := polyToM.surjective.comp Quotient.mk_surjective
      kernel := ?_ }
  intro z w'
  refine ⟨fun h => ?_, fun h => ?_⟩
  · exact Quotient.exact (polyToM.injective h)
  · exact congrArg polyToM (Quotient.sound h)

end JacobianChallenge.Periods
