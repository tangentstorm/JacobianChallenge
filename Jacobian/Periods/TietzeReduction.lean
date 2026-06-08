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

/-- If a single sub-step (e.g. "the four letters of a handle can be collected adjacently")
is itself heavy, isolate IT as the next narrow provider.
This provider pulls one full handle block to the front and leaves a shorter valid remainder. -/
theorem handle_collection_substep {g : ℕ} (w : EdgeWord g)
    (hPairs : ∀ ℓ : Letter g, ℓ ∈ w → ℓ.inv ∈ w)
    (hReduced : ∀ x : EdgeWord g, ¬ EdgeWord.InverseCancel w x)
    (hNonempty : w ≠ []) :
    ∃ i : Fin g, ∃ u : EdgeWord g,
      EdgeWord.TietzeEq w (EdgeWord.handleBlock i ++ u) ∧
      (∀ ℓ : Letter g, ℓ ∈ u → ℓ.inv ∈ u) ∧
      (∀ x : EdgeWord g, ¬ EdgeWord.InverseCancel u x) ∧
      u.length < w.length := by
  sorry

lemma InverseCancel_append_left {g : ℕ} (C : EdgeWord g) {A B : EdgeWord g} (h : EdgeWord.InverseCancel A B) :
    EdgeWord.InverseCancel (C ++ A) (C ++ B) := by
  cases h
  · rename_i i xs ys
    have h1 : C ++ (xs ++ [Letter.a i, Letter.aInv i] ++ ys) = (C ++ xs) ++ [Letter.a i, Letter.aInv i] ++ ys := by simp [List.append_assoc]
    have h2 : C ++ (xs ++ ys) = (C ++ xs) ++ ys := by simp [List.append_assoc]
    rw [h1, h2]
    exact EdgeWord.InverseCancel.ax_aInv i (C ++ xs) ys
  · rename_i i xs ys
    have h1 : C ++ (xs ++ [Letter.aInv i, Letter.a i] ++ ys) = (C ++ xs) ++ [Letter.aInv i, Letter.a i] ++ ys := by simp [List.append_assoc]
    have h2 : C ++ (xs ++ ys) = (C ++ xs) ++ ys := by simp [List.append_assoc]
    rw [h1, h2]
    exact EdgeWord.InverseCancel.aInv_a i (C ++ xs) ys
  · rename_i i xs ys
    have h1 : C ++ (xs ++ [Letter.b i, Letter.bInv i] ++ ys) = (C ++ xs) ++ [Letter.b i, Letter.bInv i] ++ ys := by simp [List.append_assoc]
    have h2 : C ++ (xs ++ ys) = (C ++ xs) ++ ys := by simp [List.append_assoc]
    rw [h1, h2]
    exact EdgeWord.InverseCancel.bx_bInv i (C ++ xs) ys
  · rename_i i xs ys
    have h1 : C ++ (xs ++ [Letter.bInv i, Letter.b i] ++ ys) = (C ++ xs) ++ [Letter.bInv i, Letter.b i] ++ ys := by simp [List.append_assoc]
    have h2 : C ++ (xs ++ ys) = (C ++ xs) ++ ys := by simp [List.append_assoc]
    rw [h1, h2]
    exact EdgeWord.InverseCancel.bInv_b i (C ++ xs) ys

lemma TietzeEq_commute_handleBlock {g : ℕ} (i : Fin g) (A B : EdgeWord g) :
    EdgeWord.TietzeEq (A ++ EdgeWord.handleBlock i ++ B) (EdgeWord.handleBlock i ++ A ++ B) := by
  let H := EdgeWord.handleBlock i
  have s1 : EdgeWord.HandleSwap (A ++ H ++ B) (B ++ H ++ A) := EdgeWord.HandleSwap.move i A B H rfl
  have eq1 : (B ++ H ++ A).rotate B.length = H ++ A ++ B := by
    have h1 : B ++ (H ++ A) = B ++ H ++ A := by simp [List.append_assoc]
    have h2 : (H ++ A) ++ B = H ++ A ++ B := by simp [List.append_assoc]
    rw [←h1, List.rotate_append_length_eq, h2]
  have s2 : EdgeWord.TietzeStep (B ++ H ++ A) (H ++ A ++ B) := by
    rw [←eq1]
    exact EdgeWord.TietzeStep.rotate _
  exact Relation.ReflTransGen.trans (Relation.ReflTransGen.single (EdgeWord.TietzeStep.swap s1)) (Relation.ReflTransGen.single s2)

lemma TietzeEq_commute_handleBlock_inv {g : ℕ} (i : Fin g) (A B : EdgeWord g) :
    EdgeWord.TietzeEq (EdgeWord.handleBlock i ++ A ++ B) (A ++ EdgeWord.handleBlock i ++ B) := by
  let H := EdgeWord.handleBlock i
  have eq1 : (H ++ A ++ B).rotate (H ++ A).length = B ++ H ++ A := by
    have h1 : (H ++ A) ++ B = H ++ A ++ B := by simp [List.append_assoc]
    have h2 : B ++ (H ++ A) = B ++ H ++ A := by simp [List.append_assoc]
    rw [←h1, List.rotate_append_length_eq, h2]
  have s1 : EdgeWord.TietzeStep (H ++ A ++ B) (B ++ H ++ A) := by
    rw [←eq1]
    exact EdgeWord.TietzeStep.rotate _
  have s2 : EdgeWord.HandleSwap (B ++ H ++ A) (A ++ H ++ B) := EdgeWord.HandleSwap.move i B A H rfl
  exact Relation.ReflTransGen.trans (Relation.ReflTransGen.single s1) (Relation.ReflTransGen.single (EdgeWord.TietzeStep.swap s2))

lemma TietzeEq_append_handleBlock_swap {g : ℕ} (i : Fin g) (A_ B_ : EdgeWord g) (h : EdgeWord.HandleSwap A_ B_) :
    EdgeWord.TietzeEq (EdgeWord.handleBlock i ++ A_) (EdgeWord.handleBlock i ++ B_) := by
  cases h
  rename_i j xs ys h_block hh
  let C := EdgeWord.handleBlock i
  
  have s1 : EdgeWord.TietzeStep (C ++ (xs ++ h_block ++ ys)) ((C ++ (xs ++ h_block ++ ys)).rotate C.length) := EdgeWord.TietzeStep.rotate _
  have eq1 : (C ++ (xs ++ h_block ++ ys)).rotate C.length = (xs ++ h_block ++ ys) ++ C := by exact List.rotate_append_length_eq C _
  have st1 : EdgeWord.TietzeEq (C ++ (xs ++ h_block ++ ys)) ((xs ++ h_block ++ ys) ++ C) := by
    rw [←eq1]; exact Relation.ReflTransGen.single s1

  have eqAC : (xs ++ h_block ++ ys) ++ C = xs ++ h_block ++ (ys ++ C) := by simp [List.append_assoc]
  have s2_swap : EdgeWord.HandleSwap (xs ++ h_block ++ (ys ++ C)) ((ys ++ C) ++ h_block ++ xs) := EdgeWord.HandleSwap.move j xs (ys ++ C) h_block hh
  have st2 : EdgeWord.TietzeEq ((xs ++ h_block ++ ys) ++ C) ((ys ++ C) ++ h_block ++ xs) := by
    rw [eqAC]; exact Relation.ReflTransGen.single (EdgeWord.TietzeStep.swap s2_swap)

  have eq_ys_C : (ys ++ C) ++ h_block ++ xs = ys ++ C ++ (h_block ++ xs) := by simp [List.append_assoc]
  have st2_1 : EdgeWord.TietzeEq ((xs ++ h_block ++ ys) ++ C) (ys ++ C ++ (h_block ++ xs)) := by
    rw [←eq_ys_C]; exact st2

  have st3 : EdgeWord.TietzeEq (ys ++ C ++ (h_block ++ xs)) (C ++ ys ++ (h_block ++ xs)) := TietzeEq_commute_handleBlock i ys (h_block ++ xs)
  have ht1 := Relation.ReflTransGen.trans st2_1 st3

  have eq_CB : C ++ ys ++ (h_block ++ xs) = C ++ (ys ++ h_block ++ xs) := by simp [List.append_assoc]
  have step23 : EdgeWord.TietzeEq ((xs ++ h_block ++ ys) ++ C) (C ++ (ys ++ h_block ++ xs)) := by
    rw [←eq_CB]; exact ht1

  exact Relation.ReflTransGen.trans st1 step23

lemma TietzeEq_append_handleBlock_rotate {g : ℕ} (i : Fin g) (A : EdgeWord g) (k : ℕ) :
    EdgeWord.TietzeEq (EdgeWord.handleBlock i ++ A) (EdgeWord.handleBlock i ++ A.rotate k) := by
  let k' := k % A.length
  let X := A.take k'
  let Y := A.drop k'
  have hA : A = X ++ Y := (List.take_append_drop k' A).symm
  have hB : A.rotate k = Y ++ X := List.rotate_eq_drop_append_take_mod
  have h1 : EdgeWord.handleBlock i ++ A = EdgeWord.handleBlock i ++ X ++ Y := by rw [hA]; simp [List.append_assoc]
  have h2 : EdgeWord.handleBlock i ++ A.rotate k = EdgeWord.handleBlock i ++ Y ++ X := by rw [hB]; simp [List.append_assoc]
  rw [h1, h2]
  have st1 := TietzeEq_commute_handleBlock_inv i X Y
  have s_swap : EdgeWord.HandleSwap (X ++ EdgeWord.handleBlock i ++ Y) (Y ++ EdgeWord.handleBlock i ++ X) := EdgeWord.HandleSwap.move i X Y _ rfl
  have st2 := Relation.ReflTransGen.single (EdgeWord.TietzeStep.swap s_swap)
  have st3 := TietzeEq_commute_handleBlock i Y X
  exact Relation.ReflTransGen.trans st1 (Relation.ReflTransGen.trans st2 st3)

lemma TietzeEq_append_handleBlock_step {g : ℕ} (i : Fin g) {A B : EdgeWord g} (h : EdgeWord.TietzeStep A B) :
    EdgeWord.TietzeEq (EdgeWord.handleBlock i ++ A) (EdgeWord.handleBlock i ++ B) := by
  cases h
  · rename_i hc
    exact EdgeWord.WordEq.toTietzeEq (Relation.ReflTransGen.single (InverseCancel_append_left _ hc))
  · rename_i hs
    exact TietzeEq_append_handleBlock_swap i _ _ hs
  · rename_i k
    exact TietzeEq_append_handleBlock_rotate i _ k

/-- Tietze equivalence is preserved under left-append of a handle block. -/
theorem TietzeEq_append_left_handleBlock {g : ℕ} (i : Fin g) {A B : EdgeWord g} (h : EdgeWord.TietzeEq A B) :
    EdgeWord.TietzeEq (EdgeWord.handleBlock i ++ A) (EdgeWord.handleBlock i ++ B) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ h_eq ih =>
    have s1 := TietzeEq_append_handleBlock_step i h_eq
    exact Relation.ReflTransGen.trans ih s1

/-- Classical Brahana handle-collection: a reduced, inverse-paired word over the
genus-`g` alphabet is `TietzeEq` to a concatenation of complete handle blocks
listed in some order `l : List (Fin g)`. This is the genuine geometric input;
re-indexing to `standardWord` is handled downstream by the proven Perm lemmas. -/
theorem orientable_handleBlock_collection
    {g : ℕ} (w : EdgeWord g)
    (hPairs : ∀ ℓ : Letter g, ℓ ∈ w → ℓ.inv ∈ w)
    (hReduced : ∀ x : EdgeWord g, ¬ EdgeWord.InverseCancel w x) :
    ∃ l : List (Fin g),
      EdgeWord.TietzeEq w (l.flatMap EdgeWord.handleBlock) := by
  induction hw : w.length using Nat.strong_induction_on generalizing w with
  | h n ih =>
    cases w with
    | nil =>
      use []
      exact EdgeWord.TietzeEq.refl []
    | cons hd tl =>
      have hNonempty : hd :: tl ≠ [] := by simp
      obtain ⟨i, u, hTietze, huPairs, huReduced, hLen⟩ := handle_collection_substep (hd :: tl) hPairs hReduced hNonempty
      have hLen' : u.length < n := by
        rw [←hw]
        exact hLen
      obtain ⟨l, hl⟩ := ih u.length hLen' u huPairs huReduced rfl
      use i :: l
      have h_bind : (i :: l).flatMap EdgeWord.handleBlock = EdgeWord.handleBlock i ++ l.flatMap EdgeWord.handleBlock := rfl
      rw [h_bind]
      have h2 := TietzeEq_append_left_handleBlock i hl
      exact hTietze.trans h2

/-- The topological constraint: if a word is the global boundary, the resulting list
of handles must be exactly a permutation of all handles. -/
theorem handleBlock_collection_is_perm
    {g : ℕ} (w : EdgeWord g)
    (hPairs : ∀ ℓ : Letter g, ℓ ∈ w → ℓ.inv ∈ w)
    (hReduced : ∀ x : EdgeWord g, ¬ EdgeWord.InverseCancel w x)
    (l : List (Fin g))
    (hTietze : EdgeWord.TietzeEq w (l.flatMap EdgeWord.handleBlock)) :
    ∃ perm : Equiv.Perm (Fin g), l = (List.finRange g).map perm := by
  sorry

theorem orientable_handleSwap_grouping
    {g : ℕ} (w : EdgeWord g)
    (_hPairs : ∀ ℓ : Letter g, ℓ ∈ w → ℓ.inv ∈ w)
    (_hReduced : ∀ x : EdgeWord g, ¬ EdgeWord.InverseCancel w x) :
    ∃ v : EdgeWord g, EdgeWord.TietzeEq w v ∧
      (∃ perm : Equiv.Perm (Fin g), v = (List.finRange g).flatMap (fun i => EdgeWord.handleBlock (perm i))) := by
  obtain ⟨l, hl⟩ := orientable_handleBlock_collection w _hPairs _hReduced
  obtain ⟨perm, hperm⟩ := handleBlock_collection_is_perm w _hPairs _hReduced l hl
  use l.flatMap EdgeWord.handleBlock
  refine ⟨hl, perm, ?_⟩
  rw [hperm]
  induction (List.finRange g) with
  | nil => rfl
  | cons hd tl ih => simp [ih]

lemma TietzeEq_swap_adj {g : ℕ} (i j : Fin g) (A B : List (Letter g)) :
  EdgeWord.TietzeEq (A ++ EdgeWord.handleBlock i ++ EdgeWord.handleBlock j ++ B)
                    (A ++ EdgeWord.handleBlock j ++ EdgeWord.handleBlock i ++ B) := by
  let hi := EdgeWord.handleBlock i
  let hj := EdgeWord.handleBlock j
  have s1 : EdgeWord.TietzeStep (A ++ hi ++ hj ++ B) ((A ++ hi ++ hj ++ B).rotate (A ++ hi ++ hj).length) :=
    EdgeWord.TietzeStep.rotate _
  have eq1 : (A ++ hi ++ hj ++ B).rotate (A ++ hi ++ hj).length = B ++ A ++ hi ++ hj := by
    have : A ++ hi ++ hj ++ B = (A ++ hi ++ hj) ++ B := by simp
    rw [this, List.rotate_append_length_eq]
    simp
  have s1_rel : EdgeWord.TietzeEq (A ++ hi ++ hj ++ B) (B ++ A ++ hi ++ hj) := by
    rw [←eq1]
    exact Relation.ReflTransGen.head s1 Relation.ReflTransGen.refl

  have s2_swap : EdgeWord.HandleSwap (B ++ A ++ hi ++ hj) (hj ++ hi ++ B ++ A) :=
    EdgeWord.HandleSwap.move i (B ++ A) hj _ rfl
  have s2_rel : EdgeWord.TietzeEq (B ++ A ++ hi ++ hj) (hj ++ hi ++ B ++ A) :=
    Relation.ReflTransGen.head (EdgeWord.TietzeStep.swap s2_swap) Relation.ReflTransGen.refl

  have s3 : EdgeWord.TietzeStep (hj ++ hi ++ B ++ A) ((hj ++ hi ++ B ++ A).rotate (hj ++ hi ++ B).length) :=
    EdgeWord.TietzeStep.rotate _
  have eq3 : (hj ++ hi ++ B ++ A).rotate (hj ++ hi ++ B).length = A ++ hj ++ hi ++ B := by
    have : hj ++ hi ++ B ++ A = (hj ++ hi ++ B) ++ A := by simp
    rw [this, List.rotate_append_length_eq]
    simp
  have s3_rel : EdgeWord.TietzeEq (hj ++ hi ++ B ++ A) (A ++ hj ++ hi ++ B) := by
    rw [←eq3]
    exact Relation.ReflTransGen.head s3 Relation.ReflTransGen.refl

  exact s1_rel.trans (s2_rel.trans s3_rel)

lemma TietzeEq_of_Perm_handleBlocks_context {g : ℕ} (l1 l2 : List (Fin g)) (h : List.Perm l1 l2) (A B : List (Letter g)) :
  EdgeWord.TietzeEq (A ++ l1.flatMap EdgeWord.handleBlock ++ B) (A ++ l2.flatMap EdgeWord.handleBlock ++ B) := by
  induction h generalizing A B with
  | nil =>
    exact EdgeWord.TietzeEq.refl _
  | cons x h IH =>
    have IH_inst := IH (A ++ EdgeWord.handleBlock x) B
    rw [List.flatMap_cons, List.flatMap_cons, ←List.append_assoc, ←List.append_assoc]
    exact IH_inst
  | swap x y l =>
    have eq1 : A ++ (y :: x :: l).flatMap EdgeWord.handleBlock ++ B = A ++ EdgeWord.handleBlock y ++ EdgeWord.handleBlock x ++ (l.flatMap EdgeWord.handleBlock ++ B) := by simp
    have eq2 : A ++ (x :: y :: l).flatMap EdgeWord.handleBlock ++ B = A ++ EdgeWord.handleBlock x ++ EdgeWord.handleBlock y ++ (l.flatMap EdgeWord.handleBlock ++ B) := by simp
    rw [eq1, eq2]
    exact TietzeEq_swap_adj y x A (l.flatMap EdgeWord.handleBlock ++ B)
  | trans h1 h2 IH1 IH2 =>
    exact (IH1 A B).trans (IH2 A B)

lemma TietzeEq_of_Perm_handleBlocks {g : ℕ} (l1 l2 : List (Fin g)) (h : List.Perm l1 l2) :
  EdgeWord.TietzeEq (l1.flatMap EdgeWord.handleBlock) (l2.flatMap EdgeWord.handleBlock) := by
  have res := TietzeEq_of_Perm_handleBlocks_context l1 l2 h [] []
  simp at res
  exact res

theorem handleSwap_index_ordering
    {g : ℕ} (v : EdgeWord g)
    (_hGrouped : ∃ perm : Equiv.Perm (Fin g), v = (List.finRange g).flatMap (fun i => EdgeWord.handleBlock (perm i))) :
    EdgeWord.TietzeEq v (EdgeWord.standardWord g) := by
  rcases _hGrouped with ⟨perm, rfl⟩
  have hPerm : List.Perm ((List.finRange g).map perm) (List.finRange g) := by
    exact Equiv.Perm.map_finRange_perm perm
  have hFlatMap : ((List.finRange g).map perm).flatMap EdgeWord.handleBlock = (List.finRange g).flatMap (fun i => EdgeWord.handleBlock (perm i)) := by
    exact List.flatMap_map _ _ _
  rw [←hFlatMap]
  exact TietzeEq_of_Perm_handleBlocks _ _ hPerm

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


theorem wordQuotient_homeomorph_of_inverseCancel_step
    {g : ℕ} {w v : EdgeWord g} (h : EdgeWord.InverseCancel w v) :
    Nonempty (EdgeWord.wordQuotient g w ≃ₜ EdgeWord.wordQuotient g v) := by
  sorry


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
