import Mathlib.Data.Fin.Basic
import Mathlib.Data.List.Basic
import Jacobian.Periods.Polygon4g

/-!
# Edge words for fundamental polygon side-pairing

For each genus `g`, this file defines the combinatorial data type
`EdgeWord g` representing a word in the generators
`a₀, b₀, a₀⁻¹, b₀⁻¹, …, a_{g-1}, b_{g-1}, a_{g-1}⁻¹, b_{g-1}⁻¹`
that labels the boundary of a fundamental `4g`-gon.

## Main definitions

* `Letter g` — the alphabet: four constructors `a i`, `b i`, `aInv i`, `bInv i`
  for `i : Fin g`.
* `EdgeWord g` — a word over `Letter g`, defined as `List (Letter g)`.
* `EdgeWord.IsStandardForm` — predicate characterising the standard relator
  `a₀ b₀ a₀⁻¹ b₀⁻¹ ⋯ a_{g-1} b_{g-1} a_{g-1}⁻¹ b_{g-1}⁻¹`.
* `standardWord g` — the standard-form word.
* `sidePairingRel g w` — the side-pairing equivalence relation on the closed
  unit disk `DiskC` determined by `w`. For `w = standardWord g`, it agrees
  with `Polygon4g.SideRel g`.
* `wordQuotient g w` — `DiskC / sidePairingRel g w`.

## References

This is leaf A2.1 of the surface-classification plan.
-/

namespace JacobianChallenge.Periods

/-- The four-letter alphabet for a genus-`g` polygon boundary word. -/
inductive Letter (g : ℕ) : Type where
  | a    (i : Fin g) : Letter g
  | b    (i : Fin g) : Letter g
  | aInv (i : Fin g) : Letter g
  | bInv (i : Fin g) : Letter g
  deriving DecidableEq

/-- An edge word is a list of letters over the genus-`g` alphabet. -/
def EdgeWord (g : ℕ) : Type := List (Letter g)

instance (g : ℕ) : Inhabited (EdgeWord g) := ⟨[]⟩

instance (g : ℕ) : DecidableEq (EdgeWord g) :=
  inferInstanceAs (DecidableEq (List (Letter g)))

namespace EdgeWord

/-- The block of four letters `aᵢ bᵢ aᵢ⁻¹ bᵢ⁻¹` for a single handle `i`. -/
def handleBlock {g : ℕ} (i : Fin g) : List (Letter g) :=
  [Letter.a i, Letter.b i, Letter.aInv i, Letter.bInv i]

/-- The standard relator word
`a₀ b₀ a₀⁻¹ b₀⁻¹ a₁ b₁ a₁⁻¹ b₁⁻¹ ⋯ a_{g-1} b_{g-1} a_{g-1}⁻¹ b_{g-1}⁻¹`
as an explicit list. -/
def standardWord (g : ℕ) : EdgeWord g :=
  (List.finRange g).flatMap handleBlock

/-- A predicate asserting that an edge word is in standard form, i.e. it equals
`standardWord g`. -/
def IsStandardForm {g : ℕ} (w : EdgeWord g) : Prop :=
  w = standardWord g

theorem standardWord_isStandardForm {g : ℕ} : (standardWord g).IsStandardForm :=
  rfl

instance {g : ℕ} (w : EdgeWord g) : Decidable w.IsStandardForm :=
  inferInstanceAs (Decidable (w = standardWord g))

end EdgeWord

/-- Inverse of a letter: `a i ↔ aInv i`, `b i ↔ bInv i`. -/
def Letter.inv {g : ℕ} : Letter g → Letter g
  | Letter.a i => Letter.aInv i
  | Letter.b i => Letter.bInv i
  | Letter.aInv i => Letter.a i
  | Letter.bInv i => Letter.b i

@[simp] lemma Letter.inv_inv {g : ℕ} (ℓ : Letter g) : ℓ.inv.inv = ℓ := by
  cases ℓ <;> rfl

namespace EdgeWord

/-! ### Quotient by side-pairing -/

/-- Generating relation for the side-pairing on the boundary of the
closed unit disk determined by a general edge word `w`. For any two
indices `i, j` such that the letters `w[i]` and `w[j]` are inverses,
the corresponding boundary arcs are identified with parameter reversal. -/
inductive SideGen (g : ℕ) (w : EdgeWord g) : DiskC → DiskC → Prop
  | pair (i j : Fin w.length) (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1)
      (h : (w.get i).inv = w.get j) :
      SideGen g w
        (boundaryParam' w.length i t)
        (boundaryParam' w.length j (1 - t))

/-- The reflexive-symmetric-transitive closure of `SideGen g w`. -/
def sidePairingRel (g : ℕ) (w : EdgeWord g) : DiskC → DiskC → Prop :=
  Relation.EqvGen (SideGen g w)

/-- Length of the standard word for genus `g`. -/
lemma standardWord_length (g : ℕ) : (standardWord g).length = 4 * g := by
  unfold standardWord
  simp [handleBlock, List.length_flatMap, List.finRange_length]

/-- The letters in `standardWord g` at indices `4i`, `4i+1`, `4i+2`, `4i+3`. -/
lemma standardWord_get_handle {g : ℕ} (i : Fin g) :
    (standardWord g).get ⟨4 * i.val, by rw [standardWord_length]; exact Nat.mul_lt_mul_of_pos_left i.is_lt (by omega)⟩ = Letter.a i ∧
    (standardWord g).get ⟨4 * i.val + 1, by rw [standardWord_length]; omega⟩ = Letter.b i ∧
    (standardWord g).get ⟨4 * i.val + 2, by rw [standardWord_length]; omega⟩ = Letter.aInv i ∧
    (standardWord g).get ⟨4 * i.val + 3, by rw [standardWord_length]; omega⟩ = Letter.bInv i := by
  unfold standardWord handleBlock
  simp [List.flatMap_get_index (fun _ => 4) (fun _ => rfl)]
  constructor <;> rfl

/-- Each letter appears exactly once in `standardWord g`. -/
lemma standardWord_get_unique {g : ℕ} (ℓ : Letter g) :
    ∃! i : Fin (standardWord g).length, (standardWord g).get i = ℓ := by
  unfold standardWord
  have h_flatMap : (List.finRange g).flatMap handleBlock = (standardWord g) := rfl
  have h_nodup : (standardWord g).Nodup := by
    rw [← h_flatMap]
    apply List.nodup_flatMap_of_nodup
    · exact List.nodup_finRange g
    · intro i; unfold handleBlock; simp
    · intro i j hij x hi hj
      unfold handleBlock at hi hj
      simp at hi hj; rcases hi with ⟨_|_|_|_⟩ <;> rcases hj with ⟨_|_|_|_⟩ <;> simp_all
  have h_mem : ℓ ∈ (standardWord g) := by
    rw [← h_flatMap, List.mem_flatMap]
    exists (match ℓ with | Letter.a i => i | Letter.b i => i | Letter.aInv i => i | Letter.bInv i => i)
    constructor
    · exact List.mem_finRange _
    · cases ℓ <;> simp [handleBlock]
  exact List.nodup_iff_exists_unique_get.mp h_nodup ℓ h_mem

/-- For the standard word, `sidePairingRel` agrees with `Polygon4g.SideRel`. -/
theorem sidePairingRel_standardWord (g : ℕ) :
    sidePairingRel g (standardWord g) = Polygon4g.SideRel g := by
  ext x y
  constructor
  · intro h
    induction h with
    | rel x y h =>
      cases h with
      | pair i j t ht hinv =>
        let L := (standardWord g).length
        have hL : L = 4 * g := standardWord_length g
        let k : Fin g := ⟨i.val / 4, by
          have : i.val < 4 * g := by rw [← hL]; exact i.is_lt
          exact Nat.div_lt_of_lt_mul this⟩
        let m := i.val % 4
        have hi : i.val = 4 * k.val + m := Nat.div_add_mod i.val 4
        have hm : m < 4 := Nat.mod_lt i.val (by omega)
        have h_get_i : (standardWord g).get i = (standardWord g).get ⟨4 * k.val + m, by rw [hL]; omega⟩ := by
          congr; exact hi
        
        interval_cases m
        · -- m = 0: w[i] = a k, so w[j] = aInv k, so j = 4k + 2
          have hi_val : (standardWord g).get i = Letter.a k := by
            rw [h_get_i]; exact (standardWord_get_handle k).1
          have hj_val : (standardWord g).get j = Letter.aInv k := by
            rw [← hinv, hi_val]; rfl
          have hj : j.val = 4 * k.val + 2 := by
            let j' : Fin L := ⟨4 * k.val + 2, by rw [hL]; omega⟩
            have hj' : (standardWord g).get j' = Letter.aInv k := (standardWord_get_handle k).2.2.1
            exact (standardWord_get_unique (Letter.aInv k)).unique (hj_val) (hj')
          rw [hi, hj, hL]
          exact Polygon4g.mk_a_pair g k t ht
        · -- m = 1: w[i] = b k, so w[j] = bInv k, so j = 4k + 3
          have hi_val : (standardWord g).get i = Letter.b k := by
            rw [h_get_i]; exact (standardWord_get_handle k).2.1
          have hj_val : (standardWord g).get j = Letter.bInv k := by
            rw [← hinv, hi_val]; rfl
          have hj : j.val = 4 * k.val + 3 := by
            let j' : Fin L := ⟨4 * k.val + 3, by rw [hL]; omega⟩
            have hj' : (standardWord g).get j' = Letter.bInv k := (standardWord_get_handle k).2.2.2
            exact (standardWord_get_unique (Letter.bInv k)).unique (hj_val) (hj')
          rw [hi, hj, hL]
          exact Polygon4g.mk_b_pair g k t ht
        · -- m = 2: w[i] = aInv k, so w[j] = a k, so j = 4k
          have hi_val : (standardWord g).get i = Letter.aInv k := by
            rw [h_get_i]; exact (standardWord_get_handle k).2.2.1
          have hj_val : (standardWord g).get j = Letter.a k := by
            rw [← hinv, hi_val]; rfl
          have hj : j.val = 4 * k.val := by
            let j' : Fin L := ⟨4 * k.val, by rw [hL]; omega⟩
            have hj' : (standardWord g).get j' = Letter.a k := (standardWord_get_handle k).1
            exact (standardWord_get_unique (Letter.a k)).unique (hj_val) (hj')
          rw [hi, hj, hL]
          -- Reverse of a_pair
          have h_rel := Polygon4g.mk_a_pair g k (1 - t) (by simp [ht])
          simp at h_rel; exact h_rel.symm
        · -- m = 3: w[i] = bInv k, so w[j] = b k, so j = 4k + 1
          have hi_val : (standardWord g).get i = Letter.bInv k := by
            rw [h_get_i]; exact (standardWord_get_handle k).2.2.2
          have hj_val : (standardWord g).get j = Letter.b k := by
            rw [← hinv, hi_val]; rfl
          have hj : j.val = 4 * k.val + 1 := by
            let j' : Fin L := ⟨4 * k.val + 1, by rw [hL]; omega⟩
            have hj' : (standardWord g).get j' = Letter.b k := (standardWord_get_handle k).2.1
            exact (standardWord_get_unique (Letter.b k)).unique (hj_val) (hj')
          rw [hi, hj, hL]
          -- Reverse of b_pair
          have h_rel := Polygon4g.mk_b_pair g k (1 - t) (by simp [ht])
          simp at h_rel; exact h_rel.symm
    | refl x => exact Relation.EqvGen.refl x
    | symm x y h ih => exact Relation.EqvGen.symm x y ih
    | trans x y z h1 h2 ih1 ih2 => exact Relation.EqvGen.trans x y z ih1 ih2
  · intro h
    induction h with
    | rel x y h =>
      cases h with
      | a_pair i t ht =>
        apply Relation.EqvGen.rel
        have hL := standardWord_length g
        let idx_i : Fin (standardWord g).length := ⟨4 * i.val, by rw [hL]; omega⟩
        let idx_j : Fin (standardWord g).length := ⟨4 * i.val + 2, by rw [hL]; omega⟩
        have hi : (standardWord g).get idx_i = Letter.a i := (standardWord_get_handle i).1
        have hj : (standardWord g).get idx_j = Letter.aInv i := (standardWord_get_handle i).2.2.1
        apply SideGen.pair idx_i idx_j t ht
        rw [hi, hj]; rfl
      | b_pair i t ht =>
        apply Relation.EqvGen.rel
        have hL := standardWord_length g
        let idx_i : Fin (standardWord g).length := ⟨4 * i.val + 1, by rw [hL]; omega⟩
        let idx_j : Fin (standardWord g).length := ⟨4 * i.val + 3, by rw [hL]; omega⟩
        have hi : (standardWord g).get idx_i = Letter.b i := (standardWord_get_handle i).2.1
        have hj : (standardWord g).get idx_j = Letter.bInv i := (standardWord_get_handle i).2.2.2
        apply SideGen.pair idx_i idx_j t ht
        rw [hi, hj]; rfl
    | refl x => exact Relation.EqvGen.refl x
    | symm x y h ih => exact Relation.EqvGen.symm x y ih
    | trans x y z h1 h2 ih1 ih2 => exact Relation.EqvGen.trans x y z ih1 ih2


/-- `sidePairingRel` is an equivalence relation. -/
theorem sidePairingRel_equivalence (g : ℕ) (w : EdgeWord g) :
    Equivalence (sidePairingRel g w) := by
  exact Relation.EqvGen.is_equivalence _

/-- The quotient of the closed unit disk by the side-pairing relation
determined by `w`. -/
def wordQuotient (g : ℕ) (w : EdgeWord g) : Type :=
  Quotient ⟨sidePairingRel g w, sidePairingRel_equivalence g w⟩

/-- The Setoid used to construct `wordQuotient g w`. -/
def wordSetoid (g : ℕ) (w : EdgeWord g) : Setoid DiskC :=
  ⟨sidePairingRel g w, sidePairingRel_equivalence g w⟩

/-- For the standard word, the wordSetoid equals `Polygon4g.sideSetoid g`. -/
theorem wordSetoid_standardWord (g : ℕ) :
    wordSetoid g (standardWord g) = Polygon4g.sideSetoid g := by
  unfold wordSetoid Polygon4g.sideSetoid
  congr 1
  exact sidePairingRel_standardWord g

/-- **A3.1.** For the standard word, `wordQuotient` is the same type as
`Polygon4g g`. The two are constructed as quotients of `DiskC` by the
same equivalence relation (`SideRel g`); their setoids coincide via
`wordSetoid_standardWord`. -/
theorem polygon4g_eq_standard_word_quotient (g : ℕ) :
    wordQuotient g (standardWord g) = Polygon4g g := by
  unfold wordQuotient Polygon4g
  rw [show (⟨sidePairingRel g (standardWord g), sidePairingRel_equivalence g (standardWord g)⟩
        : Setoid DiskC) = Polygon4g.sideSetoid g from wordSetoid_standardWord g]

/-! ### List-level Tietze cancellation -/

/-- The single-step Tietze swap relation: cancel an adjacent
inverse pair `[ℓ, ℓ⁻¹]` (or `[ℓ⁻¹, ℓ]`) anywhere in a word. -/
inductive InverseCancel : {g : ℕ} → EdgeWord g → EdgeWord g → Prop where
  | ax_aInv {g : ℕ} (i : Fin g) (xs ys : List (Letter g)) :
      InverseCancel (xs ++ [Letter.a i, Letter.aInv i] ++ ys) (xs ++ ys)
  | aInv_a {g : ℕ} (i : Fin g) (xs ys : List (Letter g)) :
      InverseCancel (xs ++ [Letter.aInv i, Letter.a i] ++ ys) (xs ++ ys)
  | bx_bInv {g : ℕ} (i : Fin g) (xs ys : List (Letter g)) :
      InverseCancel (xs ++ [Letter.b i, Letter.bInv i] ++ ys) (xs ++ ys)
  | bInv_b {g : ℕ} (i : Fin g) (xs ys : List (Letter g)) :
      InverseCancel (xs ++ [Letter.bInv i, Letter.b i] ++ ys) (xs ++ ys)

/-- Length strictly decreases by 2 under `InverseCancel`. -/
theorem InverseCancel.length_lt {g : ℕ} {w v : EdgeWord g}
    (h : InverseCancel w v) :
    v.length + 2 = w.length := by
  cases h <;> simp [List.length_append] <;> omega

/-- The reflexive-transitive closure (word equivalence under
finitely many cancellations). -/
def WordEq {g : ℕ} : EdgeWord g → EdgeWord g → Prop :=
  Relation.ReflTransGen InverseCancel

/-- `WordEq` is reflexive. -/
theorem WordEq.refl {g : ℕ} (w : EdgeWord g) : WordEq w w :=
  Relation.ReflTransGen.refl

/-- `WordEq` is transitive. -/
theorem WordEq.trans {g : ℕ} {a b c : EdgeWord g}
    (hab : WordEq a b) (hbc : WordEq b c) : WordEq a c :=
  Relation.ReflTransGen.trans hab hbc

/-- Handle swap: a full handle block `[a i, b i, aInv i, bInv i]` may
be exchanged with any two adjacent letters that are independent of `i`.
This is one of the two essential moves (the other being InverseCancel)
in the classical proof that any orientable edge word reduces to the
standard form. -/
inductive HandleSwap : {g : ℕ} → EdgeWord g → EdgeWord g → Prop where
  | move {g : ℕ} (i : Fin g) (xs ys : List (Letter g))
      (h : List (Letter g)) (_hh : h = [Letter.a i, Letter.b i, Letter.aInv i, Letter.bInv i]) :
      HandleSwap (xs ++ h ++ ys) (ys ++ h ++ xs)

/-- The combined word equivalence: closed under both `InverseCancel`
and `HandleSwap`. -/
inductive TietzeStep : {g : ℕ} → EdgeWord g → EdgeWord g → Prop where
  | cancel {g : ℕ} {w v : EdgeWord g} (h : InverseCancel w v) : TietzeStep w v
  | swap   {g : ℕ} {w v : EdgeWord g} (h : HandleSwap w v) : TietzeStep w v

/-- Word equivalence under the full Tietze move set. -/
def TietzeEq {g : ℕ} : EdgeWord g → EdgeWord g → Prop :=
  Relation.ReflTransGen TietzeStep

theorem TietzeEq.refl {g : ℕ} (w : EdgeWord g) : TietzeEq w w :=
  Relation.ReflTransGen.refl

theorem TietzeEq.trans {g : ℕ} {a b c : EdgeWord g}
    (hab : TietzeEq a b) (hbc : TietzeEq b c) : TietzeEq a c :=
  Relation.ReflTransGen.trans hab hbc

/-- Single-step embedding of `WordEq` (cancellations only) into `TietzeEq`. -/
theorem WordEq.toTietzeEq {g : ℕ} {w v : EdgeWord g} (h : WordEq w v) :
    TietzeEq w v :=
  h.mono (fun _ _ hc => TietzeStep.cancel hc)

end EdgeWord

end JacobianChallenge.Periods
