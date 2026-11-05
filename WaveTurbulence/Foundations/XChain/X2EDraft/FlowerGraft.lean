/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.XChain.X2EDraft.FlowerPair
public import WaveTurbulence.Foundations.XChain.PlainGraftEquality
public import WaveTurbulence.Foundations.XChain.LayerCutRetention

/-!
# X2E-2, step 3: the flower graft

Width `2P`, signature `ζ_j = (−1)^j`, and the partner `j ↦ j ⊕ 1` of a tree (flip the last bit).

**Flower graft data** `FlowerGraftData P p ζ`: plain graft data `base` (no irreducibility) together with a flower leaf
`𝔣_j` of each top tree (sign `ζ ζ_j`), such that every pair `{𝔣_j, 𝔣_{j⊕1}}` is a block of the partition. Such
a block is a terminal pair (its width is `2 < 4`).

**The flower graft** `flowerGraft D` is INDUCT's marked graft (`markedLayeredGardenGraft`) of the same top forest and
partition, in which each pair block carries the marked component `markedLeafLG` (two leaf trees, both marked
flowers, layer `p`), and every other block keeps its lower garden. This is the form of graftgen's
`kernelKgen_graft` (X2E-3).

**Statements.**
- `flLeaf D j`: the leaf `(j, 𝔣_j)` of the flower graft; `marked_iff`: a leaf is marked iff it is some `flLeaf D j`.
- `flowerGraft_isFlowerGarden`; the flower signs `ζ ζ_j`; the flowers are in layer `p`.
-/

@[expose] public section

namespace WaveTurbulence.X2E

open Finset Induct

/-! ## Trees in pairs -/

section Partner

variable {Pm : ℕ}

/-- The partner `j ⊕ 1` of a tree. -/
def partner (j : Fin (2 * Pm)) : Fin (2 * Pm) :=
  ⟨if (j : ℕ) % 2 = 0 then j + 1 else j - 1, by split_ifs <;> omega⟩

theorem partner_val (j : Fin (2 * Pm)) :
    (partner j : ℕ) = if (j : ℕ) % 2 = 0 then (j : ℕ) + 1 else (j : ℕ) - 1 := rfl

theorem partner_partner (j : Fin (2 * Pm)) : partner (partner j) = j := by
  apply Fin.ext
  simp only [partner_val]
  split_ifs <;> omega

theorem partner_involutive : Function.Involutive (partner (Pm := Pm)) := partner_partner

theorem partner_ne (j : Fin (2 * Pm)) : partner j ≠ j := by
  intro h
  have h1 := congrArg Fin.val h
  rw [partner_val] at h1
  split_ifs at h1 <;> omega

/-- The alternating signature `(−1)^j`. -/
def altFlowerSig (Pm : ℕ) : Fin (2 * Pm) → ℤˣ := fun j => (-1) ^ (j : ℕ)

theorem altFlowerSig_partner (j : Fin (2 * Pm)) : altFlowerSig Pm (partner j) = -altFlowerSig Pm j := by
  unfold altFlowerSig
  rw [partner_val]
  split_ifs with h
  · rw [pow_succ, mul_neg_one]
  · obtain ⟨k, hk⟩ : ∃ k, (j : ℕ) = k + 1 := ⟨(j : ℕ) - 1, by omega⟩
    rw [hk, Nat.add_sub_cancel, pow_succ, mul_neg_one, neg_neg]

end Partner

theorem four_le_of_isCanonG {n p : ℕ} {LG : LayeredGarden n} (h : IsCanonG p LG) : 4 ≤ n := by
  cases p with
  | zero => exact h.elim
  | succ q => exact h.1

/-! ## Marked leaf components -/

/-- The garden of `n` leaf trees, all of them marked flowers. -/
def markedLeafGarden (n : ℕ) (s : Fin n → ℤˣ) : Garden n where
  sig := s
  tree := fun _ => TTree.leaf
  pair := id
  mark := fun _ => some MarkTag.equal
  pair_pair _ := rfl
  pair_eq_iff _ := by simp
  pair_sign _ h := absurd rfl h

/-- The marked leaf garden in layer `p`. -/
def markedLeafLG (n : ℕ) (s : Fin n → ℤˣ) (p : ℕ) : LayeredGarden n where
  garden := markedLeafGarden n s
  layer := fun _ => p
  isLayering := ⟨fun _ _ => le_rfl, fun _ => rfl⟩

/-! ## Flower graft data -/

/-- **Flower graft data.** -/
structure FlowerGraftData (Pm p : ℕ) (ζ : ℤˣ) where
  base : PlainGraftData (altFlowerSig Pm) p
  fl : Fin (2 * Pm) → TTree.Path
  fl_mem : ∀ j, fl j ∈ (base.top j).leaves
  fl_sign : ∀ j, TTree.pathSign (altFlowerSig Pm j) (fl j) = ζ * altFlowerSig Pm j
  pair_mem : ∀ j, ({⟨(j, fl j), fl_mem j⟩, ⟨(partner j, fl (partner j)), fl_mem (partner j)⟩} :
    Finset (GLeaf base.top)) ∈ base.partition.parts

namespace FlowerGraftData

variable {Pm p : ℕ} {ζ : ℤˣ} (D : FlowerGraftData Pm p ζ)

/-- The flower of tree `j`, as a top leaf. -/
def flAt (j : Fin (2 * Pm)) : GLeaf D.base.top := ⟨(j, D.fl j), D.fl_mem j⟩

/-- The pair block of tree `j`. -/
def pairBlock (j : Fin (2 * Pm)) : Finset (GLeaf D.base.top) := {D.flAt j, D.flAt (partner j)}

theorem pairBlock_mem (j : Fin (2 * Pm)) : D.pairBlock j ∈ D.base.partition.parts := D.pair_mem j

theorem flAt_ne (j : Fin (2 * Pm)) : D.flAt j ≠ D.flAt (partner j) := by
  intro h
  exact partner_ne j (congrArg (fun l : GLeaf D.base.top => l.1.1) h).symm

theorem card_pairBlock (j : Fin (2 * Pm)) : (D.pairBlock j).card = 2 := card_pair (D.flAt_ne j)

theorem pairBlock_partner (j : Fin (2 * Pm)) : D.pairBlock (partner j) = D.pairBlock j := by
  unfold pairBlock
  rw [partner_partner, pair_comm]

/-- A block is a pair block. -/
def IsPairBlock (B : Finset (GLeaf D.base.top)) : Prop := ∃ j, B = D.pairBlock j

theorem part_flAt (j : Fin (2 * Pm)) : (blockRootEquiv D.base.top D.base.partition (D.flAt j)).1 =
    ⟨D.pairBlock j, D.pairBlock_mem j⟩ :=
  blockRootEquiv_block_of_mem D.base.top D.base.partition ⟨D.pairBlock j, D.pairBlock_mem j⟩ (D.flAt j)
    (mem_insert_self _ _)

theorem tree_of_isPairBlock {B : D.base.partition.parts} (hB : D.IsPairBlock B.1) :
    (D.base.low B).garden.tree = fun _ => TTree.leaf := by
  obtain ⟨j, hj⟩ := hB
  rcases D.base.component B with hc | ht
  · exfalso
    have h4 := four_le_of_isCanonG hc
    have hc2 : B.1.card = 2 := hj ▸ D.card_pairBlock j
    omega
  · exact funext ht.2.1

theorem layer_of_isPairBlock {B : D.base.partition.parts} (hB : D.IsPairBlock B.1)
    (a : GNode (D.base.low B).garden.tree) : (D.base.low B).layer a = p := by
  obtain ⟨j, hj⟩ := hB
  rcases D.base.component B with hc | ht
  · exfalso
    have h4 := four_le_of_isCanonG hc
    have hc2 : B.1.card = 2 := hj ▸ D.card_pairBlock j
    omega
  · exact ht.2.2 a

open Classical in
/-- The lower components of the flower graft: marked leaves at the pair blocks. -/
noncomputable def lowFl (B : D.base.partition.parts) : LayeredGarden B.1.card :=
  if D.IsPairBlock B.1 then markedLeafLG B.1.card (D.base.low B).garden.sig p else D.base.low B

theorem lowFl_of_pair {B : D.base.partition.parts} (hB : D.IsPairBlock B.1) :
    D.lowFl B = markedLeafLG B.1.card (D.base.low B).garden.sig p := by
  unfold lowFl
  exact ite_eq_left hB

theorem lowFl_of_not {B : D.base.partition.parts} (hB : ¬ D.IsPairBlock B.1) : D.lowFl B = D.base.low B := by
  unfold lowFl
  exact ite_eq_right hB

theorem lowFl_sig (B : D.base.partition.parts) (k : Fin B.1.card) :
    (D.lowFl B).garden.sig k = nodeSign (altFlowerSig Pm)
      ((blockRootEquiv D.base.top D.base.partition).symm ⟨B, k⟩).1 := by
  by_cases hB : D.IsPairBlock B.1
  · rw [D.lowFl_of_pair hB]
    exact D.base.sign B k
  · rw [D.lowFl_of_not hB]
    exact D.base.sign B k

theorem lowFl_tree (B : D.base.partition.parts) : (D.lowFl B).garden.tree = (D.base.low B).garden.tree := by
  by_cases hB : D.IsPairBlock B.1
  · rw [D.lowFl_of_pair hB, D.tree_of_isPairBlock hB]
    rfl
  · rw [D.lowFl_of_not hB]

theorem lowFl_bound (B : D.base.partition.parts) (a : GNode (D.lowFl B).garden.tree) : (D.lowFl B).layer a ≤ p := by
  by_cases hB : D.IsPairBlock B.1
  · have h := congrArg (fun G : LayeredGarden B.1.card => ∀ a : GNode G.garden.tree, G.layer a ≤ p)
      (D.lowFl_of_pair hB)
    exact (cast h.symm (fun _ => le_rfl : ∀ a : GNode (markedLeafLG B.1.card (D.base.low B).garden.sig p).garden.tree,
      (markedLeafLG B.1.card (D.base.low B).garden.sig p).layer a ≤ p)) a
  · have h := congrArg (fun G : LayeredGarden B.1.card => ∀ a : GNode G.garden.tree, G.layer a ≤ p)
      (D.lowFl_of_not hB)
    exact (cast h.symm (D.base.layer_bound B)) a

/-- **The flower graft.** -/
noncomputable def flowerGraft : LayeredGarden (2 * Pm) :=
  markedLayeredGardenGraft (altFlowerSig Pm) D.base.top D.base.partition D.lowFl p D.lowFl_sig D.lowFl_bound

theorem flowerGraft_tree : D.flowerGraft.garden.tree = D.base.graft.garden.tree := by
  change graftForest D.base.top (blockGraftTrees D.base.top D.base.partition (fun B => (D.lowFl B).garden)) =
    graftForest D.base.top (blockGraftTrees D.base.top D.base.partition (fun B => (D.base.low B).garden))
  congr 1
  funext j a
  unfold blockGraftTrees
  split_ifs with h
  · exact congrFun (D.lowFl_tree _) _
  · rfl

end FlowerGraftData

/-! ## Raw addresses in a graft -/

theorem graftLeaf_val {w : ℕ} (top : Fin w → TTree) (P : Finpartition (univ : Finset (GLeaf top)))
    (low : (B : P.parts) → Garden B.1.card) (x : GLeaf (graftForest top (blockGraftTrees top P low))) :
    x.1 = (((blockRootEquiv top P).symm ⟨(gardenLeafEquiv top P low x).1,
        (gardenLeafEquiv top P low x).2.1.1⟩).1.1,
      ((blockRootEquiv top P).symm ⟨(gardenLeafEquiv top P low x).1,
        (gardenLeafEquiv top P low x).2.1.1⟩).1.2 ++ (gardenLeafEquiv top P low x).2.1.2) := by
  have h := gardenLeafEquiv_symm_val top P low (gardenLeafEquiv top P low x).1 (gardenLeafEquiv top P low x).2
  simp only [Sigma.eta, Equiv.symm_apply_apply] at h
  exact h

theorem garden_mark_raw_of_eq {w : ℕ} {G H : Garden w} (he : G = H) (a : GLeaf G.tree) (b : GLeaf H.tree)
    (hab : a.1 = b.1) : G.mark a = H.mark b := by
  cases he
  exact congrArg G.mark (Subtype.ext hab)

/-- In a leaf tree, every leaf has the empty path. -/
theorem leaf_path_nil {n : ℕ} {tr : Fin n → TTree} (htr : tr = fun _ => TTree.leaf) (a : GLeaf tr) : a.1.2 = [] := by
  have h : a.1.2 ∈ (tr a.1.1).leaves := a.2
  rw [congrFun htr a.1.1] at h
  simpa [TTree.leaves] using h

namespace FlowerGraftData

variable {Pm p : ℕ} {ζ : ℤˣ} (D : FlowerGraftData Pm p ζ)

/-- The leaf equivalence of the flower graft. -/
noncomputable abbrev eFl :=
  gardenLeafEquiv D.base.top D.base.partition (fun B => (D.lowFl B).garden)

theorem isPairBlock_part (j : Fin (2 * Pm)) :
    D.IsPairBlock (blockRootEquiv D.base.top D.base.partition (D.flAt j)).1.1 := by
  rw [D.part_flAt j]
  exact ⟨j, rfl⟩

theorem lowFl_tree_leaf {B : D.base.partition.parts} (hB : D.IsPairBlock B.1) :
    (D.lowFl B).garden.tree = fun _ => TTree.leaf :=
  (D.lowFl_tree B).trans (D.tree_of_isPairBlock hB)

theorem nil_mem_lowFl_leaves {B : D.base.partition.parts} (hB : D.IsPairBlock B.1) (k : Fin B.1.card) :
    ([] : TTree.Path) ∈ ((D.lowFl B).garden.tree k).leaves := by
  rw [congrFun (D.lowFl_tree_leaf hB) k]
  simp [TTree.leaves]

theorem mem_base_leaves (B : D.base.partition.parts) (x : GLeaf (D.lowFl B).garden.tree) :
    x.1.2 ∈ ((D.base.low B).garden.tree x.1.1).leaves := by
  have h : x.1.2 ∈ ((D.lowFl B).garden.tree x.1.1).leaves := x.2
  rw [congrFun (D.lowFl_tree B) x.1.1] at h
  exact h

theorem mem_marked_leaves {B : D.base.partition.parts} (hB : D.IsPairBlock B.1) (x : GLeaf (D.lowFl B).garden.tree) :
    x.1.2 ∈ ((markedLeafLG B.1.card (D.base.low B).garden.sig p).garden.tree x.1.1).leaves := by
  have h : x.1.2 ∈ ((D.lowFl B).garden.tree x.1.1).leaves := x.2
  rw [congrFun (D.lowFl_tree_leaf hB) x.1.1] at h
  exact h

/-- The flower leaf of tree `j` in the flower graft. -/
noncomputable def flLeaf (j : Fin (2 * Pm)) : GLeaf D.flowerGraft.garden.tree :=
  (D.eFl).symm ⟨(blockRootEquiv D.base.top D.base.partition (D.flAt j)).1,
    ⟨((blockRootEquiv D.base.top D.base.partition (D.flAt j)).2, []),
      D.nil_mem_lowFl_leaves (D.isPairBlock_part j) _⟩⟩

theorem flLeaf_val (j : Fin (2 * Pm)) : (D.flLeaf j).1 = (j, D.fl j) := by
  have h := gardenLeafEquiv_symm_val D.base.top D.base.partition (fun B => (D.lowFl B).garden)
    (blockRootEquiv D.base.top D.base.partition (D.flAt j)).1
    ⟨((blockRootEquiv D.base.top D.base.partition (D.flAt j)).2, []),
      D.nil_mem_lowFl_leaves (D.isPairBlock_part j) _⟩
  simp only [Sigma.eta, Equiv.symm_apply_apply, List.append_nil] at h
  exact h

theorem flowerGraft_mark (x : GLeaf D.flowerGraft.garden.tree) :
    D.flowerGraft.garden.mark x = (D.lowFl (D.eFl x).1).garden.mark (D.eFl x).2 := rfl

theorem mark_ne_none_iff (x : GLeaf D.flowerGraft.garden.tree) :
    D.flowerGraft.garden.mark x ≠ none ↔ D.IsPairBlock (D.eFl x).1.1 := by
  rw [D.flowerGraft_mark]
  by_cases hB : D.IsPairBlock (D.eFl x).1.1
  · have h := garden_mark_raw_of_eq (congrArg LayeredGarden.garden (D.lowFl_of_pair hB)) (D.eFl x).2
      ⟨(D.eFl x).2.1, D.mem_marked_leaves hB (D.eFl x).2⟩ rfl
    rw [h]
    exact iff_of_true (by simp [markedLeafLG, markedLeafGarden]) hB
  · have h := garden_mark_raw_of_eq (congrArg LayeredGarden.garden (D.lowFl_of_not hB)) (D.eFl x).2
      ⟨(D.eFl x).2.1, D.mem_base_leaves _ (D.eFl x).2⟩ rfl
    rw [h]
    exact iff_of_false (fun h' => h' (D.base.plain _ _)) hB

theorem mark_flLeaf (j : Fin (2 * Pm)) : D.flowerGraft.garden.mark (D.flLeaf j) ≠ none := by
  rw [D.mark_ne_none_iff]
  unfold flLeaf
  rw [Equiv.apply_symm_apply]
  exact D.isPairBlock_part j

theorem mark_eq_equal_of_ne_none {x : GLeaf D.flowerGraft.garden.tree} (hx : D.flowerGraft.garden.mark x ≠ none) :
    D.flowerGraft.garden.mark x = some MarkTag.equal := by
  have hB := (D.mark_ne_none_iff x).mp hx
  rw [D.flowerGraft_mark]
  have h := garden_mark_raw_of_eq (congrArg LayeredGarden.garden (D.lowFl_of_pair hB)) (D.eFl x).2
    ⟨(D.eFl x).2.1, D.mem_marked_leaves hB (D.eFl x).2⟩ rfl
  rw [h]
  rfl

/-- A root in a pair block is one of its two flowers. -/
theorem root_of_isPairBlock {B : D.base.partition.parts} {j : Fin (2 * Pm)} (hj : B.1 = D.pairBlock j)
    (k : Fin B.1.card) :
    (blockRootEquiv D.base.top D.base.partition).symm ⟨B, k⟩ = D.flAt j ∨
      (blockRootEquiv D.base.top D.base.partition).symm ⟨B, k⟩ = D.flAt (partner j) := by
  have hm := blockRootEquiv_symm_mem D.base.top D.base.partition B k
  rw [hj] at hm
  simpa [pairBlock] using hm

/-- **The marked leaves of the flower graft are its flower leaves.** -/
theorem eq_flLeaf_of_marked {x : GLeaf D.flowerGraft.garden.tree} (hx : D.flowerGraft.garden.mark x ≠ none) :
    x = D.flLeaf x.1.1 := by
  have hB := (D.mark_ne_none_iff x).mp hx
  obtain ⟨j, hj⟩ := hB
  have hval := graftLeaf_val D.base.top D.base.partition (fun B => (D.lowFl B).garden) x
  have hnil := leaf_path_nil (D.lowFl_tree_leaf ⟨j, hj⟩) (D.eFl x).2
  have hroot := D.root_of_isPairBlock hj (D.eFl x).2.1.1
  apply Subtype.ext
  rw [D.flLeaf_val]
  change x.1 = (x.1.1, D.fl x.1.1)
  rw [hval]
  change (_, _ ++ (D.eFl x).2.1.2) = (_, D.fl (_, _ ++ (D.eFl x).2.1.2).1)
  rw [hnil, List.append_nil]
  rcases hroot with h | h
  · simp only [h]
    rfl
  · simp only [h]
    rfl

theorem flLeaf_injective : Function.Injective D.flLeaf := by
  intro i j h
  have h1 := congrArg (fun l : GLeaf D.flowerGraft.garden.tree => l.1.1) h
  simp only [D.flLeaf_val] at h1
  exact h1

/-- **The flower graft is a flower garden.** -/
theorem flowerGraft_isFlowerGarden : D.flowerGraft.garden.IsFlowerGarden := by
  refine ⟨fun j => ?_, fun ℓ hℓ => D.mark_eq_equal_of_ne_none hℓ, fun j => rfl⟩
  rw [card_eq_one]
  refine ⟨D.flLeaf j, ?_⟩
  ext ℓ
  simp only [mem_filter, mem_univ, true_and, mem_singleton]
  constructor
  · rintro ⟨hj, hm⟩
    rw [D.eq_flLeaf_of_marked hm, hj]
  · rintro rfl
    refine ⟨?_, D.mark_flLeaf j⟩
    rw [D.flLeaf_val]

theorem flowerGraft_flower_sign (ℓ : GLeaf D.flowerGraft.garden.tree) (hℓ : D.flowerGraft.garden.IsFlower ℓ) :
    D.flowerGraft.garden.sign ℓ.toNode = ζ * D.flowerGraft.garden.sig ℓ.1.1 := by
  have hm : D.flowerGraft.garden.mark ℓ ≠ none := by
    rw [hℓ]
    simp
  have he := D.eq_flLeaf_of_marked hm
  change nodeSign (altFlowerSig Pm) ℓ.1 = ζ * altFlowerSig Pm ℓ.1.1
  rw [he, D.flLeaf_val]
  exact D.fl_sign _

theorem flowerGraft_layer_flLeaf (j : Fin (2 * Pm)) : D.flowerGraft.layer (D.flLeaf j).toNode = p := by
  have hB := D.isPairBlock_part j
  let z := blockRootEquiv D.base.top D.base.partition (D.flAt j)
  let a : GLeaf (D.lowFl z.1).garden.tree := ⟨(z.2, []), D.nil_mem_lowFl_leaves hB z.2⟩
  have hn := gardenLeaf_toNode_lower D.base.top D.base.partition (fun B => (D.lowFl B).garden) z.1 a
  have hl := graftLayer_lower D.base.top D.base.partition D.lowFl p z.1 a.toNode
  have hr := layeredGarden_layer_raw_of_eq (D.lowFl_of_pair hB) a.toNode
    (GNode.root (markedLeafLG _ (D.base.low z.1).garden.sig p).garden.tree z.2) rfl
  change graftLayer D.base.top D.base.partition D.lowFl p
    ((gardenLeafEquiv D.base.top D.base.partition (fun B => (D.lowFl B).garden)).symm ⟨z.1, a⟩).toNode = p
  rw [hn, hl, hr]
  rfl

theorem flowerGraft_flower_layer (ℓ ℓ' : GLeaf D.flowerGraft.garden.tree) (hℓ : D.flowerGraft.garden.IsFlower ℓ)
    (hℓ' : D.flowerGraft.garden.IsFlower ℓ') : D.flowerGraft.layer ℓ.toNode = D.flowerGraft.layer ℓ'.toNode := by
  have hm : D.flowerGraft.garden.mark ℓ ≠ none := by rw [hℓ]; simp
  have hm' : D.flowerGraft.garden.mark ℓ' ≠ none := by rw [hℓ']; simp
  rw [D.eq_flLeaf_of_marked hm, D.eq_flLeaf_of_marked hm', D.flowerGraft_layer_flLeaf, D.flowerGraft_layer_flLeaf]

end FlowerGraftData

end WaveTurbulence.X2E
