/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.MkDefs.Intrinsic

/-! # B2b MK-MARK (a): owners of inflated addresses and near regions

The inflated attachment addresses `inflatedPosition S X a` of the skeleton nodes `a` (main,
`SkeletonDraft/ReconstructionPositions.lean`) reflect the ancestor order exactly
(`isDesc_iff_addrBelow`). Hence the own regions of `MkDefs.ownRegion` partition the addresses: every
address has exactly one owner (`existsUnique_mem_ownRegion`, `owner`). An address lies in the near region
of a skeleton branch `b` iff its owner is `b`, a child of `b`, or the leaf partner of a leaf child of `b`
(`mem_nearRegion_iff`); so it lies in the near regions of at most three branches (`card_nearBranches_le`):
its owner, the owner's parent, and the parent of the owner's leaf partner (`mem_nearRegion_cases`).
This is the first half of the proof of o75 Lemma 1⁺ (B0 SCOPE §2). -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical
open WaveTurbulence WaveTurbulence.Flower.MkDefs WaveTurbulence.Reg.Skeleton

namespace WaveTurbulence.Flower.MkMark

variable {w : ℕ}

/-! ## Nodes of a forest -/

section Nodes
variable {tree : Fin w → TTree}

/-- A non-root node is the child of its parent at the last step of its path. -/
theorem parent_child_self (a : GNode tree) (h : a.1.2 ≠ []) :
    (a.parent h).child (a.1.2.getLast h) = a := by
  apply Subtype.ext
  show ((a.1.1, a.1.2.dropLast ++ [a.1.2.getLast h]) : Fin w × TTree.Path) = a.1
  rw [List.dropLast_append_getLast h]

/-- A node with the empty path is the root of its tree. -/
theorem root_eq_of_path_nil (a : GNode tree) (h : a.1.2 = []) : GNode.root tree a.1.1 = a := by
  apply Subtype.ext
  show ((a.1.1, []) : Fin w × TTree.Path) = a.1
  rw [← h]

/-- Induction over the nodes of a forest: roots, then children of branches. -/
theorem node_induction {P : GNode tree → Prop} (hroot : ∀ j, P (GNode.root tree j))
    (hchild : ∀ (b : GBranch tree) (i : Fin 3), P b.toNode → P (b.child i)) (a : GNode tree) : P a := by
  induction hn : a.1.2.length generalizing a with
  | zero =>
    have h : a.1.2 = [] := List.length_eq_zero_iff.mp hn
    rw [← root_eq_of_path_nil a h]
    exact hroot _
  | succ n ih =>
    have h : a.1.2 ≠ [] := by
      intro h'
      rw [h'] at hn
      simp at hn
    rw [← parent_child_self a h]
    apply hchild
    apply ih
    show a.1.2.dropLast.length = n
    rw [List.length_dropLast, hn]
    rfl

/-- Two nodes with the same address are equal. -/
theorem gnode_eq_of_val {a a' : GNode tree} (h1 : a.1.1 = a'.1.1) (h2 : a.1.2 = a'.1.2) : a = a' :=
  Subtype.ext (Prod.ext h1 h2)

/-- `toNode` is injective. -/
theorem toNode_injective : Function.Injective (fun b : GBranch tree => b.toNode) := by
  intro b b' h
  apply Subtype.ext
  exact congrArg (fun x : GNode tree => x.1) h

/-- A leaf's `toNode` is injective. -/
theorem leaf_toNode_injective : Function.Injective (fun ℓ : GLeaf tree => ℓ.toNode) := by
  intro ℓ ℓ' h
  apply Subtype.ext
  exact congrArg (fun x : GNode tree => x.1) h

end Nodes

/-! ## Addresses below addresses -/

theorem addrBelow_refl (x : Address w) : AddrBelow x x := ⟨rfl, List.prefix_refl _⟩

theorem addrBelow_trans {x y z : Address w} (h : AddrBelow x y) (h' : AddrBelow y z) : AddrBelow x z :=
  ⟨h.1.trans h'.1, h.2.trans h'.2⟩

/-! ## Inflated positions reflect the ancestor order -/

section Inflated
variable (S : Garden w) (X : GBranch S.tree → RegChain)

/-- The inflated position stays in the node's tree. -/
theorem inflatedPosition_fst (a : GNode S.tree) : (inflatedPosition S X a).1 = a.1.1 := by
  induction a using node_induction with
  | hroot j =>
    rw [inflatedPosition_root]
    rfl
  | hchild b i ih =>
    rw [inflatedPosition_child]
    exact ih

/-- The path of a child's inflated position: the parent's, its lone path, then the child step. -/
theorem inflatedPosition_snd_child (b : GBranch S.tree) (i : Fin 3) :
    (inflatedPosition S X (b.child i)).2 = (inflatedPosition S X b.toNode).2 ++ ((X b).lonePath ++ [i]) := by
  rw [inflatedPosition_child]
  rfl

/-- Monotonicity: a descendant's inflated position lies below the ancestor's. -/
theorem addrBelow_inflatedPosition {a a' : GNode S.tree} (h : a.IsDesc a') :
    AddrBelow (inflatedPosition S X a) (inflatedPosition S X a') := by
  induction a' using node_induction with
  | hroot j =>
    have h2 : a.1.2 = [] := List.prefix_nil.mp h.2
    have ha : a = GNode.root S.tree j := gnode_eq_of_val h.1 h2
    subst ha
    exact addrBelow_refl _
  | hchild b i ih =>
    rcases List.prefix_concat_iff.mp h.2 with h' | h'
    · have ha : a = b.child i := gnode_eq_of_val h.1 h'
      subst ha
      exact addrBelow_refl _
    · have hb := ih ⟨h.1, h'⟩
      refine addrBelow_trans hb ⟨?_, ?_⟩
      · rw [inflatedPosition_fst, inflatedPosition_fst]
        rfl
      · rw [inflatedPosition_snd_child]
        exact List.prefix_append _ _

/-- Reflection: if a node's inflated position lies below another's, the node is an ancestor. -/
theorem isDesc_of_addrBelow {a a' : GNode S.tree}
    (h : AddrBelow (inflatedPosition S X a) (inflatedPosition S X a')) : a.IsDesc a' := by
  induction a using node_induction generalizing a' with
  | hroot j =>
    refine ⟨?_, List.nil_prefix⟩
    have h1 := h.1
    rw [inflatedPosition_fst, inflatedPosition_fst] at h1
    exact h1
  | hchild c k ih =>
    have h1 : AddrBelow (inflatedPosition S X c.toNode) (inflatedPosition S X a') := by
      refine ⟨?_, ?_⟩
      · rw [inflatedPosition_fst, inflatedPosition_fst]
        have h0 := h.1
        rw [inflatedPosition_fst, inflatedPosition_fst] at h0
        exact h0
      · have h0 := h.2
        rw [inflatedPosition_snd_child] at h0
        exact (List.prefix_append _ _).trans h0
    have hc := ih h1
    obtain ⟨rest, hrest⟩ := hc.2
    cases rest with
    | nil =>
      exfalso
      have ha' : a' = c.toNode := gnode_eq_of_val hc.1.symm (by simpa using hrest.symm)
      subst ha'
      have hl := h.2.length_le
      rw [inflatedPosition_snd_child] at hl
      simp at hl
    | cons m rest' =>
      have hm : (c.child m).IsDesc a' := by
        refine ⟨hc.1, ⟨rest', ?_⟩⟩
        show c.1.2 ++ [m] ++ rest' = a'.1.2
        rw [← hrest]
        simp only [List.append_assoc, List.singleton_append]
        rfl
      have h2 := addrBelow_inflatedPosition S X hm
      have hlen : (inflatedPosition S X (c.child k)).2.length =
          (inflatedPosition S X (c.child m)).2.length := by
        rw [inflatedPosition_snd_child, inflatedPosition_snd_child]
        simp
      have e : (inflatedPosition S X (c.child k)).2 = (inflatedPosition S X (c.child m)).2 :=
        (List.prefix_of_prefix_length_le h.2 h2.2 hlen.le).eq_of_length hlen
      rw [inflatedPosition_snd_child, inflatedPosition_snd_child] at e
      have hkm : k = m := by simpa using e
      subst hkm
      exact hm

/-! ## Own regions partition the addresses -/

/-- Every address has an owner: the deepest skeleton node whose inflated position lies above it. -/
theorem exists_mem_ownRegion (y : Address w) : ∃ a, y ∈ ownRegion S X a := by
  let C : Finset (GNode S.tree) := Finset.univ.filter fun a => AddrBelow (inflatedPosition S X a) y
  have hne : C.Nonempty := by
    refine ⟨GNode.root S.tree y.1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
    rw [inflatedPosition_root]
    exact ⟨rfl, List.nil_prefix⟩
  obtain ⟨a, haC, hmax⟩ := C.exists_max_image (fun a => a.1.2.length) hne
  refine ⟨a, (Finset.mem_filter.mp haC).2, fun c hac hca hc => ?_⟩
  have hle := hmax c (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hc⟩)
  have hlen : a.1.2.length < c.1.2.length := by
    rcases lt_or_eq_of_le hac.2.length_le with h | h
    · exact h
    · exact absurd (gnode_eq_of_val hac.1.symm (hac.2.eq_of_length h).symm) hca
  omega

/-- Owners are unique. -/
theorem eq_of_mem_ownRegion {y : Address w} {a a' : GNode S.tree} (h : y ∈ ownRegion S X a)
    (h' : y ∈ ownRegion S X a') : a = a' := by
  have key : ∀ {a a' : GNode S.tree}, y ∈ ownRegion S X a → y ∈ ownRegion S X a' →
      (inflatedPosition S X a).2.length ≤ (inflatedPosition S X a').2.length → a = a' := by
    intro a a' h h' hle
    have hpre := List.prefix_of_prefix_length_le h.1.2 h'.1.2 hle
    have hd : a.IsDesc a' := isDesc_of_addrBelow S X ⟨h.1.1.trans h'.1.1.symm, hpre⟩
    by_contra hne
    exact h.2 a' hd (Ne.symm hne) h'.1
  rcases le_total (inflatedPosition S X a).2.length (inflatedPosition S X a').2.length with hle | hle
  · exact key h h' hle
  · exact (key h' h hle).symm

/-- The owner of an address: the unique skeleton node whose own region contains it. -/
def owner (y : Address w) : GNode S.tree := (exists_mem_ownRegion S X y).choose

theorem mem_ownRegion_owner (y : Address w) : y ∈ ownRegion S X (owner S X y) :=
  (exists_mem_ownRegion S X y).choose_spec

theorem mem_ownRegion_iff {y : Address w} {a : GNode S.tree} : y ∈ ownRegion S X a ↔ owner S X y = a :=
  ⟨fun h => eq_of_mem_ownRegion S X (mem_ownRegion_owner S X y) h,
    fun h => h ▸ mem_ownRegion_owner S X y⟩

/-! ## Near regions -/

/-- An address lies in the near region of `b` iff its owner is `b`, a child of `b`, or the partner of a leaf
child of `b`. -/
theorem mem_nearRegion_iff {y : Address w} {b : GBranch S.tree} :
    y ∈ nearRegion S X b ↔ owner S X y = b.toNode ∨ (∃ i, owner S X y = b.child i) ∨
      ∃ ℓ : GLeaf S.tree, b.IsParentOf ℓ ∧ owner S X y = (S.pair ℓ).toNode := by
  simp only [nearRegion, Set.mem_union, Set.mem_iUnion, mem_ownRegion_iff, exists_prop]
  tauto

/-- The branches whose near region contains the address `y`. -/
def nearBranches (y : Address w) : Finset (GBranch S.tree) :=
  Finset.univ.filter fun b => y ∈ nearRegion S X b

theorem mem_nearBranches {y : Address w} {b : GBranch S.tree} : b ∈ nearBranches S X y ↔ y ∈ nearRegion S X b := by
  simp [nearBranches]

/-- **An address lies in the near region of at most three branches.** -/
theorem card_nearBranches_le (y : Address w) : (nearBranches S X y).card ≤ 3 := by
  set o := owner S X y
  let B1 : Finset (GBranch S.tree) := Finset.univ.filter fun b => o = b.toNode
  let B2 : Finset (GBranch S.tree) := Finset.univ.filter fun b => ∃ i, o = b.child i
  let B3 : Finset (GBranch S.tree) := Finset.univ.filter fun b =>
    ∃ ℓ : GLeaf S.tree, b.IsParentOf ℓ ∧ o = (S.pair ℓ).toNode
  have hsub : nearBranches S X y ⊆ B1 ∪ B2 ∪ B3 := by
    intro b hb
    rcases (mem_nearRegion_iff S X).mp ((mem_nearBranches S X).mp hb) with h | h | h
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩))
    · exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩))
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
  have h1 : B1.card ≤ 1 := by
    refine Finset.card_le_one.mpr fun b hb b' hb' => ?_
    have e1 := (Finset.mem_filter.mp hb).2
    have e2 := (Finset.mem_filter.mp hb').2
    exact toNode_injective (e1.symm.trans e2)
  have parent_eq : ∀ (b b' : GBranch S.tree) (x : Fin w × TTree.Path) (i i' : Fin 3),
      x = (b.1.1, b.1.2 ++ [i]) → x = (b'.1.1, b'.1.2 ++ [i']) → b = b' := by
    intro b b' x i i' e e'
    have e2 := e.symm.trans e'
    simp only [Prod.mk.injEq] at e2
    obtain ⟨ea, eb⟩ := e2
    have hl : b.1.2 = b'.1.2 := (List.append_inj' eb rfl).1
    exact Subtype.ext (Prod.ext ea hl)
  have h2 : B2.card ≤ 1 := by
    refine Finset.card_le_one.mpr fun b hb b' hb' => ?_
    obtain ⟨i, e1⟩ := (Finset.mem_filter.mp hb).2
    obtain ⟨i', e2⟩ := (Finset.mem_filter.mp hb').2
    exact parent_eq b b' o.1 i i' (congrArg Subtype.val e1) (congrArg Subtype.val e2)
  have h3 : B3.card ≤ 1 := by
    refine Finset.card_le_one.mpr fun b hb b' hb' => ?_
    obtain ⟨ℓ, ⟨hℓ1, i, hℓ2⟩, e1⟩ := (Finset.mem_filter.mp hb).2
    obtain ⟨ℓ', ⟨hℓ1', i', hℓ2'⟩, e2⟩ := (Finset.mem_filter.mp hb').2
    have hp : S.pair ℓ = S.pair ℓ' := leaf_toNode_injective (e1.symm.trans e2)
    have hll : ℓ = ℓ' := by rw [← S.pair_pair ℓ, hp, S.pair_pair]
    subst hll
    exact parent_eq b b' ℓ.1 i i' (Prod.ext hℓ1 hℓ2) (Prod.ext hℓ1' hℓ2')
  calc (nearBranches S X y).card ≤ (B1 ∪ B2 ∪ B3).card := Finset.card_le_card hsub
    _ ≤ (B1 ∪ B2).card + B3.card := Finset.card_union_le _ _
    _ ≤ B1.card + B2.card + B3.card := by
        have := Finset.card_union_le B1 B2
        omega
    _ ≤ 3 := by omega

end Inflated

end WaveTurbulence.Flower.MkMark
