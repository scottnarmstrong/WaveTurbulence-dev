/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Flower.MkSlots.IntRest
public import WaveTurbulence.Foundations.Flower.MkSlots.IntGeo
public import WaveTurbulence.Foundations.Molecule.LeafInsertion

/-! # B3s MK-SLOTS (integration, R-core 1): which core branches are capped flower parents

On the reconstruction `LG = layeredReconstruction D hS layer hLayer` of a skeleton `S` whose cap trees `J` are single
leaves, the core branch of a skeleton branch `b` is a capped flower parent iff a child of `b` is a skeleton leaf `σ`
off the cap trees, paired with a cap root, whose attached node is a leaf of the reconstruction, i.e. whose native
couple is trivial on `σ`'s side (`cfp_core_iff`). The attached node of `σ` is the root of the native couple of
`pairOfLeaf σ` on `σ`'s side (`root_sideOf`), so the last condition is the shape of the native couple there
(`attLeaf_iff`): it is read on the native couple layered garden alone. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical
open WaveTurbulence WaveTurbulence.LGSpine Finset TTree
open WaveTurbulence.Reg WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed
open WaveTurbulence.Flower.MkDefs

namespace WaveTurbulence.Flower.MkSlots.IntCore

open WaveTurbulence.Flower.MkSlots.IntRest

variable {w : ℕ} {S : Garden w} (D : ReconstructionData S) (hS : S.IsPlain)

/-- The attached node of the skeleton leaf `σ` is a leaf of the reconstruction. -/
def AttLeaf (σ : GLeaf S.tree) : Prop :=
  ∃ ℓ : GLeaf (D.forest hS), ℓ.toNode = attachedNode D hS σ.toNode

/-- A leaf of the reconstruction whose partner is a root of a native couple lies in that native couple. -/
theorem slotOf_of_pair_root (ℓ : GLeaf (D.forest hS)) (q : SourcePair S) (i : Fin 2)
    (h : ((D.garden hS).pair ℓ).toNode = (nativeCoupleForest D hS q).root i) :
    slotOf D hS ℓ.toNode = Sum.inl q := by
  have hmem : (D.garden hS).pair ℓ ∈
      Comb.RootedSubforest.leafSet (G := D.garden hS) (nativeCoupleForest D hS q) := by
    refine (Comb.RootedSubforest.mem_leafSet_iff (G := D.garden hS) (nativeCoupleForest D hS q) _).mpr ⟨i, ?_⟩
    rw [← h]
    exact ⟨rfl, List.prefix_refl _⟩
  have hcl := (nativeCoupleForest_closed D hS q _ hmem).2
  rw [(D.garden hS).pair_pair ℓ] at hcl
  obtain ⟨ℓ', -, he⟩ := Finset.mem_image.mp hcl
  have hn : nativeNodeAt D hS (.inl q) ℓ'.toNode = ℓ.toNode := by
    rw [← he]
    exact (subforest_leaf_node _ ℓ').symm
  rw [← hn]
  exact slotOf_nativeNodeAt D hS _ _

/-- The attached node of a skeleton branch is not a leaf of the reconstruction: it is an ancestor of its core. -/
theorem attached_branch_ne_leaf (b : GBranch S.tree) (ℓ : GLeaf (D.forest hS)) :
    ℓ.toNode ≠ attachedNode D hS b.toNode := by
  intro h
  have hv : ℓ.1 = inflatedPosition S D.tree b.toNode := congrArg Subtype.val h
  have hc := (D.coreBranch hS b).2
  have hcv : (D.coreBranch hS b).1 = (ℓ.1.1, ℓ.1.2 ++ (D.tree b).lonePath) := by
    show D.corePosition b = _
    rw [hv]
    rfl
  rw [hcv] at hc
  exact Twist.leaf_not_prefix_branch ℓ.2 hc ⟨(D.tree b).lonePath, rfl⟩

/-- A root of a rooted subforest is a leaf iff the shape there is a single leaf. -/
theorem root_isLeaf_iff {v : ℕ} {tree : Fin w → TTree} (E : Comb.RootedSubforest tree v) (i : Fin v) :
    (∃ ℓ : GLeaf tree, ℓ.toNode = E.root i) ↔ E.shape i = TTree.leaf := by
  have hs := E.subtree_eq i
  constructor
  · rintro ⟨ℓ, hℓ⟩
    have h1 : (E.root i).1.2 ++ [] ∈ (tree (E.root i).1.1).leaves := by
      rw [List.append_nil, ← hℓ]
      exact ℓ.2
    have h2 := (Comb.subtree_leaves_iff hs []).mpr h1
    cases hsh : E.shape i with
    | leaf => rfl
    | node l m r =>
      rw [hsh] at h2
      simp [TTree.leaves, TTree.nil_notMem_pre] at h2
  · intro hsh
    have h2 : ([] : Path) ∈ (E.shape i).leaves := by
      rw [hsh]
      simp [TTree.leaves]
    have h1 := (Comb.subtree_leaves_iff hs []).mp h2
    rw [List.append_nil] at h1
    exact ⟨⟨(E.root i).1, h1⟩, rfl⟩

/-- The side of a skeleton leaf in the native couple of its pair. -/
def sideOf (σ : GLeaf S.tree) : Fin 2 :=
  if (pairOfLeaf S hS σ).firstLeaf hS = σ then 0 else 1

/-- The root of the native couple of `pairOfLeaf σ` on `σ`'s side is the attached node of `σ`. -/
theorem root_sideOf (σ : GLeaf S.tree) :
    (nativeCoupleForest D hS (pairOfLeaf S hS σ)).root (sideOf hS σ) = attachedNode D hS σ.toNode := by
  unfold sideOf
  split_ifs with h
  · show attachedNode D hS ((pairOfLeaf S hS σ).firstLeaf hS).toNode = _
    rw [h]
  · show attachedNode D hS ((pairOfLeaf S hS σ).secondLeaf hS).toNode = _
    rcases pairOfLeaf_sides hS σ with ⟨e1, -⟩ | ⟨-, e2⟩
    · exact absurd e1 h
    · rw [e2]

/-- **The attached node of `σ` is a leaf iff the native couple of its pair is a single leaf on `σ`'s side.** -/
theorem attLeaf_iff (σ : GLeaf S.tree) :
    AttLeaf D hS σ ↔ (decodedCouple (D.couple (pairOfLeaf S hS σ))).tree (sideOf hS σ) = TTree.leaf := by
  unfold AttLeaf
  rw [← root_sideOf D hS σ]
  exact root_isLeaf_iff (nativeCoupleForest D hS (pairOfLeaf S hS σ)) (sideOf hS σ)

/-- A skeleton leaf in a tree whose reconstruction is a single leaf has the empty path. -/
theorem skel_path_nil {j : Fin w} (hj : D.forest hS j = TTree.leaf) (σ : GLeaf S.tree) (hσ : σ.1.1 = j) :
    σ.1.2 = [] := by
  have hroot := IntGeo.root_mem_leaves (D := D) (hS := hS) hj
  have hl : S.tree j = TTree.leaf := by
    cases ht : S.tree j with
    | leaf => rfl
    | node l m r =>
      rw [ht] at hroot
      simp [TTree.leaves, TTree.nil_notMem_pre] at hroot
  have h := σ.2
  rw [hσ, hl] at h
  simpa [TTree.leaves] using h

/-- The two skeleton leaves of a pair: equal pairs have the same two leaves. -/
theorem mem_sides_of_pair_eq {σ τ : GLeaf S.tree} (h : pairOfLeaf S hS σ = pairOfLeaf S hS τ) :
    τ = σ ∨ τ = S.pair σ := by
  rcases pairOfLeaf_sides hS σ with ⟨e1, e2⟩ | ⟨e1, e2⟩ <;>
    rcases pairOfLeaf_sides hS τ with ⟨f1, f2⟩ | ⟨f1, f2⟩ <;> rw [h] at e1 e2
  · exact Or.inl (f1.symm.trans e1)
  · exact Or.inr (f2.symm.trans e2)
  · exact Or.inr (f1.symm.trans e1)
  · exact Or.inl (f2.symm.trans e2)

variable (layer : GNode (D.forest hS) → ℕ) (hLayer : IsLayering (D.garden hS) layer)

/-- **A capped flower child of a core**: it is the attached node of a skeleton leaf child `σ` of the skeleton branch,
and its partner lies in the tree of the skeleton partner of `σ`. -/
theorem flowerChild_data (J : Finset (Fin w)) (hcap : ∀ j ∈ J, (D.garden hS).tree j = TTree.leaf)
    (b : GBranch S.tree) (i : Fin 3) (ℓ : GLeaf (D.forest hS))
    (hfl : IsCapFlower (layeredReconstruction D hS layer hLayer) J ℓ)
    (hℓc : ℓ.toNode = (D.coreBranch hS b).child i) :
    ∃ σ : GLeaf S.tree, σ.toNode = b.child i ∧ ℓ.toNode = attachedNode D hS σ.toNode ∧ σ.1.1 ∉ J ∧
      ((D.garden hS).pair ℓ).1.1 = (S.pair σ).1.1 := by
  obtain ⟨hℓJ, hpJ⟩ := hfl
  rw [← attachedNode_child] at hℓc
  rcases (Comb.TreePath.mem_nodes_iff _ _).mp (b.child i).2 with hl | hbr
  · let σ : GLeaf S.tree := ⟨(b.child i).1, hl⟩
    have hσ : σ.toNode = b.child i := rfl
    have hℓσ : ℓ.toNode = attachedNode D hS σ.toNode := by rw [hσ]; exact hℓc
    have hidx : ℓ.1.1 = σ.1.1 := by
      have h := congrArg (fun z : GNode (D.forest hS) => z.1.1) hℓσ
      exact h.trans (inflatedPosition_index S D.tree σ.toNode)
    refine ⟨σ, hσ, hℓσ, by rw [← hidx]; exact hℓJ, ?_⟩
    -- the partner of `ℓ` is the root of the cap tree `j`
    set j := ((layeredReconstruction D hS layer hLayer).garden.pair ℓ).1.1 with hjdef
    have hj : D.forest hS j = TTree.leaf := hcap j hpJ
    let σj : GLeaf S.tree := ⟨(j, []), IntGeo.root_mem_leaves hj⟩
    have hσj : attachedNode D hS σj.toNode = GNode.root (D.forest hS) j := attachedNode_root D hS j
    have hpr : ((D.garden hS).pair ℓ).toNode = attachedNode D hS σj.toNode := by
      rw [hσj]
      exact Subtype.ext (Prod.ext rfl (IntGeo.path_eq_nil_of_leafTree hj _ rfl))
    have h1 : slotOf D hS ℓ.toNode = Sum.inl (pairOfLeaf S hS σj) :=
      slotOf_of_pair_root D hS ℓ _ (sideOf hS σj) (hpr.trans (root_sideOf D hS σj).symm)
    have h2 : slotOf D hS ℓ.toNode = Sum.inl (pairOfLeaf S hS σ) := by
      rw [hℓσ]; exact slotOf_attached_leaf D hS σ
    have hq : pairOfLeaf S hS σ = pairOfLeaf S hS σj := Sum.inl_injective (h2.symm.trans h1)
    rcases mem_sides_of_pair_eq hS hq with he | he
    · exfalso
      have : σ.1.1 = j := (congrArg (fun τ : GLeaf S.tree => τ.1.1) he).symm
      rw [← hidx] at this
      exact hℓJ (this ▸ hpJ)
    · exact congrArg (fun τ : GLeaf S.tree => τ.1.1) he
  · exfalso
    exact attached_branch_ne_leaf D hS ⟨(b.child i).1, hbr⟩ ℓ hℓc

/-- (⇒) of `cfp_core_iff`. -/
theorem cfp_core_forward (J : Finset (Fin w)) (hcap : ∀ j ∈ J, (D.garden hS).tree j = TTree.leaf)
    (b : GBranch S.tree) (hb : IsCapFlowerParent (layeredReconstruction D hS layer hLayer) J (D.coreBranch hS b)) :
    ∃ (i : Fin 3) (σ : GLeaf S.tree), σ.toNode = b.child i ∧ σ.1.1 ∉ J ∧ (S.pair σ).1.1 ∈ J ∧ AttLeaf D hS σ := by
  obtain ⟨ℓ, hfl, hpar1, i, hpar2⟩ := hb
  have hℓc : ℓ.toNode = (D.coreBranch hS b).child i := Subtype.ext (Prod.ext hpar1 hpar2)
  obtain ⟨σ, hσ, hℓσ, hσJ, hp⟩ := flowerChild_data D hS layer hLayer J hcap b i ℓ hfl hℓc
  exact ⟨i, σ, hσ, hσJ, hp ▸ hfl.2, ⟨ℓ, hℓσ⟩⟩

/-- (⇐) of `cfp_core_iff`. -/
theorem cfp_core_backward (J : Finset (Fin w)) (hcap : ∀ j ∈ J, (D.garden hS).tree j = TTree.leaf)
    (b : GBranch S.tree) (i : Fin 3) (σ : GLeaf S.tree) (hσ : σ.toNode = b.child i) (hσJ : σ.1.1 ∉ J)
    (hpJ : (S.pair σ).1.1 ∈ J) (hatt : AttLeaf D hS σ) :
    IsCapFlowerParent (layeredReconstruction D hS layer hLayer) J (D.coreBranch hS b) := by
  obtain ⟨ℓ, hℓ⟩ := hatt
  have hℓc : ℓ.toNode = (D.coreBranch hS b).child i := by
    rw [hℓ, hσ]; exact attachedNode_child D hS b i
  have hv := congrArg Subtype.val hℓc
  have hidx : ℓ.1.1 = σ.1.1 := by
    have h := congrArg (fun z : GNode (D.forest hS) => z.1.1) hℓ
    exact h.trans (inflatedPosition_index S D.tree σ.toNode)
  have hv1 : ℓ.1.1 = (D.coreBranch hS b).1.1 := by have h := congrArg Prod.fst hv; exact h
  have hv2 : ℓ.1.2 = (D.coreBranch hS b).1.2 ++ [i] := by have h := congrArg Prod.snd hv; exact h
  refine ⟨ℓ, ⟨by rw [hidx]; exact hσJ, ?_⟩, hv1, i, hv2⟩
  -- the partner of `ℓ` is the root of the cap tree of `S.pair σ`
  set j := (S.pair σ).1.1 with hjdef
  have hj : D.forest hS j = TTree.leaf := hcap j hpJ
  have hσ'nil : (S.pair σ).1.2 = [] := skel_path_nil D hS hj (S.pair σ) rfl
  have hroot' : attachedNode D hS (S.pair σ).toNode = GNode.root (D.forest hS) j := by
    have he : (S.pair σ).toNode = GNode.root S.tree j := Subtype.ext (Prod.ext rfl hσ'nil)
    rw [he]; exact attachedNode_root D hS j
  let q := pairOfLeaf S hS σ
  let E := nativeCoupleForest D hS q
  -- both roots of the native couple are leaves
  have hsides : ∀ c : Fin 2, E.root c = attachedNode D hS σ.toNode ∨ E.root c = GNode.root (D.forest hS) j := by
    intro c
    rcases nativeRoot_cases D hS σ c with h | h
    · exact Or.inl h
    · exact Or.inr (h.trans hroot')
  have hrootleaf : ∀ c : Fin 2, E.shape c = TTree.leaf := by
    intro c
    refine (root_isLeaf_iff E c).mp ?_
    rcases hsides c with h | h
    · exact ⟨ℓ, hℓ.trans h.symm⟩
    · exact ⟨⟨(j, []), by
        show [] ∈ (D.forest hS j).leaves
        rw [hj]; simp [TTree.leaves]⟩, h.symm⟩
  -- `ℓ` is in the leaf set of the native couple, so is its partner
  have hmem : ℓ ∈ Comb.RootedSubforest.leafSet (G := D.garden hS) E := by
    refine (Comb.RootedSubforest.mem_leafSet_iff (G := D.garden hS) E ℓ).mpr ⟨sideOf hS σ, ?_⟩
    rw [root_sideOf D hS σ, ← hℓ]
    exact ⟨rfl, List.prefix_refl _⟩
  obtain ⟨hne, hpm⟩ := nativeCoupleForest_closed D hS q ℓ hmem
  obtain ⟨ℓ'', -, he⟩ := Finset.mem_image.mp hpm
  -- every leaf of the couple is a root
  have hpath : ℓ''.1.2 = [] := by
    have h := ℓ''.2
    rw [hrootleaf ℓ''.1.1] at h
    simpa [TTree.leaves] using h
  have hpn : ((D.garden hS).pair ℓ).toNode = E.root ℓ''.1.1 := by
    rw [← he]
    apply Subtype.ext
    show ((E.root ℓ''.1.1).1.1, (E.root ℓ''.1.1).1.2 ++ ℓ''.1.2) = (E.root ℓ''.1.1).1
    rw [hpath, List.append_nil]
  rcases hsides ℓ''.1.1 with h | h
  · exfalso
    apply hne
    apply Subtype.ext
    have := congrArg Subtype.val (hpn.trans (h.trans hℓ.symm))
    exact this
  · have := congrArg (fun z : GNode (D.forest hS) => z.1.1) (hpn.trans h)
    show ((D.garden hS).pair ℓ).1.1 ∈ J
    rw [show ((D.garden hS).pair ℓ).1.1 = j from this]
    exact hpJ

/-- **Which core branches are capped flower parents.** -/
theorem cfp_core_iff (J : Finset (Fin w)) (hcap : ∀ j ∈ J, (D.garden hS).tree j = TTree.leaf) (b : GBranch S.tree) :
    IsCapFlowerParent (layeredReconstruction D hS layer hLayer) J (D.coreBranch hS b) ↔
      ∃ (i : Fin 3) (σ : GLeaf S.tree), σ.toNode = b.child i ∧ σ.1.1 ∉ J ∧ (S.pair σ).1.1 ∈ J ∧
        AttLeaf D hS σ := by
  constructor
  · exact cfp_core_forward D hS layer hLayer J hcap b
  · rintro ⟨i, σ, hσ, hσJ, hpJ, hatt⟩
    exact cfp_core_backward D hS layer hLayer J hcap b i σ hσ hσJ hpJ hatt

/-- **A child of a core capped flower parent is the capped flower iff it is attached at a leaf paired with a cap
root** (a second such child would carry a second capped flower in the same tree). -/
theorem isCoreFlowerChild_iff {p : ℕ} (J : Finset (Fin w))
    (hG : CapGeo (layeredReconstruction D hS layer hLayer) J p) (b : GBranch S.tree)
    (hb : IsCapFlowerParent (layeredReconstruction D hS layer hLayer) J (D.coreBranch hS b)) (i : Fin 3) :
    IsCoreFlowerChild D hS layer hLayer J b i ↔ ∃ σ : GLeaf S.tree, σ.toNode = b.child i ∧ (S.pair σ).1.1 ∈ J := by
  constructor
  · rintro ⟨ℓ, hfl, hℓ⟩
    obtain ⟨σ, hσ, -, -, hp⟩ := flowerChild_data D hS layer hLayer J hG.cap_leaf b i ℓ hfl hℓ
    exact ⟨σ, hσ, hp ▸ hfl.2⟩
  · rintro ⟨σ, hσ, hpJ⟩
    by_contra hfl
    apply not_inCapNative_child D hS layer hLayer J hG b hb i hfl
    refine ⟨pairOfLeaf S hS σ, ?_, ?_⟩
    · rw [← attachedNode_child, ← hσ]
      exact slotOf_attached_leaf D hS σ
    · unfold IsCapPair
      rcases pairOfLeaf_sides hS σ with ⟨-, e2⟩ | ⟨e1, -⟩
      · rw [e2]; exact Or.inr hpJ
      · rw [e1]; exact Or.inl hpJ

/-- The momentum of the capped flower child in `restChildMom`: the cap root label of the tree of the skeleton
partner. -/
theorem restChildMom_flower {d p : ℕ} (J : Finset (Fin w))
    (hG : CapGeo (layeredReconstruction D hS layer hLayer) J p) (L : ℝ) (roots : Fin w → (Fin d → ℤ))
    (cc : Fin w → Fin 3 → Mom d) (b : GBranch S.tree) (i : Fin 3) (σ : GLeaf S.tree) (hσ : σ.toNode = b.child i)
    (h : IsCoreFlowerChild D hS layer hLayer J b i) :
    restChildMom D hS layer hLayer L J roots cc b i = latticePoint L (roots (S.pair σ).1.1) := by
  unfold restChildMom
  rw [dif_pos h]
  obtain ⟨σ', hσ', -, -, hp⟩ := flowerChild_data D hS layer hLayer J hG.cap_leaf b i h.choose h.choose_spec.1
    h.choose_spec.2
  have he : σ' = σ := Mole.leaf_toNode_injective (hσ'.trans hσ.symm)
  subst he
  rw [← hp]
  rfl

/-- The momentum of a non-flower child in `restChildMom`. -/
theorem restChildMom_other {d : ℕ} (J : Finset (Fin w)) (L : ℝ) (roots : Fin w → (Fin d → ℤ))
    (cc : Fin w → Fin 3 → Mom d) (b : GBranch S.tree) (i : Fin 3)
    (h : ¬ IsCoreFlowerChild D hS layer hLayer J b i) :
    restChildMom D hS layer hLayer L J roots cc b i = cc b.1.1 i := by
  unfold restChildMom
  rw [dif_neg h]

end WaveTurbulence.Flower.MkSlots.IntCore
