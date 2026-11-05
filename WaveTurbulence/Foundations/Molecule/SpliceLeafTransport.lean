/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.SpliceLeafPieces
import Mathlib.Tactic

/-! # The actual bijection between spliced and retained old leaves
TARGET `block_clcn` (2). No pairing or molecule isomorphism is assumed.
-/

public section
namespace WaveTurbulence.Mole
open TTree Finset
variable {w : ℕ} {G : Garden w} {a : GBranch G.tree} (B : SpliceBoundaryRoots G a)

theorem splicePieceOld_injective : Function.Injective (splicePieceOld B) := by
  rintro (l | ⟨i,q⟩) (m | ⟨j,r⟩) he
  · apply congrArg Sum.inl
    exact Subtype.ext he
  · have hd : a.toNode.IsDesc (splicePieceOld B (.inr ⟨j,r⟩)).toNode :=
      ⟨(B.below j).1,(B.below j).2.trans ⟨r.1,rfl⟩⟩
    have he' := congrArg (fun l : GLeaf G.tree => l.toNode) he
    exact (l.2 (he'.symm ▸ hd)).elim
  · have hd : a.toNode.IsDesc (splicePieceOld B (.inr ⟨i,q⟩)).toNode :=
      ⟨(B.below i).1,(B.below i).2.trans ⟨q.1,rfl⟩⟩
    have he' := congrArg (fun l : GLeaf G.tree => l.toNode) he
    exact (m.2 (he' ▸ hd)).elim
  · have hij : i = j := by
      by_contra hn
      have h1 : (B.node i).IsDesc (splicePieceOld B (.inr ⟨i,q⟩)).toNode := ⟨rfl,⟨q.1,rfl⟩⟩
      have h2 : (B.node j).IsDesc (splicePieceOld B (.inr ⟨j,r⟩)).toNode := ⟨rfl,⟨r.1,rfl⟩⟩
      have he' := congrArg (fun l : GLeaf G.tree => l.toNode) he
      have h2' : (B.node j).IsDesc (splicePieceOld B (.inr ⟨i,q⟩)).toNode := he'.symm ▸ h2
      have hi : (B.node i).1.1 = (B.node j).1.1 := h1.1.trans h2'.1.symm
      rcases List.prefix_or_prefix_of_prefix h1.2 h2'.2 with hp | hp
      · exact (B.incomparable i j hn).1 ⟨hi,hp⟩
      · exact (B.incomparable i j hn).2 ⟨hi.symm,hp⟩
    subst j
    have hp : (B.node i).1.2++q.1 = (B.node i).1.2++r.1 :=
      congrArg (fun l : GLeaf G.tree => l.1.2) he
    have hqr : q = r := Subtype.ext (List.append_cancel_left hp)
    subst r
    rfl

theorem splicePieceNew_surjective : Function.Surjective (splicePieceNew B) := by
  intro l
  by_cases hi : l.1.1 = a.1.1
  · have hl : l.1.2 ∈ (spliceForest G a B.node a.1.1).leaves := hi ▸ l.2
    rw [spliceForest_leaves] at hl
    rcases mem_union.mp hl with hout | hin
    · obtain ⟨hold,hn⟩ := mem_filter.mp hout
      let k : GLeaf G.tree := ⟨l.1,hi.symm ▸ hold⟩
      have hk : ¬ a.toNode.IsDesc k.toNode := fun h => hn h.2
      exact ⟨.inl ⟨k,hk⟩,Subtype.ext rfl⟩
    · obtain ⟨p,hp,he⟩ := mem_image.mp hin
      cases p with
      | nil =>
        have hn : ([] : Path) ∉ (spliceCrown G B.node).leaves := by
          simp [spliceCrown,TTree.leaves,TTree.nil_notMem_pre]
        exact (hn hp).elim
      | cons i q =>
        have hq := (spliceCrown_child_leaf G B.node i q).mp hp
        exact ⟨.inr ⟨i,⟨q,hq⟩⟩,Subtype.ext (Prod.ext hi.symm he)⟩
  · have hl : l.1.2 ∈ (G.tree l.1.1).leaves := by
      have hm := l.2
      rw [spliceForest_other G a B.node _ hi] at hm
      exact hm
    let k : GLeaf G.tree := ⟨l.1,hl⟩
    have hk : ¬ a.toNode.IsDesc k.toNode := fun h => hi h.1.symm
    exact ⟨.inl ⟨k,hk⟩,Subtype.ext rfl⟩

theorem splicePieceOld_surjective_retained (l : GLeaf G.tree) (hl : IsSpliceRetainedLeaf B l) :
    ∃ p : SpliceLeafPiece B, splicePieceOld B p = l := by
  rcases hl with hout | ⟨i,hi,hp⟩
  · exact ⟨.inl ⟨l,hout⟩,rfl⟩
  · obtain ⟨q,hq⟩ := hp
    have hleaf : (B.node i).1.2++q ∈ (G.tree (B.node i).1.1).leaves := by
      rw [hq]
      exact hi.symm ▸ l.2
    have hqleaf := (Comb.subtree_leaves_iff (spliceNodeSubtree_spec G (B.node i)) q).mpr hleaf
    exact ⟨.inr ⟨i,⟨q,hqleaf⟩⟩,Subtype.ext (Prod.ext hi hq)⟩

/-- The actual leaf transport for this concrete forest surgery. -/
@[expose] noncomputable def spliceLeafEquiv :
    GLeaf (spliceForest G a B.node) ≃ {l : GLeaf G.tree // IsSpliceRetainedLeaf B l} :=
  (Equiv.ofBijective (splicePieceNew B) ⟨splicePieceNew_injective B,splicePieceNew_surjective B⟩).symm.trans
    (Equiv.ofBijective (fun p => ⟨splicePieceOld B p,splicePieceOld_retained B p⟩)
      ⟨fun p q he => splicePieceOld_injective B (congrArg Subtype.val he),by
        intro l
        obtain ⟨p,hp⟩ := splicePieceOld_surjective_retained B l.1 l.2
        exact ⟨p,Subtype.ext hp⟩⟩)

end WaveTurbulence.Mole
