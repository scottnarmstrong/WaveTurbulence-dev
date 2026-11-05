/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.SpliceBranchPieces
import Mathlib.Tactic

/-! # Retained old branch transport is injective and onto
TARGET `block_clcn` (2). The removed crown is treated separately.
-/

public section
namespace WaveTurbulence.Mole
open TTree Finset
variable {w : ℕ} {G : Garden w} {a : GBranch G.tree} (B : SpliceBoundaryRoots G a)

theorem spliceBranchPieceOld_injective : Function.Injective (spliceBranchPieceOld B) := by
  rintro (l | ⟨i,q⟩) (m | ⟨j,r⟩) he
  · apply congrArg Sum.inl
    exact Subtype.ext he
  · have hd : a.toNode.IsDesc (spliceBranchPieceOld B (.inr ⟨j,r⟩)).toNode :=
      ⟨(B.below j).1,(B.below j).2.trans ⟨r.1,rfl⟩⟩
    have he' := congrArg (fun l : GBranch G.tree => l.toNode) he
    exact (l.2 (he'.symm ▸ hd)).elim
  · have hd : a.toNode.IsDesc (spliceBranchPieceOld B (.inr ⟨i,q⟩)).toNode :=
      ⟨(B.below i).1,(B.below i).2.trans ⟨q.1,rfl⟩⟩
    have he' := congrArg (fun l : GBranch G.tree => l.toNode) he
    exact (m.2 (he' ▸ hd)).elim
  · have hij : i = j := by
      by_contra hn
      have h1 : (B.node i).IsDesc (spliceBranchPieceOld B (.inr ⟨i,q⟩)).toNode := ⟨rfl,⟨q.1,rfl⟩⟩
      have h2 : (B.node j).IsDesc (spliceBranchPieceOld B (.inr ⟨j,r⟩)).toNode := ⟨rfl,⟨r.1,rfl⟩⟩
      have he' := congrArg (fun l : GBranch G.tree => l.toNode) he
      have h2' : (B.node j).IsDesc (spliceBranchPieceOld B (.inr ⟨i,q⟩)).toNode := he'.symm ▸ h2
      have hi : (B.node i).1.1 = (B.node j).1.1 := h1.1.trans h2'.1.symm
      rcases List.prefix_or_prefix_of_prefix h1.2 h2'.2 with hp | hp
      · exact (B.incomparable i j hn).1 ⟨hi,hp⟩
      · exact (B.incomparable i j hn).2 ⟨hi.symm,hp⟩
    subst j
    have hp : (B.node i).1.2++q.1 = (B.node i).1.2++r.1 :=
      congrArg (fun l : GBranch G.tree => l.1.2) he
    have hqr : q = r := Subtype.ext (List.append_cancel_left hp)
    subst r
    rfl

theorem spliceBranchPieceOld_surjective_retained (l : GBranch G.tree) (hl : IsSpliceRetainedBranch B l) :
    ∃ p : SpliceBranchPiece B, spliceBranchPieceOld B p = l := by
  rcases hl with hout | ⟨i,hi,hp⟩
  · exact ⟨.inl ⟨l,hout⟩,rfl⟩
  · obtain ⟨q,hq⟩ := hp
    have hleaf : (B.node i).1.2++q ∈ (G.tree (B.node i).1.1).branching := by
      rw [hq]
      exact hi.symm ▸ l.2
    have hqleaf := (Comb.subtree_branching_iff (spliceNodeSubtree_spec G (B.node i)) q).mpr hleaf
    exact ⟨.inr ⟨i,⟨q,hqleaf⟩⟩,Subtype.ext (Prod.ext hi hq)⟩

end WaveTurbulence.Mole
