/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.EraseTreeSubtreeReplacement
public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.RawChainInsertion
public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.InflatedSubtrees
public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.InflatedSigns

/-! # Literal whole-forest factorization for erasing one regular-tree slot -/

public section
namespace WaveTurbulence.Reg.Skeleton
open TTree

theorem ReconstructionData.eraseTree_raw_forest {w : ℕ} {S : Garden w}
    (D : ReconstructionData S) (hS : S.IsPlain) (b : GBranch S.tree) :
    (D.raw hS).tree = (((D.eraseTree b).raw hS).insertChain
      (inflatedPosition S (D.eraseTree b).tree b.toNode) (D.tree b)).tree := by
  let E := D.eraseTree b
  let A := inflatedPosition S E.tree b.toNode
  have hi : A.1 = b.1.1 := inflatedPosition_index S E.tree b.toNode
  have hs : nodeSign S.sig A = nodeSign S.sig b.1 := inflatedPosition_sign S E.tree b.toNode
  have ht : (E.forest hS A.1).subtreeAt A.2 = E.inflateNode hS b.toNode :=
    subtreeAt_eq_of_subtree _ _ _ (E.forest_subtree_position hS b.toNode)
  have hnode : (D.tree b).plug (nodeSign S.sig b.1) (E.inflateNode hS b.toNode) =
      D.inflateNode hS b.toNode := by
    rw [D.eraseTree_inflateNode_at,D.inflateNode_branch]
  change D.forest hS = Function.update (E.forest hS) A.1
    ((E.forest hS A.1).setAt A.2 ((D.tree b).plug (nodeSign S.sig A) ((E.forest hS A.1).subtreeAt A.2)))
  rw [hs,ht,hnode,setAt_eq_replaceAt]
  funext j
  by_cases hj : j = b.1.1
  · subst j
    rw [hi,Function.update_self]
    obtain ⟨p,hp,hforest⟩ := D.eraseTree_subtree_replacement hS b (GNode.root S.tree b.1.1)
      ⟨rfl,List.nil_prefix⟩
    have hpath : p = A.2 := by
      have hh := congrArg (fun z : Address w => z.2) hp
      simpa only [inflatedPosition_root,addrExt,List.nil_append] using hh.symm
    rw [hpath] at hforest
    exact hforest
  · rw [Function.update_of_ne (fun h => hj (h.trans hi))]
    apply (D.eraseTree_inflateNode_of_not_below hS b (GNode.root S.tree j) ?_).symm
    intro h
    exact hj h.1.symm

end WaveTurbulence.Reg.Skeleton
