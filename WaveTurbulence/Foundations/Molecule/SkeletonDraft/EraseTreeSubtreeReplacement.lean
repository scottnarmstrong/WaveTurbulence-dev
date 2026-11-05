/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.EraseTreeLocalSubtrees
public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.EraseTreeUpperPosition
public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.Node3Replacement
public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.ChainHoleReplacement
public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.InflatedPositionInjective

/-! # Removing one tree context changes exactly one subtree in every source ancestor -/

public section
namespace WaveTurbulence.Reg.Skeleton
open TTree

theorem ReconstructionData.eraseTree_subtree_replacement {w : ℕ} {S : Garden w}
    (D : ReconstructionData S) (hS : S.IsPlain) (b : GBranch S.tree) (a : GNode S.tree)
    (hab : Below a.1 b.1) : ∃ p : Path,
      inflatedPosition S (D.eraseTree b).tree b.toNode =
        addrExt (inflatedPosition S (D.eraseTree b).tree a) p ∧
      D.inflateNode hS a = Comb.replaceAt ((D.eraseTree b).inflateNode hS a) p
        (D.inflateNode hS b.toNode) := by
  let E := D.eraseTree b
  by_cases he : a = b.toNode
  · subst a
    exact ⟨[],by simp [addrExt],by simp [Comb.replaceAt]⟩
  · cases hs : Comb.nodeSubtree a with
    | leaf =>
      obtain ⟨q,hq⟩ := below_exists_frame a.1 b.1 hab
      have hbq : q ∈ (Comb.nodeSubtree a).branching := by
        apply (Comb.subtree_branching_iff (Comb.nodeSubtree_spec a) q).mpr
        change (addrExt a.1 q).2 ∈ (S.tree (addrExt a.1 q).1).branching
        rw [← hq]
        exact b.2
      rw [hs] at hbq
      exact (Finset.notMem_empty _ hbq).elim
    | node l m r =>
      let c := branchOfSubtree a l m r hs
      have hca : c.toNode = a := Subtype.ext rfl
      have hbc : c ≠ b := fun hc => he (hca.symm.trans (congrArg GBranch.toNode hc))
      obtain ⟨i,hi⟩ := below_child_of_desc_ne c b.toNode hab (fun h => he (hca.symm.trans h))
      obtain ⟨q,hq,ht⟩ := D.eraseTree_subtree_replacement hS b (c.child i) hi
      let p := (E.tree c).lonePath ++ [i] ++ q
      have hpos : inflatedPosition S E.tree b.toNode = addrExt (inflatedPosition S E.tree a) p := by
        rw [hq,inflatedPosition_child,addrExt_append]
        exact congrArg (fun z => addrExt z p) (congrArg (inflatedPosition S E.tree) hca)
      have hchildren : node3 (fun j => D.inflateNode hS (c.child j)) =
          Comb.replaceAt (node3 (fun j => E.inflateNode hS (c.child j))) ([i] ++ q)
            (D.inflateNode hS b.toNode) := by
        rw [replaceAt_node3_child]
        apply congrArg node3
        funext j
        by_cases hj : j = i
        · subst j
          rw [Function.update_self]
          exact ht
        · rw [Function.update_of_ne hj]
          symm
          apply D.eraseTree_inflateNode_of_not_below hS b
          intro hbelow
          have hsep := incomp_distinct_children c.1 j i [] [] hj
          have hcomp := below_comparable hbelow hi
          exact hcomp.elim hsep.1 hsep.2
      have htree : D.inflateNode hS c.toNode =
          Comb.replaceAt (E.inflateNode hS c.toNode) p (D.inflateNode hS b.toNode) := by
        have hcode : D.tree c = E.tree c := (D.eraseTree_other b c hbc).symm
        rw [D.inflateNode_branch,E.inflateNode_branch,hcode]
        simp only [p,List.append_assoc]
        rw [replaceAt_plug_lone_append]
        exact congrArg ((E.tree c).plug (nodeSign S.sig c.1)) hchildren
      exact ⟨p,hpos,(congrArg (D.inflateNode hS) hca.symm).trans
        (htree.trans (congrArg (fun t => Comb.replaceAt t p (D.inflateNode hS b.toNode))
          (congrArg (E.inflateNode hS) hca)))⟩
termination_by (Comb.nodeSubtree a).order
decreasing_by exact nodeSubtree_child_order_lt S.tree _ _

end WaveTurbulence.Reg.Skeleton
