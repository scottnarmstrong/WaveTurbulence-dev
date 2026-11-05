/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.PathSeparation
public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.InflatedPositionMonotone

/-! # Incomparable actual source slots remain incomparable after inflation -/

public section
namespace WaveTurbulence.Reg.Skeleton
open TTree

theorem inflatedPosition_index {w : ℕ} (S : Garden w) (X : GBranch S.tree → RegChain)
    (a : GNode S.tree) : (inflatedPosition S X a).1 = a.1.1 := by
  have he := inflatedPosition_below S X (GNode.root S.tree a.1.1) a ⟨rfl,List.nil_prefix⟩
  simpa only [inflatedPosition_root] using he.1

theorem inflatedPosition_incomp {w : ℕ} (S : Garden w) (X : GBranch S.tree → RegChain)
    (a b : GNode S.tree) (hab : IncompAddr a.1 b.1) :
    IncompAddr (inflatedPosition S X a) (inflatedPosition S X b) := by
  by_cases hidx : a.1.1 = b.1.1
  · obtain ⟨r,i,j,s,t,hp,hq,hij⟩ := incomparable_paths_split a.1.2 b.1.2
      (fun he => hab.1 ⟨hidx.symm,he⟩) (fun he => hab.2 ⟨hidx,he⟩)
    have hn : r ++ [i] ∈ (S.tree a.1.1).nodes := by
      apply Comb.TreePath.mem_nodes_of_prefix _ a.2
      rw [hp]
      exact ⟨s,by simp [List.append_assoc]⟩
    let c : GNode S.tree := ⟨(a.1.1,r ++ [i]),hn⟩
    have hc : c.1.2 ≠ [] := by simp [c]
    let d := c.parent hc
    have hd : d.1 = (a.1.1,r) := by
      apply Prod.ext
      · rfl
      · simp [d,c,GNode.parent]
    have hda : Below (d.child i).1 a.1 := by
      change a.1.1 = d.1.1 ∧ d.1.2 ++ [i] <+: a.1.2
      rw [hd,hp]
      exact ⟨rfl,⟨s,by simp [List.append_assoc]⟩⟩
    have hdb : Below (d.child j).1 b.1 := by
      change b.1.1 = d.1.1 ∧ d.1.2 ++ [j] <+: b.1.2
      rw [hd,hq]
      exact ⟨hidx.symm,⟨t,by simp [List.append_assoc]⟩⟩
    have hci : inflatedPosition S X (d.child i) =
        addrExt (addrExt (inflatedPosition S X d.toNode) (X d).lonePath) [i] := by
      rw [inflatedPosition_child,addrExt_append]
    have hcj : inflatedPosition S X (d.child j) =
        addrExt (addrExt (inflatedPosition S X d.toNode) (X d).lonePath) [j] := by
      rw [inflatedPosition_child,addrExt_append]
    have hi : IncompAddr (inflatedPosition S X (d.child i)) (inflatedPosition S X (d.child j)) := by
      rw [hci,hcj]
      exact incomp_distinct_children _ i j [] [] hij
    exact hi.descendants (inflatedPosition_below S X _ _ hda) (inflatedPosition_below S X _ _ hdb)
  · have ha := inflatedPosition_index S X a
    have hb := inflatedPosition_index S X b
    constructor
    · intro he
      exact hidx (ha.symm.trans (he.1.symm.trans hb))
    · intro he
      exact hidx (ha.symm.trans (he.1.trans hb))

end WaveTurbulence.Reg.Skeleton
