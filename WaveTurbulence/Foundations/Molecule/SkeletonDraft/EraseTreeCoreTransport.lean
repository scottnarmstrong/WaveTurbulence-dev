/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.EraseTreeLocalPairRoots

/-! # Every retained core branch follows the exact prefix transport of a tree-slot erasure -/

public section
namespace WaveTurbulence.Reg.Skeleton
open TTree

theorem ReconstructionData.eraseTree_corePosition {w : ℕ} {S : Garden w}
    (D : ReconstructionData S) (b c : GBranch S.tree) :
    D.corePosition c =
      stretch (inflatedPosition S (D.eraseTree b).tree b.toNode) (D.tree b).lonePath
        ((D.eraseTree b).corePosition c) := by
  let E := D.eraseTree b
  let A := inflatedPosition S E.tree b.toNode
  by_cases hcb : c = b
  · subst c
    have hnil : E.tree b = .nil := D.eraseTree_at b
    have hp : inflatedPosition S D.tree b.toNode = A := (D.eraseTree_position_at b).symm
    change addrExt (inflatedPosition S D.tree b.toNode) (D.tree b).lonePath =
      stretch A (D.tree b).lonePath (addrExt A (E.tree b).lonePath)
    rw [hp,hnil]
    simpa only [RegChain.lonePath,addrExt,List.append_nil] using (stretch_frame A (D.tree b).lonePath []).symm
  · have hcode : D.tree c = E.tree c := (D.eraseTree_other b c hcb).symm
    by_cases hc : Below c.1 b.1
    · have hn : ¬ Below b.1 c.1 := by
        intro hb
        exact hcb (Subtype.ext (Prod.ext hb.1 (hc.2.eq_of_length (Nat.le_antisymm hc.2.length_le hb.2.length_le))))
      have hp := D.eraseTree_position_of_not_below b c.toNode hn
      obtain ⟨i,hi⟩ := below_child_of_desc_ne c b.toNode hc (fun h =>
        hcb (Subtype.ext (congrArg (fun z : GNode S.tree => z.1) h)))
      have hbelow : Below (addrExt (E.corePosition c) [i]) A := by
        have he := inflatedPosition_below S E.tree (c.child i) b.toNode hi
        rw [E.core_child_position] at he
        exact he
      have hout : ¬ Below A (E.corePosition c) := by
        intro h
        have hl := h.2.length_le
        have hu := hbelow.2.length_le
        change ((E.corePosition c).2 ++ [i]).length ≤ A.2.length at hu
        simp only [List.length_append,List.length_singleton] at hu
        omega
      have heq : D.corePosition c = E.corePosition c :=
        congrArg₂ addrExt hp.symm (congrArg RegChain.lonePath hcode)
      exact heq.trans (stretch_outside A (D.tree b).lonePath _ hout).symm
    · have hp := D.eraseTree_pair_root_transport b c.toNode hc
      exact (congrArg₂ addrExt hp.1 (congrArg RegChain.lonePath hcode)).trans
        (hp.2 (E.tree c).lonePath).symm

end WaveTurbulence.Reg.Skeleton
