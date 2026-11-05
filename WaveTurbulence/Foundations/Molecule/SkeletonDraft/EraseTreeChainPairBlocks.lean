/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.EraseTreeLocalPairRoots
public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.ListPairImages

/-! # Exact transport of all other branch replacement pair blocks under a tree-slot erasure -/

public section
namespace WaveTurbulence.Reg.Skeleton

theorem ReconstructionData.eraseTree_chain_pair_block {w : ℕ} {S : Garden w}
    (D : ReconstructionData S) (b c : GBranch S.tree) (hcb : c ≠ b) :
    let E := D.eraseTree b
    let A := inflatedPosition S E.tree b.toNode
    ((D.tree c).pairsAt (nodeSign S.sig c.1) (inflatedPosition S D.tree c.toNode)).toFinset =
      (((E.tree c).pairsAt (nodeSign S.sig c.1) (inflatedPosition S E.tree c.toNode)).toFinset.image
        (fun q => (stretch A (D.tree b).lonePath q.1,stretch A (D.tree b).lonePath q.2))) := by
  classical
  dsimp only
  let E := D.eraseTree b
  let A := inflatedPosition S E.tree b.toNode
  have hcode : E.tree c = D.tree c := D.eraseTree_other b c hcb
  by_cases hc : Below c.1 b.1
  · have hn : ¬ Below b.1 c.1 := by
      intro hb
      exact hcb (Subtype.ext (Prod.ext hb.1 (hc.2.eq_of_length (Nat.le_antisymm hc.2.length_le hb.2.length_le))))
    have hp := D.eraseTree_position_of_not_below b c.toNode hn
    obtain ⟨i,hi⟩ := below_child_of_desc_ne c b.toNode hc (fun h =>
      hcb (Subtype.ext (congrArg (fun z : GNode S.tree => z.1) h)))
    have hbelow : Below (E.corePosition c) A := by
      have he := inflatedPosition_below S E.tree (c.child i) b.toNode hi
      rw [E.core_child_position] at he
      exact below_trans (below_extend _ _) he
    have he := chain_pairs_image_fixed_below_lone (E.tree c) (nodeSign S.sig c.1)
      (inflatedPosition S E.tree c.toNode) A (D.tree b).lonePath hbelow
    have hleft : ((D.tree c).pairsAt (nodeSign S.sig c.1) (inflatedPosition S D.tree c.toNode)).toFinset =
        ((E.tree c).pairsAt (nodeSign S.sig c.1) (inflatedPosition S E.tree c.toNode)).toFinset := by
      rw [hcode,hp]
    exact hleft.trans he.symm
  · have hp := D.eraseTree_pair_root_transport b c.toNode hc
    have he := chain_pairsAt_map_local (E.tree c) (stretch A (D.tree b).lonePath)
      (inflatedPosition S E.tree c.toNode) hp.2 (nodeSign S.sig c.1)
    have hh := congrArg List.toFinset he
    rw [← hp.1,list_map_toFinset] at hh
    exact (congrArg (fun X : RegChain =>
      (X.pairsAt (nodeSign S.sig c.1) (inflatedPosition S D.tree c.toNode)).toFinset) hcode.symm).trans hh

end WaveTurbulence.Reg.Skeleton
