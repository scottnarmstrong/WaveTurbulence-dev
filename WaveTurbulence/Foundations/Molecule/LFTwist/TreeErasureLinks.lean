/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.LFTwist.LinkNaturality
public import WaveTurbulence.Foundations.Molecule.LayerRegDraft.Coherent
public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.EraseTreeChainPairBlocks
public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.EraseTreeCouplePairBlocks

/-! # Exact transport of every remaining attachment's links under tree erasure -/

public section
namespace WaveTurbulence.LFTwist
open TTree Reg Reg.Skeleton Links

/-- Every leaf-pair attachment keeps its complete coherence-link list. -/
theorem eraseTree_couple_links {w : ℕ} {S : Garden w} (D : ReconstructionData S)
    (hS : S.IsPlain) (b : GBranch S.tree) (q : SourcePair S) :
    let E := D.eraseTree b
    let A := inflatedPosition S E.tree b.toNode
    (D.couple q).linksAt (inflatedPosition S D.tree (q.firstLeaf hS).toNode)
      (inflatedPosition S D.tree (q.secondLeaf hS).toNode) =
    ((E.couple q).linksAt (inflatedPosition S E.tree (q.firstLeaf hS).toNode)
      (inflatedPosition S E.tree (q.secondLeaf hS).toNode)).map
        (fun p => (stretch A (D.tree b).lonePath p.1,stretch A (D.tree b).lonePath p.2)) := by
  dsimp only
  let E := D.eraseTree b
  let A := inflatedPosition S E.tree b.toNode
  have hl := D.eraseTree_pair_root_transport b (q.firstLeaf hS).toNode
    (leaf_not_above_branch S.tree (q.firstLeaf hS) b)
  have hr := D.eraseTree_pair_root_transport b (q.secondLeaf hS).toNode
    (leaf_not_above_branch S.tree (q.secondLeaf hS) b)
  have he := couple_linksAt_map_local (D.couple q) (stretch A (D.tree b).lonePath) _ _ hl.2 hr.2
  rw [← hl.1, ← hr.1] at he
  exact he

/-- Every other branch attachment keeps its complete coherence-link list. -/
theorem eraseTree_chain_links {w : ℕ} {S : Garden w} (D : ReconstructionData S)
    (b c : GBranch S.tree) (hcb : c ≠ b) :
    let E := D.eraseTree b
    let A := inflatedPosition S E.tree b.toNode
    (D.tree c).linksAt (nodeSign S.sig c.1) (inflatedPosition S D.tree c.toNode) =
    ((E.tree c).linksAt (nodeSign S.sig c.1) (inflatedPosition S E.tree c.toNode)).map
      (fun q => (stretch A (D.tree b).lonePath q.1,stretch A (D.tree b).lonePath q.2)) := by
  dsimp only
  let E := D.eraseTree b
  let A := inflatedPosition S E.tree b.toNode
  have hcode : E.tree c = D.tree c := D.eraseTree_other b c hcb
  by_cases hc : Below c.1 b.1
  · have hn : ¬ Below b.1 c.1 := by
      intro hb
      exact hcb (Subtype.ext (Prod.ext hb.1
        (hc.2.eq_of_length (Nat.le_antisymm hc.2.length_le hb.2.length_le))))
    have hp := D.eraseTree_position_of_not_below b c.toNode hn
    obtain ⟨i,hi⟩ := below_child_of_desc_ne c b.toNode hc (fun h =>
      hcb (Subtype.ext (congrArg (fun z : GNode S.tree => z.1) h)))
    have hbelow : Below (E.corePosition c) A := by
      have he := inflatedPosition_below S E.tree (c.child i) b.toNode hi
      rw [E.core_child_position] at he
      exact below_trans (below_extend _ _) he
    have he := chain_links_image_fixed_below_lone (E.tree c) (nodeSign S.sig c.1)
      (inflatedPosition S E.tree c.toNode) A (D.tree b).lonePath hbelow
    have hleft : (D.tree c).linksAt (nodeSign S.sig c.1) (inflatedPosition S D.tree c.toNode) =
        (E.tree c).linksAt (nodeSign S.sig c.1) (inflatedPosition S E.tree c.toNode) := by
      rw [hcode,hp]
    exact hleft.trans he.symm
  · have hp := D.eraseTree_pair_root_transport b c.toNode hc
    have he := chain_linksAt_map_local (E.tree c) (stretch A (D.tree b).lonePath)
      (inflatedPosition S E.tree c.toNode) hp.2 (nodeSign S.sig c.1)
    rw [← hp.1] at he
    exact (congrArg (fun X : RegChain =>
      X.linksAt (nodeSign S.sig c.1) (inflatedPosition S D.tree c.toNode)) hcode.symm).trans he

/-- Equality of transported endpoint layers is exactly coherence of the original list. -/
theorem cohOn_map_iff {w v : ℕ} (LG : LayeredGarden w) (LH : LayeredGarden v)
    (f : Address v → Address w) (hf : ∀ z, layerAt LG (f z) = layerAt LH z)
    (L : List (Pair v)) :
    CohOn LG (L.map (fun q => (f q.1,f q.2))) ↔ CohOn LH L := by
  constructor
  · intro h q hq
    have hh := h (f q.1,f q.2) (List.mem_map.mpr ⟨q,hq,rfl⟩)
    exact (hf q.1).symm.trans (hh.trans (hf q.2))
  · intro h q hq
    obtain ⟨r,hr,he⟩ := List.mem_map.mp hq
    subst q
    exact (hf r.1).trans ((h r hr).trans (hf r.2).symm)

end WaveTurbulence.LFTwist
