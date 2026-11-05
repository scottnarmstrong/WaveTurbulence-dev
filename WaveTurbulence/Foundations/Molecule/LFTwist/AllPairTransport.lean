/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.LFTwist.ChainPairTransport
public import WaveTurbulence.Foundations.Molecule.LFTwist.CouplePairTransport

/-! # Complete reconstructed matching transport, including exceptional orientation -/

public section
namespace WaveTurbulence.LFTwist
open TTree Reg Reg.Skeleton Twist
variable {w : ℕ} (S : Garden w) (P : CorePlacement S) (hS : S.IsPlain) (D : ReconstructionData S)

private theorem firstLeaf_pair (q : SourcePair S) : S.pair (q.firstLeaf hS) = q.secondLeaf hS := by
  have hh := (pairOfLeaf_sides_pos S hS (q.firstLeaf hS) (sourcePair_first_sign S hS q)).2
  rw [pairOfLeaf_firstLeaf] at hh
  exact hh.symm

/-- Every old actual matching pair has its two physical images paired in the
transported reconstruction. The exceptional pair may reverse its orientation. -/
theorem all_pairs_addressPaired_twist (hnil : D.tree P.lower = .nil)
    (hq : D.couple (pairOfLeaf S hS P.retained) = .triv) (r : Pair w)
    (hr : r ∈ sourcePairs (D.garden hS)) :
    AddressPaired ((twistReconstruction S P hS D).garden (unitTwistGarden_plain S P hS))
      (inflatedExchange S P D r.1) (inflatedExchange S P D r.2) := by
  let E := twistReconstruction S P hS D
  let hnew := unitTwistGarden_plain S P hS
  have hp := congrArg Raw.pairs (D.garden_decodes hS).2
  change D.attachmentPairs hS = sourcePairs (D.garden hS) at hp
  rw [← hp] at hr
  rcases Finset.mem_union.mp hr with hr | hr
  · obtain ⟨q,_,hr⟩ := Finset.mem_biUnion.mp hr
    have hm := List.mem_toFinset.mp hr
    by_cases he : q = pairOfLeaf S hS P.retained
    · have hc : D.couple q = .triv := he ▸ hq
      rw [hc] at hm
      have hv : r = (inflatedPosition S D.tree (q.firstLeaf hS).toNode,
          inflatedPosition S D.tree (q.secondLeaf hS).toNode) := List.mem_singleton.mp hm
      rw [hv]
      have hh := exceptional_addressPaired_twist S P hS D hnil hq (q.firstLeaf hS)
        ((pairOfLeaf_firstLeaf S hS q).trans he)
      exact (firstLeaf_pair S hS q) ▸ hh
    · have hm' : (inflatedExchange S P D r.1,inflatedExchange S P D r.2) ∈
          (E.couple (twistSourcePairEquiv S P hS q)).pairsAt
            (inflatedPosition (unitTwistGarden S P) E.tree
              ((twistSourcePairEquiv S P hS q).firstLeaf hnew).toNode)
            (inflatedPosition (unitTwistGarden S P) E.tree
              ((twistSourcePairEquiv S P hS q).secondLeaf hnew).toNode) := by
        rw [couple_pairs_twist S P hS D hnil q he]
        exact List.mem_map.mpr ⟨r,hm,rfl⟩
      exact addressPaired_of_sourcePairs _ _ (E.couple_pair_mem hnew (E.garden_decodes hnew) _ _ hm')
  · obtain ⟨b,_,hr⟩ := Finset.mem_biUnion.mp hr
    have hm := List.mem_toFinset.mp hr
    have hm' : (inflatedExchange S P D r.1,inflatedExchange S P D r.2) ∈
        (E.tree (coreBranchEquiv S P b)).pairsAt
          (nodeSign (unitTwistGarden S P).sig (coreBranchEquiv S P b).1)
          (inflatedPosition (unitTwistGarden S P) E.tree (coreBranchEquiv S P b).toNode) := by
      rw [chain_pairs_twist S P hS D hnil b]
      exact List.mem_map.mpr ⟨r,hm,rfl⟩
    exact addressPaired_of_sourcePairs _ _ (E.chain_pair_mem hnew (E.garden_decodes hnew) _ _ hm')

end WaveTurbulence.LFTwist
