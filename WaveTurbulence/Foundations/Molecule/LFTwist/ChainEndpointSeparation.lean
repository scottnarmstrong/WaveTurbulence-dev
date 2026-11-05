/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.LFTwist.ExchangeLocality
public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.ChainEndpointGeometry

/-! # Native chain endpoints avoid every other nonancestor source slot -/

public section
namespace WaveTurbulence.LFTwist
open TTree Reg Reg.Skeleton Twist
variable {w : ℕ} {S : Garden w} (D : ReconstructionData S)

/-- A different source node below a branch is below its terminal core hole. -/
theorem corePosition_below_source_desc (b : GBranch S.tree) (n : GNode S.tree)
    (hbn : Below b.1 n.1) (hne : b.toNode ≠ n) :
    Below (D.corePosition b) (inflatedPosition S D.tree n) := by
  obtain ⟨i,hi⟩ := below_child_of_desc_ne b n hbn hne
  have he := inflatedPosition_below S D.tree (b.child i) n hi
  rw [D.core_child_position] at he
  exact below_trans (below_extend _ _) he

/-- A chain's internal matching cannot enter any nonancestor source node. -/
theorem chain_endpoint_not_below_source (b : GBranch S.tree) (n : GNode S.tree)
    (hn : ¬ Below n.1 b.1) (z : Address w)
    (hz : z ∈ pairEndpoints ((D.tree b).pairsAt (nodeSign S.sig b.1)
      (inflatedPosition S D.tree b.toNode))) :
    ¬ Below (inflatedPosition S D.tree n) z := by
  by_cases hb : Below b.1 n.1
  · have hne : b.toNode ≠ n := by
      intro he
      apply hn
      rw [← he]
      exact ⟨rfl,List.prefix_refl _⟩
    have hc := corePosition_below_source_desc D b n hb hne
    intro h
    exact chain_endpoint_not_below_lone (D.tree b) (nodeSign S.sig b.1)
      (inflatedPosition S D.tree b.toNode) z hz (below_trans hc h)
  · have hi := inflatedPosition_incomp S D.tree n b.toNode ⟨hn,hb⟩
    obtain ⟨q,hq,_,_⟩ := chain_endpoint_frame (D.tree b) (nodeSign S.sig b.1)
      (inflatedPosition S D.tree b.toNode) z hz
    intro h
    rw [hq] at h
    exact (hi.descendants ⟨rfl,List.prefix_refl _⟩ (below_extend _ q)).1 h

/-- Outside the moved crown, every internal chain endpoint is fixed literally. -/
theorem inflatedExchange_chain_endpoint_fixed (P : CorePlacement S) (b : GBranch S.tree)
    (hb : ¬ Below P.lower.1 b.1) (z : Address w)
    (hz : z ∈ pairEndpoints ((D.tree b).pairsAt (nodeSign S.sig b.1)
      (inflatedPosition S D.tree b.toNode))) : inflatedExchange S P D z = z := by
  have ha := chain_endpoint_not_below_source D b P.lower.toNode hb z hz
  have hp : ¬ Below (S.pair P.retained).1 b.1 := by
    intro he
    exact leaf_not_prefix_branch (S.pair P.retained).2 (he.1 ▸ b.2) he.2
  have hd := chain_endpoint_not_below_source D b (S.pair P.retained).toNode hp z hz
  have he : z ≠ inflatedPosition S D.tree (S.pair P.retained).toNode := by
    intro he
    exact hd (he ▸ ⟨rfl,List.prefix_refl _⟩)
  exact (ite_eq_right ha).trans (ite_eq_right he)

end WaveTurbulence.LFTwist
