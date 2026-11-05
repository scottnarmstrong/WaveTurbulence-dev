/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.LFTwist.ChainEndpointSeparation

/-! # All native chain matching blocks commute with the physical exchange -/

public section
namespace WaveTurbulence.LFTwist
open TTree Reg Reg.Skeleton Twist
variable {w : ℕ} (S : Garden w) (P : CorePlacement S) (hS : S.IsPlain) (D : ReconstructionData S)

/-- Strictly inside the crown the map respects the whole local context. -/
theorem inflatedExchange_branch_respectsAt_inside (b : GBranch S.tree)
    (hb : Below P.lower.1 b.1) (hne : b ≠ P.lower) :
    RespectsAt (inflatedExchange S P D) (inflatedPosition S D.tree b.toNode) := by
  apply exchange_respectsAt_of_away
  · intro he
    have hh := (inflatedPosition_below_iff S D.tree b.toNode P.lower.toNode).mp he
    exact hne (Subtype.ext (Prod.ext hh.1.symm (hh.2.eq_of_length
      (Nat.le_antisymm hh.2.length_le hb.2.length_le))))
  · intro he
    have hh := (inflatedPosition_below_iff S D.tree (S.pair P.retained).toNode b.toNode).mp he
    exact leaf_not_prefix_branch (S.pair P.retained).2 (hh.1 ▸ b.2) hh.2
  · intro he
    have hh := (inflatedPosition_below_iff S D.tree b.toNode (S.pair P.retained).toNode).mp he
    have hd := below_trans hb hh
    exact P.paired_outside ⟨hd.1.symm,hd.2⟩

/-- An ordinary chain outside the crown has a fixed root and fixed internal pairs. -/
theorem inflatedExchange_chain_pairs (b : GBranch S.tree) (hb : ¬ Below P.lower.1 b.1) :
    (D.tree b).pairsAt (nodeSign S.sig b.1)
        (inflatedExchange S P D (inflatedPosition S D.tree b.toNode)) =
      ((D.tree b).pairsAt (nodeSign S.sig b.1) (inflatedPosition S D.tree b.toNode)).map
        (fun q => (inflatedExchange S P D q.1,inflatedExchange S P D q.2)) := by
  have ha : ¬ Below (inflatedPosition S D.tree P.lower.toNode) (inflatedPosition S D.tree b.toNode) :=
    fun he => hb ((inflatedPosition_below_iff S D.tree P.lower.toNode b.toNode).mp he)
  have hp : inflatedPosition S D.tree b.toNode ≠ inflatedPosition S D.tree (S.pair P.retained).toNode := by
    intro he
    exact Mole.branch_toNode_ne_leaf b (S.pair P.retained) (inflatedPosition_injective S D.tree he)
  have hr : inflatedExchange S P D (inflatedPosition S D.tree b.toNode) =
      inflatedPosition S D.tree b.toNode := (ite_eq_right ha).trans (ite_eq_right hp)
  rw [hr]
  symm
  conv_rhs => rw [← List.map_id ((D.tree b).pairsAt (nodeSign S.sig b.1) (inflatedPosition S D.tree b.toNode))]
  apply List.map_congr_left
  intro q hq
  exact Prod.ext
    (inflatedExchange_chain_endpoint_fixed D P b hb q.1 ((mem_pairEndpoints_iff _ _).mpr ⟨q,hq,Or.inl rfl⟩))
    (inflatedExchange_chain_endpoint_fixed D P b hb q.2 ((mem_pairEndpoints_iff _ _).mpr ⟨q,hq,Or.inr rfl⟩))

/-- Every actual chain block has exactly its transported internal matching;
the erased lower block is empty. -/
theorem chain_pairs_twist (hnil : D.tree P.lower = .nil) (b : GBranch S.tree) :
    ((twistReconstruction S P hS D).tree (coreBranchEquiv S P b)).pairsAt
        (nodeSign (unitTwistGarden S P).sig (coreBranchEquiv S P b).1)
        (inflatedPosition (unitTwistGarden S P) (twistReconstruction S P hS D).tree
          (coreBranchEquiv S P b).toNode) =
      ((D.tree b).pairsAt (nodeSign S.sig b.1) (inflatedPosition S D.tree b.toNode)).map
        (fun q => (inflatedExchange S P D q.1,inflatedExchange S P D q.2)) := by
  have hc := transportReconstruction_tree hS (unitTwistGarden_plain S P hS)
    (coreBranchEquiv S P) (coreLeafEquiv S P) (fun l => (unitTwistGarden_pair S P l).symm) D b
  change (twistReconstruction S P hS D).tree (coreBranchEquiv S P b) = D.tree b at hc
  rw [hc]
  by_cases he : b = P.lower
  · rw [he,hnil]
    rfl
  · rw [ordinaryBranchSign_twist S P b he, inflatedPosition_branch_twist S P hS D hnil b]
    by_cases hb : Below P.lower.1 b.1
    · exact chain_pairsAt_map_local (D.tree b) (inflatedExchange S P D)
        (inflatedPosition S D.tree b.toNode) (inflatedExchange_branch_respectsAt_inside S P D b hb he)
        (nodeSign S.sig b.1)
    · exact inflatedExchange_chain_pairs S P D b hb

end WaveTurbulence.LFTwist
