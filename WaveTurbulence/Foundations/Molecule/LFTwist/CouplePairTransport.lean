/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.LFTwist.ExchangeLocality
public import WaveTurbulence.Foundations.Molecule.LFTwist.TrivialPairLeaves

/-! # Ordinary couple matching and the reversed exceptional trivial pair -/

public section
namespace WaveTurbulence.LFTwist
open TTree Reg Reg.Skeleton Twist
variable {w : ℕ} (S : Garden w) (P : CorePlacement S) (hS : S.IsPlain) (D : ReconstructionData S)

/-- Both leaves of an ordinary source slot are distinct from the exceptional pair. -/
theorem ordinary_pair_leaves (q : SourcePair S) (hq : q ≠ pairOfLeaf S hS P.retained) :
    q.firstLeaf hS ≠ S.pair P.retained ∧ q.secondLeaf hS ≠ S.pair P.retained := by
  constructor
  · intro he
    apply hq
    exact (pairOfLeaf_firstLeaf S hS q).symm.trans
      ((congrArg (pairOfLeaf S hS) he).trans (pairOfLeaf_partner S hS P.retained))
  · intro he
    apply hq
    exact (pairOfLeaf_secondLeaf S hS q).symm.trans
      ((congrArg (pairOfLeaf S hS) he).trans (pairOfLeaf_partner S hS P.retained))

/-- Every ordinary oriented couple block retains its exact code and matching. -/
theorem couple_pairs_twist (hnil : D.tree P.lower = .nil) (q : SourcePair S)
    (hq : q ≠ pairOfLeaf S hS P.retained) :
    ((twistReconstruction S P hS D).couple (twistSourcePairEquiv S P hS q)).pairsAt
      (inflatedPosition (unitTwistGarden S P) (twistReconstruction S P hS D).tree
        ((twistSourcePairEquiv S P hS q).firstLeaf (unitTwistGarden_plain S P hS)).toNode)
      (inflatedPosition (unitTwistGarden S P) (twistReconstruction S P hS D).tree
        ((twistSourcePairEquiv S P hS q).secondLeaf (unitTwistGarden_plain S P hS)).toNode) =
    ((D.couple q).pairsAt (inflatedPosition S D.tree (q.firstLeaf hS).toNode)
      (inflatedPosition S D.tree (q.secondLeaf hS).toNode)).map
        (fun r => (inflatedExchange S P D r.1,inflatedExchange S P D r.2)) := by
  have hc := transportReconstruction_couple hS (unitTwistGarden_plain S P hS)
    (coreBranchEquiv S P) (coreLeafEquiv S P) (fun l => (unitTwistGarden_pair S P l).symm) D q
  change (twistReconstruction S P hS D).couple (twistSourcePairEquiv S P hS q) = D.couple q at hc
  have hs := twistSourcePair_sides S P hS q hq
  rw [hc,hs.1,hs.2]
  apply (congrArg₂ (D.couple q).pairsAt
    (inflatedPosition_leaf_twist S P hS D hnil (q.firstLeaf hS))
    (inflatedPosition_leaf_twist S P hS D hnil (q.secondLeaf hS))).trans
  exact couple_pairsAt_map_local (D.couple q) (inflatedExchange S P D) _ _
    (inflatedExchange_leaf_respectsAt S P D _ (ordinary_pair_leaves S P hS q hq).1)
    (inflatedExchange_leaf_respectsAt S P D _ (ordinary_pair_leaves S P hS q hq).2)

/-- Literal actual matching of two raw addresses, with either orientation allowed. -/
@[expose] def AddressPaired (G : Garden w) (a b : Address w) : Prop :=
  ∃ l : GLeaf G.tree, l.1 = a ∧ (G.pair l).1 = b

/-- Any oriented source pair gives its literal actual matching. -/
theorem addressPaired_of_sourcePairs (G : Garden w) (r : Pair w) (hr : r ∈ sourcePairs G) :
    AddressPaired G r.1 r.2 := by
  obtain ⟨l,_,he⟩ := Finset.mem_image.mp hr
  exact ⟨l,congrArg Prod.fst he,congrArg Prod.snd he⟩

/-- The exceptional trivial block is transported as an actual matching. Its
positive/negative orientation may reverse, so no oriented pair-image claim is made. -/
theorem exceptional_addressPaired_twist (hnil : D.tree P.lower = .nil)
    (hq : D.couple (pairOfLeaf S hS P.retained) = .triv) (l : GLeaf S.tree)
    (hl : pairOfLeaf S hS l = pairOfLeaf S hS P.retained) :
    AddressPaired ((twistReconstruction S P hS D).garden (unitTwistGarden_plain S P hS))
      (inflatedExchange S P D (inflatedPosition S D.tree l.toNode))
      (inflatedExchange S P D (inflatedPosition S D.tree (S.pair l).toNode)) := by
  let E := twistReconstruction S P hS D
  let hnew := unitTwistGarden_plain S P hS
  have he : E.couple (pairOfLeaf (unitTwistGarden S P) hnew (coreLeafEquiv S P l)) = .triv :=
    (twistReconstruction_couple_at_leaf S P hS D l).trans (by rw [hl]; exact hq)
  let L := decodedTrivLeaf E hnew (E.garden_decodes hnew) (coreLeafEquiv S P l) he
  refine ⟨L,(inflatedPosition_leaf_twist S P hS D hnil l),?_⟩
  have hp := decodedTrivLeaf_pair E hnew (E.garden_decodes hnew) (coreLeafEquiv S P l) he
  have hv := congrArg (fun z : GLeaf (E.garden hnew).tree => z.1) hp
  apply hv.trans
  change inflatedPosition (unitTwistGarden S P) E.tree
    ((unitTwistGarden S P).pair (coreLeafEquiv S P l)).toNode = _
  exact (congrArg (fun z : GLeaf (unitTwistGarden S P).tree => inflatedPosition (unitTwistGarden S P) E.tree z.toNode)
    (unitTwistGarden_pair S P l)).trans (inflatedPosition_leaf_twist S P hS D hnil (S.pair l))

end WaveTurbulence.LFTwist
