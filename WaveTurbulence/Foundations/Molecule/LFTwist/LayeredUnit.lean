/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.TwistDecorations
public import WaveTurbulence.Foundations.Molecule.TwistDecorationRoots
public import WaveTurbulence.Foundations.WaveB.Lemmas

/-! # The actual unit twist with unchanged node layers

TARGET lftwistprop L1485–L1487, after collapsing the two coherent
exceptional attachments: the lower branch and its retained leaf have
the same layer. This suffices for the literal subtree exchange to carry
an actual layering. Canonicity is proved separately.
-/

public section
namespace WaveTurbulence.LFTwist
open TTree Twist
variable {w : ℕ} (LG : LayeredGarden w) (P : CorePlacement LG.garden)

/-- The source collapsed equal-layer condition at the retained child. -/
@[expose] def SameLowerLayer : Prop := LG.layer P.lower.toNode = LG.layer P.retained.toNode

/-- The literal node-layer transport is an actual layering after the surgery. -/
theorem unitTwist_isLayering (he : SameLowerLayer LG P) :
    IsLayering (unitTwistGarden LG.garden P) (twistNodeLabels LG.garden P LG.layer) := by
  constructor
  · intro b i
    obtain ⟨b,rfl⟩ := (coreBranchEquiv LG.garden P).surjective b
    by_cases hb : b = P.lower
    · subst b
      have hc := twistNodeLabels_lower_child LG.garden P LG.layer i
      have hb := twistNodeLabels_lower LG.garden P LG.layer
      have hm : (if i = P.keep then LG.layer P.lower.toNode else LG.layer (P.lower.child (freeSwap P.keep i))) ≤
          LG.layer P.retained.toNode := by
        split
        · exact he.le
        · exact (LG.isLayering.1 P.lower (freeSwap P.keep i)).trans_eq he
      exact hc.trans_le (hm.trans_eq hb.symm)
    · exact (twistNodeLabels_other_child LG.garden P LG.layer (LG.isLayering.2 P.retained) b hb i).trans_le
        ((LG.isLayering.1 b i).trans_eq (twistNodeLabels_branch LG.garden P LG.layer b hb).symm)
  · exact twistNodeLabels_leaf_pairs LG.garden P LG.layer LG.isLayering.2

/-- The actual layered unit twist used after the two coherent collapses. -/
@[expose] noncomputable def unitLayerTwist (he : SameLowerLayer LG P) : LayeredGarden w where
  garden := unitTwistGarden LG.garden P
  layer := twistNodeLabels LG.garden P LG.layer
  isLayering := unitTwist_isLayering LG P he

/-- All corresponding branching nodes keep their source layer, including the lower joint. -/
theorem unitLayerTwist_branch (he : SameLowerLayer LG P) (b : GBranch LG.garden.tree) :
    (unitLayerTwist LG P he).layer (coreBranchEquiv LG.garden P b).toNode = LG.layer b.toNode := by
  by_cases hb : b = P.lower
  · subst b
    exact (twistNodeLabels_lower LG.garden P LG.layer).trans he.symm
  · exact twistNodeLabels_branch LG.garden P LG.layer b hb

/-- All corresponding leaves keep their source layer. -/
theorem unitLayerTwist_leaf (he : SameLowerLayer LG P) (l : GLeaf LG.garden.tree) :
    (unitLayerTwist LG P he).layer (coreLeafEquiv LG.garden P l).toNode = LG.layer l.toNode := by
  have h := twistNodeLabels_leaf LG.garden P LG.layer l
  by_cases hl : l = P.retained ∨ l = LG.garden.pair P.retained
  · rcases hl with hl | hl
    · subst l
      exact h.trans ((ite_eq_left (Or.inl rfl)).trans he)
    · subst l
      exact h.trans ((ite_eq_left (Or.inr rfl)).trans (he.trans (LG.isLayering.2 P.retained)))
  · exact h.trans (ite_eq_right hl)

/-- The source statement that every corresponding node has the same layer. -/
theorem unitLayerTwist_node (he : SameLowerLayer LG P) (n : GNode LG.garden.tree) :
    (unitLayerTwist LG P he).layer (naiveNodeEquiv LG.garden P n) = LG.layer n := by
  obtain ⟨p,rfl⟩ := (nodePieceEquiv LG.garden.tree).surjective n
  cases p with
  | inl b =>
    exact (congrArg (unitLayerTwist LG P he).layer (naiveNodeEquiv_branch LG.garden P b)).trans
      (unitLayerTwist_branch LG P he b)
  | inr l =>
    exact (congrArg (unitLayerTwist LG P he).layer (naiveNodeEquiv_leaf LG.garden P l)).trans
      (unitLayerTwist_leaf LG P he l)

end WaveTurbulence.LFTwist
