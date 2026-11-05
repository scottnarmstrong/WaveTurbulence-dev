/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.LFTwist.ExpandedPlacement
public import WaveTurbulence.Foundations.Molecule.LFTwist.CanonicalUnit

/-! # Source core layers at the actual expanded unit-twist site

The uniform parent inequality below is the guard needed by the collapsed-unit
argument. Its derivation from the named source vine scenarios is separate.
-/

public section
namespace WaveTurbulence.LFTwist
open TTree Reg Reg.Skeleton Twist
variable {w : ℕ} {S : Garden w} (LG : LayeredGarden w) (D : ReconstructionData S)
    (hS : S.IsPlain) (hd : D.Decodes hS LG.garden) (P : CorePlacement S)
    (hq : D.couple (pairOfLeaf S hS P.retained) = .triv)

/-- The paired leaf's actual parent is the inherited source parent's core branch. -/
theorem expandedPlacement_paired_parent :
    GNode.parent (LG.garden.pair (expandedPlacement D hS hd P hq).retained).toNode
      (expandedPlacement D hS hd P hq).paired_nonroot =
        D.decodedCoreBranch hS hd (GNode.parent (S.pair P.retained).toNode P.paired_nonroot) := by
  have hp := decodedTrivLeaf_pair D hS hd P.retained hq
  have hn := inflatedPosition_nonroot S D.tree (S.pair P.retained).toNode P.paired_nonroot
  exact (nodeParent_congr (expandedPlacement D hS hd P hq).paired_nonroot hn
    (congrArg GLeaf.toNode hp)).trans
      (decodedTrivLeaf_parent D hS hd (S.pair P.retained) P.paired_nonroot
        (by simpa only [pairOfLeaf_partner] using hq))

/-- The inherited source guard is exactly the actual parent-layer guard. -/
theorem expandedPlacement_parent_guard
    (hb : inducedPrelayer LG D hS hd P.lower ≤
      inducedPrelayer LG D hS hd (GNode.parent (S.pair P.retained).toNode P.paired_nonroot)) :
    LG.layer (expandedPlacement D hS hd P hq).lower.toNode ≤
      LG.layer (GNode.parent (LG.garden.pair (expandedPlacement D hS hd P hq).retained).toNode
        (expandedPlacement D hS hd P hq).paired_nonroot).toNode := by
  exact hb.trans_eq (congrArg (fun b : GBranch LG.garden.tree => LG.layer b.toNode)
    (expandedPlacement_paired_parent LG D hS hd P hq)).symm

/-- Canonical minimum-parent leaf layers force the required equal lower layer. -/
theorem expandedPlacement_sameLowerLayer {p : ℕ} (hc : LG.CanonCriterion p)
    (hb : inducedPrelayer LG D hS hd P.lower ≤
      inducedPrelayer LG D hS hd (GNode.parent (S.pair P.retained).toNode P.paired_nonroot)) :
    SameLowerLayer LG (expandedPlacement D hS hd P hq) :=
  sameLowerLayer_of_canonical LG _ hc (expandedPlacement_parent_guard LG D hS hd P hq hb)

/-- Source same-tree geometry is retained after inserting all ordinary attachments. -/
theorem expandedPlacement_same_tree
    (hs : P.lower.1.1 = (S.pair P.retained).1.1) :
    (expandedPlacement D hS hd P hq).lower.1.1 =
      (LG.garden.pair (expandedPlacement D hS hd P hq).retained).1.1 := by
  have hp := decodedTrivLeaf_pair D hS hd P.retained hq
  change (D.corePosition P.lower).1 = (LG.garden.pair (decodedTrivLeaf D hS hd P.retained hq)).1.1
  exact (inflatedPosition_index S D.tree P.lower.toNode).trans
    (hs.trans ((inflatedPosition_index S D.tree (S.pair P.retained).toNode).symm.trans
      (congrArg (fun l : GLeaf LG.garden.tree => l.1.1) hp).symm))

end WaveTurbulence.LFTwist
