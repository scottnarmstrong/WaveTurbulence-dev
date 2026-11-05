/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.LFTwist.ReconstructedCommon
public import WaveTurbulence.Foundations.Molecule.LFTwist.ExpandedPlacement
public import WaveTurbulence.Foundations.Molecule.TwistForestInvolution

/-! # Reconstruction commutes with the literal unit-twist forest surgery -/

public section
namespace WaveTurbulence.LFTwist
open TTree Reg Reg.Skeleton Twist Links
variable {w : ℕ} (S : Garden w) (P : CorePlacement S) (hS : S.IsPlain) (D : ReconstructionData S)

private theorem expanded_lower_address (hnil : D.tree P.lower = .nil)
    (hq : D.couple (pairOfLeaf S hS P.retained) = .triv) :
    (expandedPlacement D hS (D.garden_decodes hS) P hq).lower.1 =
      (reconstructedLowerHole S P hS D).1 := by
  change addrExt (inflatedPosition S D.tree P.lower.toNode) (D.tree P.lower).lonePath = _
  rw [hnil]
  simp only [RegChain.lonePath, addrExt_nil]
  exact inflatedPosition_eq_rawSourcePosition D P.lower.toNode

private theorem expanded_paired_address
    (hq : D.couple (pairOfLeaf S hS P.retained) = .triv) :
    (pairedHole (D.garden hS) (expandedPlacement D hS (D.garden_decodes hS) P hq)).1 =
      (reconstructedPairedHole S P hS D hq).1 := by
  change ((D.garden hS).pair (decodedTrivLeaf D hS (D.garden_decodes hS) P.retained hq)).1 = _
  rw [decodedTrivLeaf_pair]
  exact inflatedPosition_eq_rawSourcePosition D (S.pair P.retained).toNode

/-- Erasing the actual lower crown gives the raw inflation of the source common forest. -/
theorem expanded_commonForest (hnil : D.tree P.lower = .nil)
    (hq : D.couple (pairOfLeaf S hS P.retained) = .triv) :
    commonForest (D.garden hS) (expandedPlacement D hS (D.garden_decodes hS) P hq).lower =
      reconstructedCommonForest S P hS D := by
  let collapse (F : Fin w → TTree) (a : Address w) :=
    Function.update F a.1 (Comb.collapseAt (F a.1) a.2)
  have he := congrArg₂ collapse (reconstruction_old_common_factor S P hS D)
    (expanded_lower_address S P hS D hnil hq)
  exact he.trans (collapse_insertLeaf _ _ _)

/-- The actual lower crown is exactly the inflated source crown. -/
theorem expanded_lowerCrown (hnil : D.tree P.lower = .nil)
    (hq : D.couple (pairOfLeaf S hS P.retained) = .triv) :
    lowerCrown (D.garden hS) (expandedPlacement D hS (D.garden_decodes hS) P hq).lower =
      inflateTreeAt S.sig (branchLookup D) (leafLookup D hS) (lowerCrown S P.lower) P.lower.1 := by
  let extract (F : Fin w → TTree) (a : Address w) := Comb.subtree (F a.1) a.2
  have he := congrArg₂ extract (reconstruction_old_common_factor S P hS D)
    (expanded_lower_address S P hS D hnil hq)
  have hs := Mole.spliceNodeSubtree_spec (D.garden hS)
    (expandedPlacement D hS (D.garden_decodes hS) P hq).lower.toNode
  exact Option.some.inj (hs.symm.trans (he.trans (subtree_insertLeaf _ _ _)))

/-- With both exceptional attachments erased, reconstruction and the actual
unit twist have literally equal ordered forests. No output canonicity is assumed. -/
theorem reconstructed_unit_forest (hnil : D.tree P.lower = .nil)
    (hq : D.couple (pairOfLeaf S hS P.retained) = .triv) :
    (twistReconstruction S P hS D).forest (unitTwistGarden_plain S P hS) =
      (unitTwistGarden (D.garden hS) (expandedPlacement D hS (D.garden_decodes hS) P hq)).tree := by
  rw [reconstruction_new_common_factor S P hS D hnil hq]
  symm
  exact insertLeaf_congr_of_address (expanded_commonForest S P hS D hnil hq)
    (pairedHole (D.garden hS) (expandedPlacement D hS (D.garden_decodes hS) P hq))
    (reconstructedPairedHole S P hS D hq) (expanded_paired_address S P hS D hq) _ _
    (congrArg (switchFree P.keep) (expanded_lowerCrown S P hS D hnil hq))

end WaveTurbulence.LFTwist
