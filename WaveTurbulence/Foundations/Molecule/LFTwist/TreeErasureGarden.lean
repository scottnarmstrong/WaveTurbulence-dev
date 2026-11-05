/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.LFTwist.TreeErasureForest
public import WaveTurbulence.Foundations.Molecule.LFTwist.TreeErasurePairs
public import WaveTurbulence.Foundations.Molecule.LFTwist.PlainGardenExt
public import WaveTurbulence.Foundations.Molecule.CoreTwistForest

/-! # General paired-tree collapse is the exact erased reconstruction garden -/

public section
namespace WaveTurbulence.LFTwist
open TTree Reg Reg.Skeleton

/-- The actual relative collapse path is the regular tree's actual lone path. -/
theorem reconstruction_collapse_path {w : ℕ} {S : Garden w} (D : ReconstructionData S)
    (hS : S.IsPlain) (b : GBranch S.tree) :
    (Comb.collapseDataOfDesc (D.decoded_chain_isSubPairedTree hS (D.garden_decodes hS) b).1).path =
      (D.tree b).lonePath := by
  have he := collapseData_frame (D.decoded_chain_isSubPairedTree hS (D.garden_decodes hS) b).1
  have hp := congrArg (fun z : Address w => z.2) he
  change (inflatedPosition S D.tree b.toNode).2 ++ (D.tree b).lonePath =
    (inflatedPosition S D.tree b.toNode).2 ++ _ at hp
  exact (List.append_cancel_left hp).symm

/-- The concrete collapse and erasure agree as actual garden structures,
including every surviving partner and all original root signatures. -/
theorem eraseTree_collapse_garden {w : ℕ} {S : Garden w} (D : ReconstructionData S)
    (hS : S.IsPlain) (b : GBranch S.tree) :
    collapsePairedTreeGarden (D.decoded_chain_isSubPairedTree hS (D.garden_decodes hS) b) =
      (D.eraseTree b).garden hS := by
  let E := D.eraseTree b
  let hc := D.decoded_chain_isSubPairedTree hS (D.garden_decodes hS) b
  let ht := eraseTree_collapse_forest D hS b
  let C := collapsePairedTreeGarden hc
  let castLeaf := Twist.forestLeafCast ht.symm
  let emb : GLeaf (E.garden hS).tree → GLeaf (D.garden hS).tree :=
    fun l => pairedTreeLeafEmbedding hc (castLeaf l)
  let A := inflatedPosition S E.tree b.toNode
  let f := stretch A (D.tree b).lonePath
  have hv (l : GLeaf (E.garden hS).tree) : (emb l).1 = f l.1 := by
    change stretch (inflatedPosition S D.tree b.toNode)
      (Comb.collapseDataOfDesc hc.1).path l.1 = _
    rw [reconstruction_collapse_path D hS b]
    exact congrArg (fun z => stretch z (D.tree b).lonePath l.1) (D.eraseTree_position_at b).symm
  have hs (l : GLeaf (E.garden hS).tree) :
      nodeSign (D.garden hS).sig (emb l).1 = nodeSign (E.garden hS).sig l.1 :=
    (pairedTreeLeafEmbedding_sign hc (castLeaf l)).symm
  have hp (l : GLeaf (E.garden hS).tree) :
      (D.garden hS).pair (emb l) = emb ((E.garden hS).pair l) :=
    pairEmbedding_of_sourcePairs (D.garden hS) (E.garden hS) (D.garden_plain hS) (E.garden_plain hS)
      emb f hv hs (eraseTree_background_pair_inclusion D hS b) l
  apply plainGarden_eq_of_pair_addresses (collapsePairedTreeGarden_plain hc (D.garden_plain hS))
    (E.garden_plain hS) rfl ht
  intro l m he
  have hm : castLeaf m = l := Subtype.ext he.symm
  have hemb : emb m = pairedTreeLeafEmbedding hc l := congrArg (pairedTreeLeafEmbedding hc) hm
  have heq : pairedTreeLeafEmbedding hc (C.pair l) = emb ((E.garden hS).pair m) :=
    (collapsePairedTreeGarden_pair hc l).trans ((congrArg (D.garden hS).pair hemb).symm.trans (hp m))
  have hleaves : C.pair l = castLeaf ((E.garden hS).pair m) :=
    (pairedTreeLeafEmbedding hc).injective heq
  exact congrArg (fun n : GLeaf C.tree => n.1) hleaves

/-- The exact erased assignment decodes the concrete collapse in any actual
ambient garden decoded by D. This is the general tree counterpart of C3's
couple-collapse decoding theorem. -/
theorem eraseTree_collapse_decodes {w : ℕ} {S G : Garden w} (D : ReconstructionData S)
    (hS : S.IsPlain) (hd : D.Decodes hS G) (b : GBranch S.tree) :
    (D.eraseTree b).Decodes hS
      (collapsePairedTreeGarden (D.decoded_chain_isSubPairedTree hS hd b)) := by
  have he : G = D.garden hS := rawOfGarden_injective_plain hd.1 (D.garden_plain hS)
    (hd.2.symm.trans (D.garden_raw hS).symm)
  subst G
  rw [eraseTree_collapse_garden D hS b]
  exact (D.eraseTree b).garden_decodes hS

end WaveTurbulence.LFTwist
