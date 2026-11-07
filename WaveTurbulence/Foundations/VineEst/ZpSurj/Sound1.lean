/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.ZpSurj.Geo4

/-! # ZP-SURJ soundness: layers of an arbitrary LF construction on its exceptional couple -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.ZpSurj
open TTree Reg Reg.Skeleton Twist Links RegRed WaveTurbulence.LFTwist WaveTurbulence.Stage1

variable {w p : ℕ} {kind : Bool} {LG : LayeredGarden w} {s : LFSource p kind LG} {ε : Bool}
  (con : LFConstruction s ε)

/-- The mid layered garden of a construction. -/
@[expose] noncomputable def conMid : LayeredGarden w :=
  layeredReconstruction (s.midData ε con.newCouple con.couple_wf) (s.chosen_plain ε) con.midLayer con.mid_isLayering

theorem con_collapse :
    collapsePairedTreeLayered con.output
      (con.data.decoded_chain_isSubPairedTree (s.chosen_plain ε) (con.data.garden_decodes _)
        (s.branches ε s.placement.lower)) = conMid con :=
  collapse_insert_tree' con.data (s.chosen_plain ε) con.output (conMid con) (con.data.garden_decodes _)
    (s.branches ε s.placement.lower) (s.midData ε con.newCouple con.couple_wf)
    (eraseTree_final con.newTree con.newCouple con.tree_wf con.couple_wf) con.newTree (Function.update_self _ _ _)
    ((s.midData ε con.newCouple con.couple_wf).garden_decodes _) con.treeInsertion.oldEmbedding
    con.treeInsertion.outside

theorem con_layer_couple (i : Fin 2) (r : Path) :
    layerAt con.output (addrExt (coupleRoot con.data (s.chosen_plain ε) (s.pairs ε s.exceptional) i) r) =
      layerAt (conMid con) (addrExt (coupleRoot (s.midData ε con.newCouple con.couple_wf) (s.chosen_plain ε)
        (s.pairs ε s.exceptional) i) r) := by
  have h1 := te1_couple con.output con.data (s.chosen_plain ε) (con.data.garden_decodes _)
    (s.branches ε s.placement.lower) (s.pairs ε s.exceptional) i r
  have h2 := congrArg (fun L => layerAt L (addrExt (coupleRoot (con.data.eraseTree (s.branches ε s.placement.lower))
    (s.chosen_plain ε) (s.pairs ε s.exceptional) i) r)) (con_collapse con)
  have h3 := eraseTree_final (s := s) (ε := ε) con.newTree con.newCouple con.tree_wf con.couple_wf
  have h4 : con.data.eraseTree (s.branches ε s.placement.lower) = s.midData ε con.newCouple con.couple_wf := h3
  refine h1.trans (h2.trans ?_)
  rw [h4]

end WaveTurbulence.ZpSurj
