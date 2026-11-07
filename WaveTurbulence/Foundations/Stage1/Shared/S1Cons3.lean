/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.Shared.S1Cons2
import Mathlib.Tactic

/-!
# Glue specification: the tree stage
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Stage1
open TTree Reg Reg.Skeleton Twist Links RegRed WaveTurbulence.LFTwist

variable {w p : ℕ} {kind : Bool} {LG : LayeredGarden w}

namespace GlueSpec
variable {s : LFSource p kind LG} {ε : Bool} (g : GlueSpec s ε)

/-- The final data. -/
@[expose] noncomputable def FD : ReconstructionData (s.chosen ε) := s.finalData ε g.X g.Q g.hX g.hQ

theorem eraseFD : g.FD.eraseTree (s.branches ε s.placement.lower) = s.midData ε g.Q g.hQ :=
  eraseTree_final _ _ _ _

theorem FD_tree_lower : g.FD.tree (s.branches ε s.placement.lower) = g.X := Function.update_self _ _ _

theorem pos_FD : inflatedPosition (s.chosen ε) g.FD.tree (s.branches ε s.placement.lower).toNode =
    inflatedPosition (s.chosen ε) (s.midData ε g.Q g.hQ).tree (s.branches ε s.placement.lower).toNode := by
  have := (g.FD.eraseTree_position_at (s.branches ε s.placement.lower)).symm
  rw [g.eraseFD] at this
  exact this

theorem lower_not_region :
    ¬ InRegion (inflatedPosition (s.chosen ε) (s.midData ε g.Q g.hQ).tree
        ((s.pairs ε s.exceptional).firstLeaf (s.chosen_plain ε)).toNode)
      (inflatedPosition (s.chosen ε) (s.midData ε g.Q g.hQ).tree
        ((s.pairs ε s.exceptional).secondLeaf (s.chosen_plain ε)).toNode)
      (inflatedPosition (s.chosen ε) (s.midData ε g.Q g.hQ).tree (s.branches ε s.placement.lower).toNode) := by
  rintro (h | h)
  · exact leaf_not_above_branch (s.chosen ε).tree _ _
      ((inflatedPosition_below_iff _ _ _ _).mp ((under_iff_below_addr _ _).mp h))
  · exact leaf_not_above_branch (s.chosen ε).tree _ _
      ((inflatedPosition_below_iff _ _ _ _).mp ((under_iff_below_addr _ _).mp h))

theorem lower_mem_N : (inflatedPosition (s.chosen ε) (s.midData ε g.Q g.hQ).tree
    (s.branches ε s.placement.lower).toNode).2 ∈
      ((s.base ε).garden.tree (inflatedPosition (s.chosen ε) (s.midData ε g.Q g.hQ).tree
        (s.branches ε s.placement.lower).toNode).1).nodes :=
  ((s.baseData ε).decodedNode (s.chosen_plain ε) (s.base_decodes ε) (s.branches ε s.placement.lower).toNode).2

theorem lower_mem_glued1 : (inflatedPosition (s.chosen ε) (s.midData ε g.Q g.hQ).tree
    (s.branches ε s.placement.lower).toNode).2 ∈
      (g.glued1.garden.tree (inflatedPosition (s.chosen ε) (s.midData ε g.Q g.hQ).tree
        (s.branches ε s.placement.lower).toNode).1).nodes :=
  ((s.midData ε g.Q g.hQ).decodedNode (s.chosen_plain ε) ((s.midData ε g.Q g.hQ).garden_decodes _)
    (s.branches ε s.placement.lower).toNode).2

theorem parAt_lower : parAt g.glued1 p (inflatedPosition (s.chosen ε) (s.midData ε g.Q g.hQ).tree
    (s.branches ε s.placement.lower).toNode) = parAt (s.base ε) p (inflatedPosition (s.chosen ε)
      (s.baseData ε).tree (s.branches ε s.placement.lower).toNode) :=
  (g.glueC.outAgree.parAt_eq_out g.lower_not_region g.lower_mem_N g.lower_mem_glued1).symm

theorem layer_lower : layerAt g.glued1 (inflatedPosition (s.chosen ε) (s.midData ε g.Q g.hQ).tree
    (s.branches ε s.placement.lower).toNode) = layerAt (s.base ε) (inflatedPosition (s.chosen ε)
      (s.baseData ε).tree (s.branches ε s.placement.lower).toNode) :=
  (g.glueC.glued_out g.lower_not_region).symm

end GlueSpec
end WaveTurbulence.Stage1
