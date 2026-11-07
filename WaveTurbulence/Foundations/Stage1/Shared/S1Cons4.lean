/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.Shared.S1Cons3
import Mathlib.Tactic

/-!
# Glue specification: the tree reinsertion record and the glued output
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Stage1
open TTree Reg Reg.Skeleton Twist Links RegRed WaveTurbulence.LFTwist

variable {w p : ℕ} {kind : Bool} {LG : LayeredGarden w}

namespace GlueSpec
variable {s : LFSource p kind LG} {ε : Bool} (g : GlueSpec s ε)

theorem glueT : GlueT g.glued1 g.To (g.FD.garden (s.chosen_plain ε)) (g.FD.tree (s.branches ε s.placement.lower))
    (nodeSign (s.chosen ε).sig (s.branches ε s.placement.lower).1)
    (inflatedPosition (s.chosen ε) g.FD.tree (s.branches ε s.placement.lower).toNode) g.aT2
    (node3 (fun i => g.FD.inflateNode (s.chosen_plain ε) ((s.branches ε s.placement.lower).child i))) g.t' p := by
  have hLM : g.glued1.garden = (g.FD.eraseTree (s.branches ε s.placement.lower)).garden (s.chosen_plain ε) := by
    rw [g.eraseFD]; rfl
  refine glueT_ofData g.FD (s.chosen_plain ε) (s.branches ε s.placement.lower) g.glued1 g.To hLM g.aT2 g.t' p
    ?_ ?_ ?_ g.hpo
  · rw [g.FD_tree_lower]; exact g.embX
  · rw [g.pos_FD, g.parAt_lower]; exact g.hpl
  · rw [g.FD_tree_lower, g.pos_FD, g.layer_lower]; exact g.hlone

/-- The glued layered garden after both reinsertions. -/
@[expose] noncomputable def glued2 : LayeredGarden w := g.glueT.glued

theorem glued2_garden : g.glued2.garden = g.FD.garden (s.chosen_plain ε) := rfl

theorem treeInsertion_aux :
    CoherentTreeInsertion p g.glued1 g.glued2
      (inflatedPosition (s.chosen ε) (s.midData ε g.Q g.hQ).tree (s.branches ε s.placement.lower).toNode)
      (nodeSign (s.chosen ε).sig (s.branches ε s.placement.lower).1)
      (node3 (fun i => g.FD.inflateNode (s.chosen_plain ε) ((s.branches ε s.placement.lower).child i))) g.X := by
  refine cti_congr g.pos_FD g.FD_tree_lower (g.glueT.insertion ?_ ?_ ?_ ?_)
  · rw [g.FD_tree_lower]; exact g.patX
  · rw [g.FD_tree_lower]; exact g.hX
  · rfl
  · rw [g.pos_FD]
    exact ((s.midData ε g.Q g.hQ).decodedNode_sign (s.chosen_plain ε) ((s.midData ε g.Q g.hQ).garden_decodes _)
      (s.branches ε s.placement.lower).toNode)

end GlueSpec
end WaveTurbulence.Stage1
