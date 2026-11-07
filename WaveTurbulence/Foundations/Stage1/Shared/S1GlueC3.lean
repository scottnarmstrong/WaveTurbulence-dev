/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.Shared.S1GlueC2
import Mathlib.Tactic

/-!
# The glued layer function is a layering (couple case): the parent-child condition
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Stage1
open TTree Reg Reg.Skeleton Twist Links RegRed WaveTurbulence.LFTwist

variable {w : ℕ}

namespace GlueC
variable {LN T : LayeredGarden w} {G : Garden w} {Q : RegCpl} {a b aT bT : Fin w × Path} {p : ℕ}
  (h : GlueC LN T G Q a b aT bT p)
include h

theorem glue_a (q : Path) :
    glueAt LN T a b aT bT (addrExt a q) = layerAt T (addrExt aT q) := by
  rw [glueAt_in _ _ _ _ _ _ (Or.inl (under_ext a q)), h.port_a]

theorem glue_b (q : Path) :
    glueAt LN T a b aT bT (addrExt b q) = layerAt T (addrExt bT q) := by
  rw [glueAt_in _ _ _ _ _ _ (Or.inr (under_ext b q)), h.port_b]

/-- Inside one region the template's layers are monotone downwards. -/
theorem region_child {rT : Fin w × Path} {Qt : TTree}
    (hrT : rT.2 ∈ (T.garden.tree rT.1).nodes) (hrtT : (T.garden.tree rT.1).subtreeAt rT.2 = Qt)
    (q : Path) (i : Fin 3) (hc : (q ++ [i]) ∈ Qt.nodes) :
    layerAt T (addrExt rT (q ++ [i])) ≤ layerAt T (addrExt rT q) := by
  have hq : q ∈ Qt.nodes := by
    have := TTree.dropLast_mem_nodes _ hc
    simpa using this
  refine layerAt_le_of_under T ?_ ?_ ?_
  · exact (node_iff_of_subtree hrT hrtT q).1.mpr hq
  · exact (node_iff_of_subtree hrT hrtT (q ++ [i])).1.mpr hc
  · exact (under_ext_iff rT q (q ++ [i])).mpr (List.prefix_append _ _)

end GlueC
end WaveTurbulence.Stage1
