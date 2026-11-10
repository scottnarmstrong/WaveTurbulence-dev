/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.Shared.S1GlueC6
import Mathlib.Tactic

/-!
# The glued garden: outside agreement and layers inside the regions
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

theorem glued_layerAt_of_mem {z : Fin w × Path} (hz : z.2 ∈ (G.tree z.1).nodes) :
    layerAt h.glued z = glueAt LN T a b aT bT z := by
  have : layerAt h.glued z = h.glued.layer ⟨z, hz⟩ := layerAt_of_mem h.glued hz
  exact this

theorem glued_layerAt_not_mem {z : Fin w × Path} (hz : ¬ z.2 ∈ (G.tree z.1).nodes) :
    layerAt h.glued z = 0 := by
  unfold layerAt
  have hz' : ¬ z.2 ∈ (h.glued.garden.tree z.1).nodes := hz
  simp [hz']

/-- Region nodes correspond under the translation. -/
theorem region_node_iff {z : Fin w × Path} (hz : InRegion a b z) :
    z.2 ∈ (G.tree z.1).nodes ↔ (couplePort a b aT bT z).2 ∈ (T.garden.tree (couplePort a b aT bT z).1).nodes := by
  rcases hz with hz | hz
  · obtain ⟨q, rfl⟩ := under_of_addrExt hz
    rw [h.port_a]
    exact (node_iff_of_subtree h.embM.nodeA h.embM.treeA q).1.trans
      (node_iff_of_subtree h.embT.nodeA h.embT.treeA q).1.symm
  · obtain ⟨q, rfl⟩ := under_of_addrExt hz
    rw [h.port_b]
    exact (node_iff_of_subtree h.embM.nodeB h.embM.treeB q).1.trans
      (node_iff_of_subtree h.embT.nodeB h.embT.treeB q).1.symm

/-- **Inside the regions the glued garden has the layers of the template.** -/
theorem glued_region {z : Fin w × Path} (hz : InRegion a b z) :
    layerAt h.glued z = layerAt T (couplePort a b aT bT z) := by
  by_cases hm : z.2 ∈ (G.tree z.1).nodes
  · rw [h.glued_layerAt_of_mem hm, glueAt_in _ _ _ _ _ _ hz]
  · rw [h.glued_layerAt_not_mem hm]
    have hm' := mt (h.region_node_iff hz).mpr hm
    unfold layerAt
    simp [hm']

theorem glued_out {z : Fin w × Path} (hz : ¬ InRegion a b z) :
    layerAt LN z = layerAt h.glued z := by
  by_cases hm : z.2 ∈ (G.tree z.1).nodes
  · rw [h.glued_layerAt_of_mem hm, glueAt_out _ _ _ _ _ _ hz]
  · rw [h.glued_layerAt_not_mem hm]
    have hm' : ¬ z.2 ∈ (LN.garden.tree z.1).nodes := fun hh => hm ((h.node z hz).mpr hh)
    unfold layerAt
    simp [hm']

/-- **Outside agreement of the base and the glued garden.** -/
theorem outAgree : OutAgree LN h.glued a b where
  node z hz := (h.node z hz).symm
  leaf z hz := (h.leaf z hz).symm
  layer z hz := h.glued_out hz
  pair ℓ ℓ' hz he := by
    have := h.pair ℓ' ℓ (by rw [← he]; exact hz) he.symm
    exact this.symm

end GlueC
end WaveTurbulence.Stage1
