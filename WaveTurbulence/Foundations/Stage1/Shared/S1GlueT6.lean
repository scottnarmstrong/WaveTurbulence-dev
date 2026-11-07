/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.Shared.S1GlueT5
import Mathlib.Tactic

/-!
# Gluing a template regular tree: outside agreement, layers in the tree region, the insertion record
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Stage1
open TTree Reg Reg.Skeleton Twist Links RegRed WaveTurbulence.LFTwist

variable {w : ℕ}

theorem chainNodesSet_not_under_lone {X : RegChain} {ζ : ℤˣ} {a z : Fin w × Path}
    (hz : z ∈ chainNodesSet X ζ a) : ¬ Under (addrExt a X.lonePath) z := by
  unfold chainNodesSet at hz
  rcases Finset.mem_union.mp hz with hz | hz
  · obtain ⟨l, hl, hzl⟩ := (mem_pairEndpoints_iff _ _).mp hz
    have := chain_link_not_below_lone X ζ a l hl
    rcases hzl with rfl | rfl
    · exact fun hh => this.1 ((under_iff_below _ _).mp hh)
    · exact fun hh => this.2 ((under_iff_below _ _).mp hh)
  · exact chain_pairs_not_under_lone X ζ a z hz

namespace GlueT
variable {LM T : LayeredGarden w} {G2 : Garden w} {X : RegChain} {ζ : ℤˣ} {a aT : Fin w × Path}
  {t t' : TTree} {p : ℕ} (h : GlueT LM T G2 X ζ a aT t t' p)
include h

theorem glued_layerAt_of_mem {z : Fin w × Path} (hz : z.2 ∈ (G2.tree z.1).nodes) :
    layerAt h.glued z = glueTAt LM T a aT (addrExt a X.lonePath) z := by
  have : layerAt h.glued z = h.glued.layer ⟨z, hz⟩ := layerAt_of_mem h.glued hz
  exact this

theorem glued_layerAt_not_mem {z : Fin w × Path} (hz : ¬ z.2 ∈ (G2.tree z.1).nodes) :
    layerAt h.glued z = 0 := by
  unfold layerAt
  have hz' : ¬ z.2 ∈ (h.glued.garden.tree z.1).nodes := hz
  simp [hz']

/-- **Inside the tree region the glued garden has the layers of the template.** -/
theorem glued_region {z : Fin w × Path} (hz : InTree a (addrExt a X.lonePath) z) :
    layerAt h.glued z = layerAt T (treePort a aT z) := by
  by_cases hm : z.2 ∈ (G2.tree z.1).nodes
  · rw [h.glued_layerAt_of_mem hm, glueTAt_in _ _ _ _ _ hz]
    rfl
  · rw [h.glued_layerAt_not_mem hm]
    have hm' := mt (h.port_node_iff hz).mpr hm
    unfold layerAt
    simp [hm']

theorem glued_lone : layerAt h.glued (addrExt a X.lonePath) = layerAt T (addrExt aT X.lonePath) := by
  have hn : (addrExt a X.lonePath).2 ∈ (G2.tree (addrExt a X.lonePath).1).nodes :=
    (node_iff_of_subtree h.embG.node h.embG.tree X.lonePath).1.mpr (lonePath_mem_plug X ζ t)
  rw [h.glued_layerAt_of_mem hn, glueTAt_out _ _ _ _ _ (fun hh => hh.2 (under_refl _)), shift_self,
    h.hlone]

theorem glued_out {z : Fin w × Path} :
    layerAt LM z = layerAt h.glued (shiftAddr a (addrExt a X.lonePath) z) := by
  have hz : ¬ InTree a a z := fun hh => hh.2 hh.1
  have hout : ¬ InTree a (addrExt a X.lonePath) (shiftAddr a (addrExt a X.lonePath) z) :=
    out_shift hz
  by_cases hm : z.2 ∈ (LM.garden.tree z.1).nodes
  · have hm' := (h.node z).mp hm
    rw [h.glued_layerAt_of_mem hm', glueTAt_out _ _ _ _ _ hout,
      shift_shift (n := a) (n' := addrExt a X.lonePath) (a := a) h.under_lone hz]
  · have hm' : ¬ (shiftAddr a (addrExt a X.lonePath) z).2 ∈
        (G2.tree (shiftAddr a (addrExt a X.lonePath) z).1).nodes := fun hh => hm ((h.node z).mpr hh)
    rw [h.glued_layerAt_not_mem hm']
    unfold layerAt
    simp [hm]

/-- **Outside agreement of the base and the glued garden (with the move of the subtree).** -/
theorem outAgreeT : OutAgreeT LM h.glued a a (addrExt a X.lonePath) where
  node z _ := h.node z
  leaf z _ := h.leaf z
  layer z _ := h.glued_out
  pair ℓ ℓ' _ he := h.pair ℓ ℓ' he

end GlueT
end WaveTurbulence.Stage1
