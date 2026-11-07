/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.Shared.S1GlueT3
import Mathlib.Tactic

/-!
# Glued tree layers: paired leaves have equal layers; the glued layered garden
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Stage1
open TTree Reg Reg.Skeleton Twist Links RegRed WaveTurbulence.LFTwist

variable {w : ℕ}

namespace GlueT
variable {LM T : LayeredGarden w} {G2 : Garden w} {X : RegChain} {ζ : ℤˣ} {a aT : Fin w × Path}
  {t t' : TTree} {p : ℕ} (h : GlueT LM T G2 X ζ a aT t t' p)
include h

theorem pairs_port : X.pairsAt ζ aT =
    (X.pairsAt ζ a).map (fun r => (treePort a aT r.1, treePort a aT r.2)) := by
  have := chain_pairsAt_map_local X (treePort a aT) a (treePort_respects a aT) ζ
  rwa [treePort_self] at this

theorem pair_in_tree (ℓ : GLeaf G2.tree) (hℓ : InTree a (addrExt a X.lonePath) ℓ.1) :
    glueTAt LM T a aT (addrExt a X.lonePath) ℓ.1 =
      glueTAt LM T a aT (addrExt a X.lonePath) (G2.pair ℓ).1 := by
  obtain ⟨r, hr, hrl⟩ := h.embG.partner ℓ hℓ
  have hpin := h.embG.pair_region ℓ hℓ
  have hr1 : r.1 ∈ pairEndpoints (X.pairsAt ζ a) :=
    (mem_pairEndpoints_iff _ _).mpr ⟨r, hr, Or.inl rfl⟩
  have hr2 : r.2 ∈ pairEndpoints (X.pairsAt ζ a) :=
    (mem_pairEndpoints_iff _ _).mpr ⟨r, hr, Or.inr rfl⟩
  have hr' : (treePort a aT r.1, treePort a aT r.2) ∈ X.pairsAt ζ aT := by
    rw [h.pairs_port]
    exact List.mem_map.mpr ⟨r, hr, rfl⟩
  have hr1' : treePort a aT r.1 ∈ pairEndpoints (X.pairsAt ζ aT) :=
    (mem_pairEndpoints_iff _ _).mpr ⟨_, hr', Or.inl rfl⟩
  let ℓT : GLeaf T.garden.tree := ⟨treePort a aT r.1, h.embT.leaf_of_mem hr1'⟩
  have hpT : (T.garden.pair ℓT).1 = treePort a aT r.2 := h.embT.pairs _ hr' ℓT rfl
  have hr2' : treePort a aT r.2 ∈ pairEndpoints (X.pairsAt ζ aT) :=
    (mem_pairEndpoints_iff _ _).mpr ⟨_, hr', Or.inr rfl⟩
  let ℓT' : GLeaf T.garden.tree := ⟨treePort a aT r.2, h.embT.leaf_of_mem hr2'⟩
  have hpair : T.garden.pair ℓT = ℓT' := Subtype.ext hpT
  have hT : layerAt T (treePort a aT r.1) = layerAt T (treePort a aT r.2) := by
    have e1 := layerAt_node T ℓT.toNode
    have e2 := layerAt_node T ℓT'.toNode
    have e3 := T.isLayering.2 ℓT
    rw [hpair] at e3
    exact e1.trans (e3.trans e2.symm)
  rw [glueTAt_in _ _ _ _ _ hℓ, glueTAt_in _ _ _ _ _ hpin]
  rcases hrl with ⟨e1, e2⟩ | ⟨e1, e2⟩
  · rw [e1, e2]; exact hT
  · rw [e1, e2]; exact hT.symm

theorem pair_out (ℓ : GLeaf G2.tree) (hℓ : ¬ InTree a (addrExt a X.lonePath) ℓ.1) :
    glueTAt LM T a aT (addrExt a X.lonePath) ℓ.1 =
      glueTAt LM T a aT (addrExt a X.lonePath) (G2.pair ℓ).1 := by
  have hpout := h.embG.pair_out ℓ hℓ
  have hleaf : (shiftAddr (addrExt a X.lonePath) a ℓ.1).2 ∈
      (LM.garden.tree (shiftAddr (addrExt a X.lonePath) a ℓ.1).1).leaves := by
    rw [h.leaf, h.shift_back hℓ]; exact ℓ.2
  let ℓ0 : GLeaf LM.garden.tree := ⟨shiftAddr (addrExt a X.lonePath) a ℓ.1, hleaf⟩
  have hp := h.pair ℓ0 ℓ (h.shift_back hℓ)
  rw [glueTAt_out _ _ _ _ _ hℓ, glueTAt_out _ _ _ _ _ hpout]
  have e : shiftAddr (addrExt a X.lonePath) a (G2.pair ℓ).1 = (LM.garden.pair ℓ0).1 := by
    rw [← hp]
    exact shift_shift (n := a) (n' := addrExt a X.lonePath) (a := a) h.under_lone (fun hh => hh.2 hh.1)
  rw [e]
  have e1 := layerAt_node LM ℓ0.toNode
  have e2 := layerAt_node LM (LM.garden.pair ℓ0).toNode
  have e3 := LM.isLayering.2 ℓ0
  exact e1.trans (e3.trans e2.symm)

theorem isLayering : IsLayering G2 (fun n => glueTAt LM T a aT (addrExt a X.lonePath) n.1) := by
  refine ⟨fun c i => h.child_le c i, fun ℓ => ?_⟩
  by_cases hℓ : InTree a (addrExt a X.lonePath) ℓ.1
  · exact h.pair_in_tree ℓ hℓ
  · exact h.pair_out ℓ hℓ

/-- The glued layered garden (tree case). -/
@[expose] noncomputable def glued : LayeredGarden w :=
  ⟨G2, fun n => glueTAt LM T a aT (addrExt a X.lonePath) n.1, h.isLayering⟩

end GlueT
end WaveTurbulence.Stage1
