/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.Shared.S1GlueT1
import Mathlib.Tactic

/-!
# Glued tree layers: the tree region of the garden and of the template correspond
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Stage1
open TTree Reg Reg.Skeleton Twist Links RegRed WaveTurbulence.LFTwist

variable {w : ℕ}

/-- Relative translation of the tree region below `a` to the one below `aT`. -/
@[expose] def treePort (a aT : Fin w × Path) (z : Fin w × Path) : Fin w × Path :=
  addrExt aT (z.2.drop a.2.length)

theorem treePort_ext (a aT : Fin w × Path) (q : Path) : treePort a aT (addrExt a q) = addrExt aT q := by
  simp [treePort, addrExt]

theorem treePort_respects (a aT : Fin w × Path) : RespectsAt (treePort a aT) a := by
  intro q
  rw [treePort_ext]
  simp [treePort, addrExt]

theorem treePort_self (a aT : Fin w × Path) : treePort a aT a = aT := by
  simp [treePort, addrExt]

namespace GlueT
variable {LM T : LayeredGarden w} {G2 : Garden w} {X : RegChain} {ζ : ℤˣ} {a aT : Fin w × Path}
  {t t' : TTree} {p : ℕ} (h : GlueT LM T G2 X ζ a aT t t' p)
include h

theorem chainNodes_port : chainNodesSet X ζ aT = (chainNodesSet X ζ a).image (treePort a aT) := by
  have := chainNodesSet_map X ζ (treePort a aT) a (treePort_respects a aT)
  rwa [treePort_self] at this

theorem port_node_iff {z : Fin w × Path} (hz : InTree a (addrExt a X.lonePath) z) :
    z.2 ∈ (G2.tree z.1).nodes ↔ (treePort a aT z).2 ∈ (T.garden.tree (treePort a aT z).1).nodes := by
  obtain ⟨q, rfl⟩ := under_of_addrExt hz.1
  rw [treePort_ext]
  have hnl : ¬ Under (addrExt aT X.lonePath) (addrExt aT q) := by
    intro hu
    exact hz.2 (by
      rw [under_ext_iff] at hu ⊢
      exact hu)
  constructor
  · intro hn
    have hz1 : addrExt a q ∈ chainNodesSet X ζ a := h.embG.mem_chainNodesSet hn hz
    have : addrExt aT q ∈ chainNodesSet X ζ aT := by
      rw [h.chainNodes_port, ← treePort_ext a aT q]
      exact Finset.mem_image_of_mem _ hz1
    exact h.embT.mem_nodes this
  · intro hn
    have hz1 : addrExt aT q ∈ chainNodesSet X ζ aT := h.embT.mem_chainNodesSet hn ⟨under_ext aT q, hnl⟩
    rw [h.chainNodes_port] at hz1
    obtain ⟨z', hz', hze⟩ := Finset.mem_image.mp hz1
    obtain ⟨q', rfl⟩ := under_of_addrExt (chainNodesSet_under hz')
    rw [treePort_ext] at hze
    have hq : q' = q := by
      have := congrArg Prod.snd hze
      simpa [addrExt] using this
    subst hq
    exact h.embG.mem_nodes hz'

end GlueT
end WaveTurbulence.Stage1
