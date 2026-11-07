/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.Shared.S1GlueT6
import Mathlib.Tactic

/-!
# Gluing a template regular tree: the coherent tree insertion record
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Stage1
open TTree Reg Reg.Skeleton Twist Links RegRed WaveTurbulence.LFTwist

variable {w : ℕ}

theorem treePattern_map {LG LG' : LayeredGarden w} (f : (Fin w × Path) → (Fin w × Path))
    (X : RegChain) (ζ : ℤˣ) (a : Fin w × Path) (p : ℕ) (ha : RespectsAt f a)
    (hlay : ∀ x, x ∈ chainNodesSet X ζ a ∨ x = addrExt a X.lonePath →
      layerAt LG' x = layerAt LG (f x))
    (hpa : parAt LG' p a = parAt LG p (f a)) (h : TreePattern LG p X ζ (f a)) :
    TreePattern LG' p X ζ a := by
  obtain ⟨hc, hcp, hb⟩ := h
  have hfa : ∀ q, f (addrExt a q) = addrExt (f a) q := ha
  refine ⟨?_, chainPairLayers_map' f X ζ a ha hlay hcp, ?_⟩
  · intro l hl
    have hmem : (f l.1, f l.2) ∈ X.linksAt ζ (f a) := by
      rw [chain_linksAt_map_local X f a ha ζ]
      exact List.mem_map.mpr ⟨l, hl, rfl⟩
    have h1 : l.1 ∈ chainNodesSet X ζ a :=
      Finset.mem_union_left _ ((mem_pairEndpoints_iff _ _).mpr ⟨l, hl, Or.inl rfl⟩)
    have h2 : l.2 ∈ chainNodesSet X ζ a :=
      Finset.mem_union_left _ ((mem_pairEndpoints_iff _ _).mpr ⟨l, hl, Or.inr rfl⟩)
    rw [hlay _ (Or.inl h1), hlay _ (Or.inl h2)]
    exact hc _ hmem
  · intro z hz
    have hz' : f z ∈ chainNodesSet X ζ (f a) := by
      rw [chainNodesSet_map X ζ f a ha]; exact Finset.mem_image_of_mem f hz
    have := hb _ hz'
    rw [hlay z (Or.inl hz), hlay _ (Or.inr rfl), hfa, hpa]
    exact this

namespace GlueT
variable {LM T : LayeredGarden w} {G2 : Garden w} {X : RegChain} {ζ : ℤˣ} {a aT : Fin w × Path}
  {t t' : TTree} {p : ℕ} (h : GlueT LM T G2 X ζ a aT t t' p)
include h

theorem glued_parAt_a : parAt h.glued p a = parAt T p aT := by
  rw [h.hpa]
  exact (OutAgreeT.parAt_root_eq (X := RegChain.nil) (X' := X) (a := a) (LG := LM) (LG' := h.glued)
    (p := p) (by simpa [RegChain.lonePath, addrExt] using h.outAgreeT) h.embM.node
    (by
      have hn : a.2 ∈ (G2.tree a.1).nodes := h.embG.node
      exact hn)).symm

theorem glued_pattern (hT : TreePattern T p X ζ aT) : TreePattern h.glued p X ζ a := by
  refine treePattern_map (LG := T) (treePort a aT) X ζ a p (treePort_respects a aT) ?_ ?_ ?_
  · intro x hx
    rcases hx with hx | rfl
    · exact h.glued_region ⟨chainNodesSet_under hx, chainNodesSet_not_under_lone hx⟩
    · rw [h.glued_lone, treePort_ext]
  · rw [treePort_self]; exact h.glued_parAt_a
  · rw [treePort_self]; exact hT

/-- **The glued layered garden is a coherent tree insertion** into the base. -/
theorem insertion (hT : TreePattern T p X ζ aT) (hwf : X.wf = true)
    (hsig : G2.sig = LM.garden.sig) (hroot : nodeSign LM.garden.sig a = ζ) :
    CoherentTreeInsertion p LM h.glued a ζ t X where
  wf := hwf
  signature := hsig
  rootSign := hroot
  oldEmbedding := h.embM
  newEmbedding := h.embG
  outside := by simpa [RegChain.lonePath, addrExt] using h.outAgreeT
  pattern := h.glued_pattern hT

end GlueT
end WaveTurbulence.Stage1
