/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.Shared.S1GlueC4
import Mathlib.Tactic

/-!
# Glued layers: paired leaves have equal layers
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Stage1
open TTree Reg Reg.Skeleton Twist Links RegRed WaveTurbulence.LFTwist

variable {w : ℕ}

theorem endpoint_inRegion {Q : RegCpl} {a b z : Fin w × Path}
    (hz : z ∈ pairEndpoints (Q.pairsAt a b)) : InRegion a b z := by
  rw [← couple_leafAddresses Q a b, Finset.mem_union] at hz
  rcases hz with hz | hz
  · obtain ⟨q, _, rfl⟩ := mem_image_addrExt hz
    exact Or.inl (under_ext a q)
  · obtain ⟨q, _, rfl⟩ := mem_image_addrExt hz
    exact Or.inr (under_ext b q)

namespace GlueC
variable {LN T : LayeredGarden w} {G : Garden w} {Q : RegCpl} {a b aT bT : Fin w × Path} {p : ℕ}
  (h : GlueC LN T G Q a b aT bT p)
include h

/-- Pairs of a decoded endpoint list, seen in the template. -/
theorem tmpl_pair {r : (Fin w × Path) × (Fin w × Path)} (hr : r ∈ Q.pairsAt a b)
    (ℓT : GLeaf T.garden.tree) (hl : ℓT.1 = couplePort a b aT bT r.1) :
    ∃ ℓT' : GLeaf T.garden.tree, ℓT'.1 = couplePort a b aT bT r.2 ∧ T.garden.pair ℓT = ℓT' := by
  have hr' : (couplePort a b aT bT r.1, couplePort a b aT bT r.2) ∈ Q.pairsAt aT bT := by
    rw [h.pairs_port]
    exact List.mem_map.mpr ⟨r, hr, rfl⟩
  have := h.embT.pairs _ hr' ℓT hl
  exact ⟨T.garden.pair ℓT, this, rfl⟩

theorem pair_in_region (ℓ : GLeaf G.tree) (hℓ : InRegion a b ℓ.1) :
    glueAt LN T a b aT bT ℓ.1 = glueAt LN T a b aT bT (G.pair ℓ).1 := by
  have hmem := h.embM.leaf_mem ℓ hℓ
  obtain ⟨r, hr, hrl⟩ := (mem_pairEndpoints_iff _ _).mp hmem
  -- a template leaf for the first endpoint
  have hr1 : r.1 ∈ pairEndpoints (Q.pairsAt a b) :=
    (mem_pairEndpoints_iff _ _).mpr ⟨r, hr, Or.inl rfl⟩
  have hr2 : r.2 ∈ pairEndpoints (Q.pairsAt a b) :=
    (mem_pairEndpoints_iff _ _).mpr ⟨r, hr, Or.inr rfl⟩
  have hr1' : couplePort a b aT bT r.1 ∈ pairEndpoints (Q.pairsAt aT bT) := by
    rw [h.pairs_port]
    exact (mem_pairEndpoints_iff _ _).mpr ⟨_, List.mem_map.mpr ⟨r, hr, rfl⟩, Or.inl rfl⟩
  let ℓT : GLeaf T.garden.tree := ⟨couplePort a b aT bT r.1, h.embT.leaf_of_mem hr1'⟩
  obtain ⟨ℓT', hℓT', hpT⟩ := h.tmpl_pair hr ℓT rfl
  let ℓ1 : GLeaf G.tree := ⟨r.1, h.embM.leaf_of_mem hr1⟩
  have hp1 : (G.pair ℓ1).1 = r.2 := h.embM.pairs r hr ℓ1 rfl
  have hT : layerAt T ℓT.1 = layerAt T ℓT'.1 := by
    have e1 := layerAt_node T ℓT.toNode
    have e2 := layerAt_node T ℓT'.toNode
    have e3 := T.isLayering.2 ℓT
    rw [hpT] at e3
    exact e1.trans (e3.trans e2.symm)
  have hrin1 : InRegion a b r.1 := endpoint_inRegion hr1
  have hrin2 : InRegion a b r.2 := endpoint_inRegion hr2
  rcases hrl with hl | hl
  · have hpart : (G.pair ℓ).1 = r.2 := h.embM.pairs r hr ℓ hl
    rw [glueAt_in _ _ _ _ _ _ hℓ, hpart, glueAt_in _ _ _ _ _ _ hrin2, hl]
    exact hT.trans (by rw [hℓT'])
  · have hpart : G.pair ℓ = ℓ1 := by
      have : G.pair ℓ1 = ℓ := Subtype.ext (hp1.trans hl.symm)
      rw [← this, G.pair_pair]
    have hp' : (G.pair ℓ).1 = r.1 := by rw [hpart]
    rw [glueAt_in _ _ _ _ _ _ hℓ, hp', glueAt_in _ _ _ _ _ _ hrin1, hl]
    rw [← hℓT']
    exact hT.symm

end GlueC
end WaveTurbulence.Stage1
