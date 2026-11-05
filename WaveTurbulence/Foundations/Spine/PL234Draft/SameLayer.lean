/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Spine.SpineInputs
public import WaveTurbulence.Foundations.Spine.CoherentTopLayer

/-!
# Coherent objects with equal parent layers lie in one layer (TARGET L1235, `layerreg1`)

TARGET's proof of Prop 6.1 (L1235): "when `q = q'` all the nodes in `𝒬` must be in the same layer".
For the spine's eligible objects (`IsCoherentCoupleAt`, `IsCoherentTreeAt`):

* `coherentCouple_layer_eq`: a coherent embedded couple with `q = q'` has every node (leaves included) of
  its local layered garden in layer `q` (LAYERREG `cpl_coherent`, second conjunct);
* `coherentTree_layer_eq`: a coherent embedded regular tree whose lone leaf is in its root's parent layer
  `q` has every node in layer `q` (LAYERREG `layerreg1_tree`).

The address facts `addrExt_mem_cplNodes`, `addrExt_mem_chainNodes` place every node of a decoded carrier
among the nodes of the placed code (LINKS `couple_branchAddresses`, `chain_branchAddresses`, REG-STRUCT
`couple_leafAddresses`, `chain_leafAddresses`).
-/

@[expose] public section

namespace WaveTurbulence.PL234

open TTree Finset WaveTurbulence.Links WaveTurbulence.Reg WaveTurbulence.LGSpine

/-- Every node of a decoded couple carrier, read at the placement `(a, b)`, is a node of the placed code. -/
theorem addrExt_mem_cplNodes {G : Garden 2} {Q : RegCpl} (hQ : Q.Decodes G) {w : ℕ}
    (a b : Fin w × Path) (z : GNode G.tree) :
    addrExt (if z.1.1 = 0 then a else b) z.1.2 ∈ cplNodes Q a b := by
  rw [cplNodes, ← couple_branchAddresses, ← couple_leafAddresses]
  simp only [mem_union, branchAddresses, leafAddresses]
  rcases z with ⟨⟨i, path⟩, hp⟩
  fin_cases i
  · have h0 : G.tree 0 = Q.trees.1 := hQ.2.1
    rcases (TTree.mem_nodes_iff _ _).mp hp with hl | hb
    · refine Or.inr (Or.inl (mem_image.mpr ⟨path, ?_, by simp⟩))
      change path ∈ (G.tree (0 : Fin 2)).leaves at hl
      rwa [h0] at hl
    · refine Or.inl (Or.inl (mem_image.mpr ⟨path, ?_, by simp⟩))
      change path ∈ (G.tree (0 : Fin 2)).branching at hb
      rwa [h0] at hb
  · have h1 : G.tree 1 = Q.trees.2 := hQ.2.2.1
    rcases (TTree.mem_nodes_iff _ _).mp hp with hl | hb
    · refine Or.inr (Or.inr (mem_image.mpr ⟨path, ?_, by simp⟩))
      change path ∈ (G.tree (1 : Fin 2)).leaves at hl
      rwa [h1] at hl
    · refine Or.inl (Or.inr (mem_image.mpr ⟨path, ?_, by simp⟩))
      change path ∈ (G.tree (1 : Fin 2)).branching at hb
      rwa [h1] at hb

/-- Every node of a decoded tree carrier, read at the root `a`, is a node of the placed chain or its lone
position. -/
theorem addrExt_mem_chainNodes {G : Garden 1} {X : RegChain} (hX : X.DecodesTree G) {w : ℕ}
    (a : Fin w × Path) (z : GNode G.tree) :
    addrExt a z.1.2 ∈ chainNodesSet X (G.sig 0) a ∨ z.1.2 = X.lonePath := by
  have ht : G.tree 0 = X.plug (G.sig 0) .leaf := hX.1
  rcases z with ⟨⟨i, path⟩, hp⟩
  have hi : i = 0 := Subsingleton.elim _ _
  subst hi
  change path ∈ (G.tree 0).nodes at hp
  rw [ht] at hp
  rcases (TTree.mem_nodes_iff _ _).mp hp with hl | hb
  · have hmem : addrExt a path ∈ leafAddresses (X.plug (G.sig 0) .leaf) a :=
      mem_image.mpr ⟨path, hl, rfl⟩
    rw [chain_leafAddresses] at hmem
    rcases mem_union.mp hmem with h | h
    · exact Or.inl (mem_union.mpr (Or.inr h))
    · right
      simp only [leafAddresses, TTree.leaves, Finset.image_singleton, mem_singleton] at h
      have h2 := congrArg Prod.snd h
      simpa [addrExt] using h2
  · have hmem : addrExt a path ∈ branchAddresses (X.plug (G.sig 0) .leaf) a :=
      mem_image.mpr ⟨path, hb, rfl⟩
    rw [chain_branchAddresses] at hmem
    rcases mem_union.mp hmem with h | h
    · exact Or.inl (mem_union.mpr (Or.inl h))
    · simp [branchAddresses, TTree.branching] at h

/-- **A coherent embedded couple with `q = q'` lies in layer `q`** (TARGET L1235; LAYERREG
`cpl_coherent`). -/
theorem coherentCouple_layer_eq {p q : ℕ} {Q : RegCpl} {LG : LayeredGarden 2}
    (h : IsCoherentCoupleAt p q q Q LG) : ∀ z, LG.layer z = q := by
  obtain ⟨hwf, hQ, w, H, a, b, hcan, hE, -, -, hcoh, hpa, hpb, hlay⟩ := h
  have hc := (cpl_coherent hcan.2.2 hcan.1 Q a b hwf hE hcoh).2 (hpa.trans hpb.symm)
  intro z
  rw [hlay z, hc _ (addrExt_mem_cplNodes hQ a b z), hpa]

/-- **A coherent embedded regular tree whose lone leaf is in layer `q` lies in layer `q`** (TARGET L1235;
LAYERREG `layerreg1_tree`). -/
theorem coherentTree_layer_eq {p q : ℕ} {X : RegChain} {LG : LayeredGarden 1}
    (h : IsCoherentTreeAt p q q X LG) : ∀ z, LG.layer z = q := by
  obtain ⟨hwf, hX, w, H, a, hh, hcan, hC, -, hcoh, hpa, hlone, hlay⟩ := h
  obtain ⟨-, hL, -⟩ := layerreg1_tree hcan.2.2 hcan.1 hwf hC hcoh
  intro z
  rw [hlay z]
  rcases addrExt_mem_chainNodes hX a z with hz | hz
  · exact le_antisymm ((hL _ hz).2.trans_eq hpa) (hlone.symm.le.trans (hL _ hz).1)
  · rw [hz, hlone]

end WaveTurbulence.PL234
