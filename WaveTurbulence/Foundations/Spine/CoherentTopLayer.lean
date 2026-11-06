/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.GardenPartition
public import WaveTurbulence.Foundations.Molecule.LayerRegDraft.LayerReg1
/-! TARGET L2233: a whole coherent canonical couple has every node in the top layer. -/
public section
namespace WaveTurbulence.LGSpine
open Finset
open WaveTurbulence.Reg WaveTurbulence.Links

theorem cplNodes_covers_node {G : Garden 2} {Q : RegCpl} (hQ : Q.Decodes G)
    (z : GNode G.tree) : z.1 ∈ cplNodes Q (0, []) (1, []) := by
  rw [cplNodes, ← couple_branchAddresses, ← couple_leafAddresses]
  simp only [mem_union]
  rcases z with ⟨⟨i, path⟩, hp⟩
  fin_cases i
  · rcases (TTree.mem_nodes_iff _ _).mp hp with hl | hb
    · apply Or.inr
      apply Or.inl
      exact mem_image.mpr ⟨path, by change path ∈ (G.tree (0 : Fin 2)).leaves at hl; rw [hQ.2.1] at hl; exact hl, rfl⟩
    · apply Or.inl
      apply Or.inl
      exact mem_image.mpr ⟨path, by change path ∈ (G.tree (0 : Fin 2)).branching at hb; rw [hQ.2.1] at hb; exact hb, rfl⟩
  · rcases (TTree.mem_nodes_iff _ _).mp hp with hl | hb
    · apply Or.inr
      apply Or.inr
      exact mem_image.mpr ⟨path, by change path ∈ (G.tree (1 : Fin 2)).leaves at hl; rw [hQ.2.2.1] at hl; exact hl, rfl⟩
    · apply Or.inl
      apply Or.inr
      exact mem_image.mpr ⟨path, by change path ∈ (G.tree (1 : Fin 2)).branching at hb; rw [hQ.2.2.1] at hb; exact hb, rfl⟩

/-- This is the exact whole-couple specialization of the proved C4 layerreg1 theorem. -/
theorem coherent_canonical_layer_eq {LG : LayeredGarden 2} {p : ℕ}
    (hcan : IsCanonC (p + 1) LG) (hcoh : IsCoherentCouple LG) : ∀ z, LG.layer z = p := by
  obtain ⟨_, Q, hwf, hQ, hi⟩ := hcoh
  intro z
  have h := layerreg1_canonCouple hcan hQ hwf hi z.1 (cplNodes_covers_node hQ z)
  simpa only [layerAt_node] using h

end WaveTurbulence.LGSpine
