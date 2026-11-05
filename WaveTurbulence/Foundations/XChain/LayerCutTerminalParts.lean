/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.LayerCutPartitionParts
/-! The terminal inverse blocks are exactly pairs of original leaves in layer p. -/
public section
namespace WaveTurbulence.Induct
open Finset
open scoped Classical

theorem layerCutPartition_terminal_roots {w : ℕ} (LG : LayeredGarden w) (p : ℕ)
    (hbound : ∀ a, LG.layer a ≤ p) (P : Finpartition (LG.attachNodes p)) (ℓ : TerminalLeaf LG p) :
    cutBlockRoots LG p ((layerCutPartition LG p hbound P).part
      ((layerCutLeafEquiv LG p hbound).symm (.inr ℓ))) = {ℓ.1.toNode, (LG.garden.pair ℓ.1).toNode} := by
  classical
  ext x
  constructor
  · intro hx
    obtain ⟨b, hb, hbx⟩ := Finset.mem_map.mp hx
    obtain ⟨z, rfl⟩ := (layerCutLeafEquiv LG p hbound).symm.surjective b
    have hm := (layerCutPartition_mem_part_equiv LG p hbound P (.inr ℓ) z).mp hb
    rcases z with v | v
    · exact False.elim (sumPartition_not_mem_part_inr _ _ ℓ v hm)
    · have hv := (sumPartition_mem_part_inr _ _ ℓ v).mp hm
      rw [pairingPartition_part] at hv
      have hx' : x = v.1.toNode := hbx.symm
      rcases (show v = ℓ ∨ v = terminalLeafPair LG p ℓ from by
        simpa only [mem_insert, mem_singleton] using hv) with he | he
      · exact Finset.mem_insert.mpr (Or.inl (hx'.trans (congrArg (fun v : TerminalLeaf LG p => v.1.toNode) he)))
      · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr
          (hx'.trans (congrArg (fun v : TerminalLeaf LG p => v.1.toNode) he))))
  · intro hx
    let Q := pairingPartition (terminalLeafPair LG p) (terminalLeafPair_involutive LG p)
    have hv : ∃ v : TerminalLeaf LG p, v ∈ Q.part ℓ ∧ v.1.toNode = x := by
      rcases (show x = ℓ.1.toNode ∨ x = (LG.garden.pair ℓ.1).toNode from by
        simpa only [mem_insert, mem_singleton] using hx) with hx | hx
      · exact ⟨ℓ, Q.mem_part (mem_univ _), hx.symm⟩
      · refine ⟨terminalLeafPair LG p ℓ, ?_, hx.symm⟩
        rw [pairingPartition_part]
        exact Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr rfl))
    obtain ⟨v, hv, hvx⟩ := hv
    refine Finset.mem_map.mpr ⟨(layerCutLeafEquiv LG p hbound).symm (.inr v), ?_, hvx⟩
    apply (layerCutPartition_mem_part_equiv LG p hbound P (.inr ℓ) (.inr v)).mpr
    exact (sumPartition_mem_part_inr _ _ ℓ v).mpr hv

theorem layerCutPartition_terminal_card {w : ℕ} (LG : LayeredGarden w) (p : ℕ)
    (hbound : ∀ a, LG.layer a ≤ p) (hplain : LG.garden.IsPlain)
    (P : Finpartition (LG.attachNodes p)) (ℓ : TerminalLeaf LG p) :
    ((layerCutPartition LG p hbound P).part ((layerCutLeafEquiv LG p hbound).symm (.inr ℓ))).card = 2 := by
  let Q := pairingPartition (terminalLeafPair LG p) (terminalLeafPair_involutive LG p)
  have he := congrArg Finset.card (mapUnivPartition_part (layerCutLeafEquiv LG p hbound).symm
    (sumPartition (subtypePartition P) Q) (.inr ℓ))
  simp only [Finset.card_map] at he
  have hs := congrArg Finset.card (sumPartition_part_inr (subtypePartition P) Q ℓ)
  simp only [Finset.card_map] at hs
  have hc := pairingPartition_card_part (terminalLeafPair LG p) (terminalLeafPair_involutive LG p)
    (terminalLeafPair_ne_self LG p hplain) (Q.part ℓ) (Q.part_mem.mpr (mem_univ _))
  exact he.trans (hs.trans hc)

theorem layerCutPartition_terminal_leaf {w : ℕ} (LG : LayeredGarden w) (p : ℕ)
    (hbound : ∀ a, LG.layer a ≤ p) (P : Finpartition (LG.attachNodes p)) (ℓ : TerminalLeaf LG p)
    (b : GLeaf (layerCutForest LG p))
    (hb : b ∈ (layerCutPartition LG p hbound P).part ((layerCutLeafEquiv LG p hbound).symm (.inr ℓ))) :
    b.1.2 ∈ (LG.garden.tree b.1.1).leaves ∧ LG.layer (cutLeafNodeEmbedding LG p b) = p := by
  obtain ⟨z, rfl⟩ := (layerCutLeafEquiv LG p hbound).symm.surjective b
  have hm := (layerCutPartition_mem_part_equiv LG p hbound P (.inr ℓ) z).mp hb
  rcases z with v | v
  · exact False.elim (sumPartition_not_mem_part_inr _ _ ℓ v hm)
  · exact ⟨v.1.2, v.2⟩

end WaveTurbulence.Induct
