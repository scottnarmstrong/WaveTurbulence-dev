/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.LayerCutPartition
public import WaveTurbulence.Foundations.XChain.LayerCutBlockRoots
/-! Exact source blocks recovered from the inverse top-leaf partition. -/
public section
namespace WaveTurbulence.Induct
open Finset
open scoped Classical

theorem layerCutPartition_mem_part_equiv {w : ℕ} (LG : LayeredGarden w) (p : ℕ)
    (hbound : ∀ a, LG.layer a ≤ p) (P : Finpartition (LG.attachNodes p))
    (a b : ↥(LG.attachNodes p) ⊕ TerminalLeaf LG p) :
    (layerCutLeafEquiv LG p hbound).symm b ∈
      (layerCutPartition LG p hbound P).part ((layerCutLeafEquiv LG p hbound).symm a) ↔
    b ∈ (sumPartition (subtypePartition P)
      (pairingPartition (terminalLeafPair LG p) (terminalLeafPair_involutive LG p))).part a := by
  have he := mapUnivPartition_mem_part (layerCutLeafEquiv LG p hbound).symm
    (sumPartition (subtypePartition P)
      (pairingPartition (terminalLeafPair LG p) (terminalLeafPair_involutive LG p)))
    ((layerCutLeafEquiv LG p hbound).symm a) ((layerCutLeafEquiv LG p hbound).symm b)
  simpa only [Equiv.symm_symm, Equiv.apply_symm_apply, layerCutPartition] using he

theorem layerCutPartition_attach_roots {w : ℕ} (LG : LayeredGarden w) (p : ℕ)
    (hbound : ∀ a, LG.layer a ≤ p) (P : Finpartition (LG.attachNodes p)) (u : ↥(LG.attachNodes p)) :
    cutBlockRoots LG p ((layerCutPartition LG p hbound P).part
      ((layerCutLeafEquiv LG p hbound).symm (.inl u))) = P.part u.1 := by
  classical
  ext x
  constructor
  · intro hx
    obtain ⟨b, hb, hbx⟩ := Finset.mem_map.mp hx
    obtain ⟨z, rfl⟩ := (layerCutLeafEquiv LG p hbound).symm.surjective b
    have hm := (layerCutPartition_mem_part_equiv LG p hbound P (.inl u) z).mp hb
    rcases z with v | v
    · have hv := (subtypePartition_mem_part P u v).mp
        ((sumPartition_mem_part_inl _ _ u v).mp hm)
      have he : cutLeafNodeEmbedding LG p ((layerCutLeafEquiv LG p hbound).symm (.inl v)) = v.1 := rfl
      exact (he.symm.trans hbx) ▸ hv
    · exact False.elim (sumPartition_not_mem_part_inl _ _ u v hm)
  · intro hx
    have hu : x ∈ LG.attachNodes p := P.le (P.part_mem.mpr u.2) hx
    let v : ↥(LG.attachNodes p) := ⟨x, hu⟩
    have hv := (sumPartition_mem_part_inl (subtypePartition P)
      (pairingPartition (terminalLeafPair LG p) (terminalLeafPair_involutive LG p)) u v).mpr
      ((subtypePartition_mem_part P u v).mpr hx)
    refine Finset.mem_map.mpr ⟨(layerCutLeafEquiv LG p hbound).symm (.inl v),
      (layerCutPartition_mem_part_equiv LG p hbound P (.inl u) (.inl v)).mpr hv, ?_⟩
    rfl

end WaveTurbulence.Induct
