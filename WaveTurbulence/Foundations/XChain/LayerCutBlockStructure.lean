/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.LayerCutTerminalParts
public import WaveTurbulence.Foundations.XChain.LeafRootPairing
/-! Every inverse block is an actual canonical component or a terminal leaf pair. -/
public section
namespace WaveTurbulence.Induct
open Finset

theorem canonInd_completelyPaired {w : ℕ} (LG : LayeredGarden w) (p : ℕ)
    (U : Finset (GNode LG.garden.tree)) (h : LG.CanonInd p U) :
    LG.garden.CompletelyPaired (LG.leavesBelowSet U) := by
  cases p with
  | zero => exact False.elim h
  | succ q => exact h.2.2.1

theorem layerCut_block_structure {w : ℕ} (LG : LayeredGarden w) (p : ℕ)
    (hbound : ∀ a, LG.layer a ≤ p) (hplain : LG.garden.IsPlain) (P : Finpartition (LG.attachNodes p))
    (hTD : LG.TopDecompWith false p (LG.CanonInd p) LG.roots (LG.attachNodes p) P)
    (B : ↥(layerCutPartition LG p hbound P).parts) :
    LG.CanonInd p (cutBlockRoots LG p B.1) ∨
      B.1.card = 2 ∧ ∀ b ∈ B.1, b.1.2 ∈ (LG.garden.tree b.1.1).leaves ∧
        LG.layer (cutLeafNodeEmbedding LG p b) = p := by
  classical
  obtain ⟨a, ha⟩ := (layerCutPartition LG p hbound P).nonempty_of_mem_parts B.2
  obtain ⟨z, rfl⟩ := (layerCutLeafEquiv LG p hbound).symm.surjective a
  have hpart := (layerCutPartition LG p hbound P).part_eq_of_mem B.2 ha
  rcases z with u | ℓ
  · left
    have he := (congrArg (cutBlockRoots LG p) hpart).symm.trans
      (layerCutPartition_attach_roots LG p hbound P u)
    have hc := (hTD.2.2.2 (P.part u.1) (P.part_mem.mpr u.2)).2
    exact he.symm ▸ hc
  · right
    have hcard := layerCutPartition_terminal_card LG p hbound hplain P ℓ
    refine ⟨(congrArg Finset.card hpart).symm.trans hcard, ?_⟩
    intro b hb
    exact layerCutPartition_terminal_leaf LG p hbound P ℓ b (hpart.symm ▸ hb)

theorem layerCut_block_completelyPaired {w : ℕ} (LG : LayeredGarden w) (p : ℕ)
    (hbound : ∀ a, LG.layer a ≤ p) (hplain : LG.garden.IsPlain) (P : Finpartition (LG.attachNodes p))
    (hTD : LG.TopDecompWith false p (LG.CanonInd p) LG.roots (LG.attachNodes p) P)
    (B : ↥(layerCutPartition LG p hbound P).parts) :
    LG.garden.CompletelyPaired (LG.leavesBelowSet (cutBlockRoots LG p B.1)) := by
  classical
  obtain ⟨a, ha⟩ := (layerCutPartition LG p hbound P).nonempty_of_mem_parts B.2
  obtain ⟨z, rfl⟩ := (layerCutLeafEquiv LG p hbound).symm.surjective a
  have hpart := (layerCutPartition LG p hbound P).part_eq_of_mem B.2 ha
  rcases z with u | ℓ
  · have he := (congrArg (cutBlockRoots LG p) hpart).symm.trans
      (layerCutPartition_attach_roots LG p hbound P u)
    have hc := canonInd_completelyPaired LG p (P.part u.1)
      (hTD.2.2.2 (P.part u.1) (P.part_mem.mpr u.2)).2
    exact (congrArg (fun U => LG.garden.CompletelyPaired (LG.leavesBelowSet U)) he).mpr hc
  · have he := (congrArg (cutBlockRoots LG p) hpart).symm.trans
      (layerCutPartition_terminal_roots LG p hbound P ℓ)
    have hs := (congrArg LG.leavesBelowSet he).trans (leavesBelowSet_leaf_pair LG ℓ.1)
    exact (congrArg LG.garden.CompletelyPaired hs).mpr (completelyPaired_leaf_pair LG.garden hplain ℓ.1)

end WaveTurbulence.Induct
