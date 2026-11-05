/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.SubtreeOrder
public import WaveTurbulence.Foundations.XChain.AttachmentBlockOrder
public import WaveTurbulence.Foundations.XChain.LayerCutLowerFamily
public import WaveTurbulence.Foundations.XChain.LayerCutOrder
/-! Exact source truncation bounds in the inverse canonical construction. -/
public section
namespace WaveTurbulence.Induct
open Finset

theorem inverseLowerFamily_order_le_iff {w : ℕ} (LG : LayeredGarden w) (p N : ℕ)
    (hbound : ∀ a, LG.layer a ≤ p) (hplain : LG.garden.IsPlain) (P : Finpartition (LG.attachNodes p))
    (hTD : LG.TopDecompWith false p (LG.CanonInd p) LG.roots (LG.attachNodes p) P) :
    (∀ B, (inverseLowerFamily LG p hbound hplain P hTD B).garden.order ≤ N) ↔
      ∀ u ∈ LG.attachNodes p, LG.attachedOrder p u ≤ N := by
  classical
  constructor
  · intro h u hu
    let a := (layerCutLeafEquiv LG p hbound).symm (.inl ⟨u, hu⟩)
    let B : ↥(layerCutPartition LG p hbound P).parts :=
      ⟨(layerCutPartition LG p hbound P).part a, (layerCutPartition LG p hbound P).part_mem.mpr (mem_univ a)⟩
    have hr := layerCutPartition_attach_roots LG p hbound P ⟨u, hu⟩
    have ho := cutBlockGarden_order LG p B.1 (layerCut_block_completelyPaired LG p hbound hplain P hTD B)
    have he : (inverseLowerFamily LG p hbound hplain P hTD B).garden.order =
        LG.attachedOrder p u := by
      exact ho.trans ((congrArg (fun U : Finset (GNode LG.garden.tree) => ∑ v ∈ U, v.orderBelow) hr).trans
        (attachedOrder_eq_block_sum LG p P hTD ⟨P.part u, P.part_mem.mpr hu⟩ u (P.mem_part hu)).symm)
    exact he ▸ h B
  · intro h B
    obtain ⟨a, ha⟩ := (layerCutPartition LG p hbound P).nonempty_of_mem_parts B.2
    obtain ⟨z, rfl⟩ := (layerCutLeafEquiv LG p hbound).symm.surjective a
    have hpart := (layerCutPartition LG p hbound P).part_eq_of_mem B.2 ha
    rcases z with u | l
    · have hr := (congrArg (cutBlockRoots LG p) hpart).symm.trans
        (layerCutPartition_attach_roots LG p hbound P u)
      have ho := cutBlockGarden_order LG p B.1 (layerCut_block_completelyPaired LG p hbound hplain P hTD B)
      have he : (inverseLowerFamily LG p hbound hplain P hTD B).garden.order =
          LG.attachedOrder p u.1 := by
        exact ho.trans ((congrArg (fun U : Finset (GNode LG.garden.tree) => ∑ v ∈ U, v.orderBelow) hr).trans
          (attachedOrder_eq_block_sum LG p P hTD ⟨P.part u.1, P.part_mem.mpr u.2⟩ u.1 (P.mem_part u.2)).symm)
      exact he.symm ▸ h u.1 u.2
    · have ht : ∀ b ∈ B.1, b.1.2 ∈ (LG.garden.tree b.1.1).leaves := by
        intro b hb
        exact (layerCutPartition_terminal_leaf LG p hbound P l b (hpart.symm ▸ hb)).1
      have ho : (inverseLowerFamily LG p hbound hplain P hTD B).garden.order = 0 := by
        change (∑ k, ((cutBlockGarden LG p B.1 _).garden.tree k).order) = 0
        simp_rw [cutBlockGarden_terminal_trees LG p B.1 _ ht, TTree.order]
        exact sum_const_zero
      exact ho ▸ Nat.zero_le N

theorem sourceTrunc_iff_inverse_bounds {w : ℕ} (LG : LayeredGarden w) (p Ntop Natt : ℕ)
    (hbound : ∀ a, LG.layer a ≤ p) (hplain : LG.garden.IsPlain) (P : Finpartition (LG.attachNodes p))
    (hTD : LG.TopDecompWith false p (LG.CanonInd p) LG.roots (LG.attachNodes p) P) :
    LG.IsTrunc p Ntop Natt ↔ (∀ j, (layerCutForest LG p j).order ≤ Ntop) ∧
      ∀ B, (inverseLowerFamily LG p hbound hplain P hTD B).garden.order ≤ Natt := by
  simp only [LayeredGarden.IsTrunc, layerCutForest_order LG p hbound,
    inverseLowerFamily_order_le_iff LG p Natt hbound hplain P hTD]

end WaveTurbulence.Induct
