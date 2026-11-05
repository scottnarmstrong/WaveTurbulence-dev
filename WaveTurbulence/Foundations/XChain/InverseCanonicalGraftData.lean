/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.CanonicalGraftData
public import WaveTurbulence.Foundations.XChain.InverseGraftEquality
public import WaveTurbulence.Foundations.XChain.TopPartitionNecessity
public import WaveTurbulence.Foundations.XChain.CanonicalTopDecomp
/-! Every canonical garden has literal top-tree and attached-garden construction data. -/
@[expose] public section
namespace WaveTurbulence.Induct
open Finset

theorem inverseLowerFamily_component_strong {w : ℕ} (LG : LayeredGarden w) (p : ℕ)
    (hbound : ∀ a, LG.layer a ≤ p) (hplain : LG.garden.IsPlain) (P : Finpartition (LG.attachNodes p))
    (hTD : LG.TopDecompWith false p (LG.CanonInd p) LG.roots (LG.attachNodes p) P)
    (B : ↥(layerCutPartition LG p hbound P).parts) :
    IsCanonG p (inverseLowerFamily LG p hbound hplain P hTD B) ∨
      B.1.card = 2 ∧ (∀ k, (inverseLowerFamily LG p hbound hplain P hTD B).garden.tree k = TTree.leaf) ∧
      ∀ a, (inverseLowerFamily LG p hbound hplain P hTD B).layer a = p := by
  rcases layerCut_block_structure LG p hbound hplain P hTD B with hc | ht
  · exact Or.inl (cutBlockGarden_isCanonG LG p B.1 _ hc)
  · exact Or.inr ⟨ht.1, cutBlockGarden_terminal_trees LG p B.1 _ (fun b hb => (ht.2 b hb).1),
      cutBlockGarden_terminal_layer LG p B.1 _ ht.2⟩

noncomputable def inverseCanonicalGraftData {w : ℕ} (LG : LayeredGarden w) (p : ℕ)
    (hbound : ∀ a, LG.layer a ≤ p) (hplain : LG.garden.IsPlain) (hirr : LG.garden.Irreducible)
    (P : Finpartition (LG.attachNodes p))
    (hTD : LG.TopDecompWith false p (LG.CanonInd p) LG.roots (LG.attachNodes p) P) :
    CanonicalGraftData LG.garden.sig p where
  top := layerCutForest LG p
  partition := layerCutPartition LG p hbound P
  low := inverseLowerFamily LG p hbound hplain P hTD
  plain := inverseLowerFamily_plain LG p hbound hplain P hTD
  sign := inverseLowerFamily_sig LG p hbound hplain P hTD
  irreducible := topPartitionIrreducible_of_graft LG.garden.sig (layerCutForest LG p)
    (layerCutPartition LG p hbound P) (fun B => (inverseLowerFamily LG p hbound hplain P hTD B).garden)
    (inverseLowerFamily_plain LG p hbound hplain P hTD) (inverseLowerFamily_sig LG p hbound hplain P hTD)
    ((congrArg Garden.Irreducible (inverseGraft_garden LG p hbound hplain P hTD)).mpr hirr)
  component := inverseLowerFamily_component_strong LG p hbound hplain P hTD

theorem inverseCanonicalGraftData_graft {w : ℕ} (LG : LayeredGarden w) (p : ℕ)
    (hbound : ∀ a, LG.layer a ≤ p) (hplain : LG.garden.IsPlain) (hirr : LG.garden.Irreducible)
    (P : Finpartition (LG.attachNodes p))
    (hTD : LG.TopDecompWith false p (LG.CanonInd p) LG.roots (LG.attachNodes p) P) :
    (inverseCanonicalGraftData LG p hbound hplain hirr P hTD).graft = LG :=
  inverseGraft_eq LG p hbound hplain P hTD

theorem exists_canonicalGraftData {w p : ℕ} (LG : LayeredGarden w) (hG : IsCanonG (p + 1) LG) :
    ∃ C : CanonicalGraftData LG.garden.sig p, C.graft = LG := by
  obtain ⟨P, hTD, _⟩ := existsUnique_topDecomp LG p hG
  exact ⟨inverseCanonicalGraftData LG p hG.2.2.2.1 hG.2.1 hG.2.2.1 P hTD,
    inverseCanonicalGraftData_graft LG p hG.2.2.2.1 hG.2.1 hG.2.2.1 P hTD⟩

end WaveTurbulence.Induct
