/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.LayerCutBlockStructure
public import WaveTurbulence.Foundations.XChain.LayerCutPairGarden
public import WaveTurbulence.Foundations.XChain.BlockRootMembership
/-! The actual family of canonical-or-pair gardens recovered from the source top decomposition. -/
@[expose] public section
namespace WaveTurbulence.Induct
open Finset

noncomputable def inverseLowerFamily {w : ℕ} (LG : LayeredGarden w) (p : ℕ)
    (hbound : ∀ a, LG.layer a ≤ p) (hplain : LG.garden.IsPlain) (P : Finpartition (LG.attachNodes p))
    (hTD : LG.TopDecompWith false p (LG.CanonInd p) LG.roots (LG.attachNodes p) P)
    (B : ↥(layerCutPartition LG p hbound P).parts) : LayeredGarden B.1.card :=
  cutBlockGarden LG p B.1 (layerCut_block_completelyPaired LG p hbound hplain P hTD B)

theorem inverseLowerFamily_component {w : ℕ} (LG : LayeredGarden w) (p : ℕ)
    (hbound : ∀ a, LG.layer a ≤ p) (hplain : LG.garden.IsPlain) (P : Finpartition (LG.attachNodes p))
    (hTD : LG.TopDecompWith false p (LG.CanonInd p) LG.roots (LG.attachNodes p) P)
    (B : ↥(layerCutPartition LG p hbound P).parts) :
    IsCanonG p (inverseLowerFamily LG p hbound hplain P hTD B) ∨
      B.1.card = 2 ∧ ∀ a, (inverseLowerFamily LG p hbound hplain P hTD B).layer a = p := by
  rcases layerCut_block_structure LG p hbound hplain P hTD B with hc | ht
  · exact Or.inl (cutBlockGarden_isCanonG LG p B.1 _ hc)
  · exact Or.inr ⟨ht.1, cutBlockGarden_terminal_layer LG p B.1 _ ht.2⟩

theorem inverseLowerFamily_plain {w : ℕ} (LG : LayeredGarden w) (p : ℕ)
    (hbound : ∀ a, LG.layer a ≤ p) (hplain : LG.garden.IsPlain) (P : Finpartition (LG.attachNodes p))
    (hTD : LG.TopDecompWith false p (LG.CanonInd p) LG.roots (LG.attachNodes p) P)
    (B : ↥(layerCutPartition LG p hbound P).parts) :
    (inverseLowerFamily LG p hbound hplain P hTD B).garden.IsPlain := fun _ => rfl

theorem inverseLowerFamily_bound {w : ℕ} (LG : LayeredGarden w) (p : ℕ)
    (hbound : ∀ a, LG.layer a ≤ p) (hplain : LG.garden.IsPlain) (P : Finpartition (LG.attachNodes p))
    (hTD : LG.TopDecompWith false p (LG.CanonInd p) LG.roots (LG.attachNodes p) P)
    (B : ↥(layerCutPartition LG p hbound P).parts)
    (a : GNode (inverseLowerFamily LG p hbound hplain P hTD B).garden.tree) :
    (inverseLowerFamily LG p hbound hplain P hTD B).layer a ≤ p := by
  exact hbound (cutBlockNodeMap LG p B.1 _ a)

end WaveTurbulence.Induct
