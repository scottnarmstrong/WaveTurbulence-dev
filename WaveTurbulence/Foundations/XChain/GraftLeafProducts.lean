/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.MarkedLayeredGraft
/-! Leaf-input factors and marks split exactly across the attached gardens. -/
public section
namespace WaveTurbulence.Induct
open Finset

theorem mem_inputLeaves_iff {w : ℕ} (G : Garden w) (ℓ : GLeaf G.tree) :
    ℓ ∈ inputLeaves G ↔ G.sign ℓ.toNode = 1 ∧ G.mark ℓ = none := by
  simp only [inputLeaves, Finset.mem_filter, Finset.mem_univ, true_and]

theorem markedGardenGraft_inputLeaf_iff {w : ℕ} (sig : Fin w → ℤˣ) (top : Fin w → TTree)
    (P : Finpartition (univ : Finset (GLeaf top))) (low : (B : P.parts) → Garden B.1.card)
    (hsig : ∀ B k, (low B).sig k = nodeSign sig ((blockRootEquiv top P).symm ⟨B, k⟩).1)
    (B : P.parts) (ℓ : GLeaf (low B).tree) :
    lowerLeafEmbedding top P low B ℓ ∈ inputLeaves (markedGardenGraft sig top P low hsig) ↔
      ℓ ∈ inputLeaves (low B) := by
  have hs := gardenLeafEquiv_sign sig top P low hsig (lowerLeafEmbedding top P low B ℓ)
  have he := congrArg (fun z : Σ B : P.parts, GLeaf (low B).tree => nodeSign (low z.1).sig z.2.1)
    ((gardenLeafEquiv top P low).apply_symm_apply ⟨B, ℓ⟩)
  have hsign := hs.symm.trans he
  have hm := markedGardenGraft_mark_lower sig top P low hsig B ℓ
  constructor
  · intro h
    obtain ⟨hpos, hmark⟩ := (mem_inputLeaves_iff _ _).mp h
    exact (mem_inputLeaves_iff _ _).mpr ⟨hsign.symm.trans hpos, hm.symm.trans hmark⟩
  · intro h
    obtain ⟨hpos, hmark⟩ := (mem_inputLeaves_iff _ _).mp h
    exact (mem_inputLeaves_iff _ _).mpr ⟨hsign.trans hpos, hm.trans hmark⟩

theorem markedLayeredGardenGraft_leaf_layer {w : ℕ} (sig : Fin w → ℤˣ) (top : Fin w → TTree)
    (P : Finpartition (univ : Finset (GLeaf top))) (low : (B : P.parts) → LayeredGarden B.1.card)
    (p : ℕ)
    (hsig : ∀ B k, (low B).garden.sig k = nodeSign sig ((blockRootEquiv top P).symm ⟨B, k⟩).1)
    (hbound : ∀ B a, (low B).layer a ≤ p) (B : P.parts) (ℓ : GLeaf (low B).garden.tree) :
    (markedLayeredGardenGraft sig top P low p hsig hbound).layer
      (lowerLeafEmbedding top P (fun B => (low B).garden) B ℓ).toNode =
      (low B).layer ℓ.toNode := by
  exact (congrArg (graftLayer top P low p)
    (gardenLeaf_toNode_lower top P (fun B => (low B).garden) B ℓ)).trans
      (graftLayer_lower top P low p B ℓ.toNode)

end WaveTurbulence.Induct
