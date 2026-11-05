/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.LFTwist.CanonicalObject

/-! # Finite erasure of all coherent regular-tree attachments -/

public section
namespace WaveTurbulence.LFTwist
open TTree Reg Reg.Skeleton

/-- Erase an arbitrary finite list, preserving the original canonical kind,
all other coherence conditions, every couple code and every inherited branch layer. -/
theorem eraseTrees_list {w : ℕ} {S : Garden w} (hS : S.IsPlain) {p : ℕ} {kind : Bool}
    (bs : List (GBranch S.tree)) (LG : LayeredGarden w) (D : ReconstructionData S)
    (hd : D.Decodes hS LG.garden) (hc : CanonicalObject p kind LG)
    (hall : AllAttachmentsCoherent LG D hS) :
    ∃ (E : ReconstructionData S) (LH : LayeredGarden w) (he : E.Decodes hS LH.garden),
      CanonicalObject p kind LH ∧ AllAttachmentsCoherent LH E hS ∧
      (∀ b ∈ bs, E.tree b = .nil) ∧ (∀ b, b ∉ bs → E.tree b = D.tree b) ∧
      E.couple = D.couple ∧ inducedPrelayer LH E hS he = inducedPrelayer LG D hS hd := by
  induction bs generalizing LG D with
  | nil =>
    refine ⟨D,LG,hd,hc,hall,?_,?_,rfl,rfl⟩
    · intro b hb
      simp only [List.not_mem_nil] at hb
    · intro b _
      rfl
  | cons b bs ih =>
    let E₀ := D.eraseTree b
    let LH₀ := collapsePairedTreeLayered LG (D.decoded_chain_isSubPairedTree hS hd b)
    have he₀ : E₀.Decodes hS LH₀.garden := eraseTree_collapse_decodes D hS hd b
    have hc₀ : CanonicalObject p kind LH₀ := hc.eraseTree D hS hd hall b
    have hall₀ : AllAttachmentsCoherent LH₀ E₀ hS := eraseTree_allAttachmentsCoherent LG D hS hd b hall
    obtain ⟨E,LH,he,hc',hall',hnil,hother,hcpl,hcore⟩ := ih LH₀ E₀ he₀ hc₀ hall₀
    refine ⟨E,LH,he,hc',hall',?_,?_,hcpl,?_⟩
    · intro c hmem
      rcases List.mem_cons.mp hmem with heq | hmem
      · subst c
        by_cases hb : b ∈ bs
        · exact hnil b hb
        · exact (hother b hb).trans (D.eraseTree_at b)
      · exact hnil c hmem
    · intro c hmem
      have hcne : c ≠ b := fun h => hmem (List.mem_cons.mpr (Or.inl h))
      have hcn : c ∉ bs := fun h => hmem (List.mem_cons.mpr (Or.inr h))
      exact (hother c hcn).trans (D.eraseTree_other b c hcne)
    · exact hcore.trans (eraseTree_inducedPrelayer_eq LG D hS hd b)

/-- All tree attachments can be collapsed at once without changing the induced pre-layering. -/
theorem eraseAllTrees {w : ℕ} {S : Garden w} (hS : S.IsPlain) {p : ℕ} {kind : Bool}
    (LG : LayeredGarden w) (D : ReconstructionData S) (hd : D.Decodes hS LG.garden)
    (hc : CanonicalObject p kind LG) (hall : AllAttachmentsCoherent LG D hS) :
    ∃ (E : ReconstructionData S) (LH : LayeredGarden w) (he : E.Decodes hS LH.garden),
      CanonicalObject p kind LH ∧ AllAttachmentsCoherent LH E hS ∧ (∀ b, E.tree b = .nil) ∧
      E.couple = D.couple ∧ inducedPrelayer LH E hS he = inducedPrelayer LG D hS hd := by
  classical
  obtain ⟨E,LH,he,hc',hall',hnil,hother,hcpl,hcore⟩ :=
    eraseTrees_list hS (Finset.univ.toList) LG D hd hc hall
  exact ⟨E,LH,he,hc',hall',fun b => hnil b (Finset.mem_toList.mpr (Finset.mem_univ b)),hcpl,hcore⟩

end WaveTurbulence.LFTwist
