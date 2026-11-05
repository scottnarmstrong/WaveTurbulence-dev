/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.GraftBoundaryDecorations
/-! Assemble matching boundary-labelled decorations, preserving external root and flower labels. -/
@[expose] public section
namespace WaveTurbulence.Induct
open Finset

abbrev BoundaryDecorationData {w : ℕ} (top : Fin w → TTree)
    (P : Finpartition (univ : Finset (GLeaf top))) (low : (B : P.parts) → Garden B.1.card)
    (d : ℕ) (n : Fin w → (Fin d → ℤ)) (nfl : Fin d → ℤ) :=
  Σ κtop : ForestDecoration top d n,
    (B : P.parts) → GenDecoration (low B) d
      (fun k => κtop.1 ((blockRootEquiv top P).symm ⟨B, k⟩).toNode) nfl

noncomputable def assembleGenDecoration {d w : ℕ} (sig : Fin w → ℤˣ) (top : Fin w → TTree)
    (P : Finpartition (univ : Finset (GLeaf top))) (low : (B : P.parts) → Garden B.1.card)
    (hsig : ∀ B k, (low B).sig k = nodeSign sig ((blockRootEquiv top P).symm ⟨B, k⟩).1)
    (n : Fin w → (Fin d → ℤ)) (nfl : Fin d → ℤ)
    (x : BoundaryDecorationData top P low d n nfl) :
    GenDecoration (markedGardenGraft sig top P low hsig) d n nfl := by
  let labels := (x.1.1, fun B => (x.2 B).1)
  have hx : GraftMatching top P low labels := fun B k => ((x.2 B).2.2.1 k).symm
  let κ := graftAssembleLabels top P low labels
  have htop : (fun a => κ (topNodeEmbedding top P low a)) = x.1.1 :=
    funext (graftAssembleLabels_top top P low labels hx)
  have hlow (B : P.parts) : (fun a => κ (lowerNodeEmbedding top P low B a)) = (x.2 B).1 :=
    funext (graftAssembleLabels_lower top P low labels B)
  refine ⟨κ, (isDecoration_markedGardenGraft_iff sig top P low hsig κ).mpr ?_, ?_, ?_⟩
  · exact ⟨htop.symm ▸ x.1.2.1, fun B => (hlow B).symm ▸ (x.2 B).2.1⟩
  · intro j
    exact (graftAssembleLabels_top top P low labels hx (GNode.root top j)).trans (x.1.2.2 j)
  · intro ℓ hℓ
    obtain ⟨⟨B, l⟩, rfl⟩ := (gardenLeafEquiv top P low).symm.surjective ℓ
    have hm := markedGardenGraft_mark_lower sig top P low hsig B l
    have hf : (low B).IsFlower l := hm.symm.trans hℓ
    exact (congrArg κ (gardenLeaf_toNode_lower top P low B l)).trans
      ((graftAssembleLabels_lower top P low labels B l.toNode).trans ((x.2 B).2.2.2 l hf))

theorem assemble_splitGenDecoration {d w : ℕ} (sig : Fin w → ℤˣ) (top : Fin w → TTree)
    (P : Finpartition (univ : Finset (GLeaf top))) (low : (B : P.parts) → Garden B.1.card)
    (hsig : ∀ B k, (low B).sig k = nodeSign sig ((blockRootEquiv top P).symm ⟨B, k⟩).1)
    (n : Fin w → (Fin d → ℤ)) (nfl : Fin d → ℤ)
    (κ : GenDecoration (markedGardenGraft sig top P low hsig) d n nfl) :
    assembleGenDecoration sig top P low hsig n nfl (splitGenDecoration sig top P low hsig n nfl κ) = κ := by
  apply Subtype.ext
  exact (graftMatchingLabelsEquiv top P low).symm_apply_apply κ.1

end WaveTurbulence.Induct
