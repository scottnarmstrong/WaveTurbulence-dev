/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Spine.SkeletonDraft.ReconstructionAClosure
public import WaveTurbulence.Foundations.Spine.SkeletonDraft.ReconstructionBClosure
public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.ReconstructionIdentityRaw
public import WaveTurbulence.Foundations.Spine.SkeletonDraft.SourceExpansionHistories

/-! # Every source reconstruction history gives actual regular replacement data -/

public section
namespace WaveTurbulence.Reg.Skeleton

theorem Expand.exists_decoding {w : ℕ} {S G H : Garden w} {R T : Raw w}
    (D : ReconstructionData S) (hS : S.IsPlain) (hd : D.Decodes hS G)
    (hH : H.IsPlain) (h : Expand R T) (hGR : rawOfGarden G = R) (hHT : rawOfGarden H = T) :
    ∃ E : ReconstructionData S, E.Decodes hS H := by
  cases h with
  | opA x y k hR hp =>
    apply D.opA_decodes hS hd x y k hH
    · have he := congrArg Raw.pairs hGR
      change sourcePairs G = R.pairs at he
      exact he.symm ▸ hp
    · exact hHT.trans (congrArg (fun A : Raw w => A.opA x y k) hGR).symm
  | opB a m hR ha =>
    apply D.opB_decodes hS hd a m hH
    · have he := congrArg Raw.tree hGR
      change G.tree = R.tree at he
      rw [he]
      exact ha
    · exact hHT.trans (congrArg (fun A : Raw w => A.opB a m) hGR).symm

/-- DH21 structure theorem existence: the source A/B construction history is decoded
by literal regular trees at branches and regular couples at canonical leaf pairs. -/
theorem exists_reconstructionData_of_reconstructs {w : ℕ} (S G : Garden w)
    (hS : S.IsPlain) (hG : G.IsPlain)
    (h : Reconstructs (rawOfGarden S) (rawOfGarden G)) :
    ∃ D : ReconstructionData S, D.Decodes hS G := by
  suffices hh : ∀ {T : Raw w}, Reconstructs (rawOfGarden S) T →
      ∀ (H : Garden w), H.IsPlain → rawOfGarden H = T →
        ∃ D : ReconstructionData S, D.Decodes hS H from hh h G hG rfl
  intro T hr
  induction hr with
  | refl =>
    intro H hH he
    exact ⟨ReconstructionData.identity S,hH,(ReconstructionData.identity_raw S hS).trans he.symm⟩
  | @tail T U hr hs ih =>
    intro H hH he
    let K := gardenOfRaw T hs.source_valid
    have hK : K.IsPlain := gardenOfRaw_plain _ _
    have hKR : rawOfGarden K = T := rawOfGarden_gardenOfRaw _ _
    obtain ⟨D,hd⟩ := ih K hK hKR
    exact hs.exists_decoding D hS hd hH hKR he

end WaveTurbulence.Reg.Skeleton
