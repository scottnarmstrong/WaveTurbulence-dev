/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Spine.SkeletonDraft.ForwardACollapse
public import WaveTurbulence.Foundations.Spine.SkeletonDraft.ForwardBCollapse
public import WaveTurbulence.Foundations.Spine.SkeletonDraft.Termination

/-! # Every guarded forward source construction history is an actual inverse garden reduction -/

public section
namespace WaveTurbulence.Reg.Skeleton

theorem Expand.gardenStep {w : ℕ} {R T : Raw w} (h : Expand R T) (S G : Garden w)
    (hS : S.IsPlain) (hG : G.IsPlain) (hSR : rawOfGarden S = R) (hGT : rawOfGarden G = T) :
    GardenStep G S := by
  cases h with
  | opA x y k hR hp =>
    apply gardenStep_of_raw_opA S G hS hG x y k
    · rw [hSR]
      exact hp
    · rw [hSR]
      exact hGT
  | opB a m hR ha =>
    apply gardenStep_of_raw_opB S G hS hG a m
    · have ht := congrArg Raw.tree hSR
      change S.tree = R.tree at ht
      rw [ht]
      exact ha
    · rw [hSR]
      exact hGT

/-- A source construction history produces actual ordinary intermediate gardens and the full native
inverse history; the source carrier at the end is constructed, never assumed as an extra premise. -/
theorem Reconstructs.reverse_garden {w : ℕ} {R T : Raw w} (h : Reconstructs R T)
    (G : Garden w) (hG : G.IsPlain) (he : rawOfGarden G = T) :
    ∃ S : Garden w, S.IsPlain ∧ rawOfGarden S = R ∧ GardenReduces G S := by
  induction h generalizing G with
  | refl => exact ⟨G,hG,he,Relation.ReflTransGen.refl⟩
  | @tail T U hr hs ih =>
    let H := gardenOfRaw T hs.source_valid
    have hH : H.IsPlain := gardenOfRaw_plain _ _
    have hHR : rawOfGarden H = T := rawOfGarden_gardenOfRaw _ _
    have hstep : GardenStep G H := hs.gardenStep H G hH hG hHR he
    obtain ⟨S,hS,hSR,hHS⟩ := ih H hH hHR
    exact ⟨S,hS,hSR,hHS.head hstep⟩

/-- The source's forward A/B construction relation gives the same actual inverse-surgery history. -/
theorem gardenReduces_of_reconstructs {w : ℕ} (S G : Garden w) (hS : S.IsPlain) (hG : G.IsPlain)
    (h : Reconstructs (rawOfGarden S) (rawOfGarden G)) : GardenReduces G S := by
  obtain ⟨H,hH,he,hGH⟩ := h.reverse_garden G hG rfl
  have hg : H = S := rawOfGarden_injective_plain hH hS he
  exact hg ▸ hGH

end WaveTurbulence.Reg.Skeleton
