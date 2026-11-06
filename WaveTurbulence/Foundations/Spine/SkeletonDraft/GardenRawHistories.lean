/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Spine.SkeletonDraft.SourceExpansionHistories
public import WaveTurbulence.Foundations.Spine.SkeletonDraft.MiniAOrientation

/-! # Native inverse source histories and guarded forward construction histories agree exactly -/

public section
namespace WaveTurbulence.Reg.Skeleton

theorem GardenStep.raw_reconstructs {w : ℕ} {G H : Garden w} (h : GardenStep G H) :
    Reconstructs (rawOfGarden H) (rawOfGarden G) := by
  cases h with
  | opA hG b c k hm =>
    rcases Int.units_eq_one_or (nodeSign G.sig b.1) with hb | hb
    · exact Relation.ReflTransGen.single (hm.predecessor hG hb)
    · have hc : nodeSign G.sig c.1 = 1 := by
        have he : nodeSign G.sig c.1 = -nodeSign G.sig b.1 := hm.1
        rw [hb,neg_neg] at he
        exact he
      have hr : Reconstructs (rawOfGarden (collapseCoupleGarden (hm.flip.isSubCouple hG)))
          (rawOfGarden G) := Relation.ReflTransGen.single (hm.flip.predecessor hG hc)
      have he := congrArg rawOfGarden (hm.collapse_flip_eq hG)
      exact he ▸ hr
  | opB hG b c k hm => exact Relation.ReflTransGen.single (hm.predecessor hG)

theorem GardenReduces.raw_reconstructs {w : ℕ} {G H : Garden w} (h : GardenReduces G H) :
    Reconstructs (rawOfGarden H) (rawOfGarden G) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail hr hs ih => exact hs.raw_reconstructs.trans ih

/-- No source-construction or inverse-surgery semantics are lost by the garden carrier bridge. -/
theorem gardenReduces_iff_reconstructs {w : ℕ} (S G : Garden w) (hS : S.IsPlain) (hG : G.IsPlain) :
    GardenReduces G S ↔ Reconstructs (rawOfGarden S) (rawOfGarden G) :=
  ⟨GardenReduces.raw_reconstructs,gardenReduces_of_reconstructs S G hS hG⟩

end WaveTurbulence.Reg.Skeleton
