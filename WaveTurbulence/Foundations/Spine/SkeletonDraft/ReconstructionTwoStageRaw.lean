/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Spine.SkeletonDraft.ReconstructionSecondStagePairs
public import WaveTurbulence.Foundations.Spine.SkeletonDraft.RawValidityFaithfulness

/-! # Literal equality of a regular reconstruction and its bare-chain/couple two-stage form -/

public section
namespace WaveTurbulence.Reg.Skeleton

theorem ReconstructionData.secondStage_raw {w : ℕ} {S : Garden w}
    (D : ReconstructionData S) (hS : S.IsPlain) :
    (D.secondStage hS).raw (D.barePart.garden_plain hS) = D.raw hS := by
  exact Raw.eq_of_valid_sig_pairs _ _
    ((D.secondStage hS).raw_valid (D.barePart.garden_plain hS)) (D.raw_valid hS)
    rfl (D.secondStage_pairs hS)

theorem ReconstructionData.secondStage_decodes {w : ℕ} {S G : Garden w}
    (D : ReconstructionData S) (hS : S.IsPlain) (hd : D.Decodes hS G) :
    (D.secondStage hS).Decodes (D.barePart.garden_plain hS) G :=
  ⟨hd.1,(D.secondStage_raw hS).trans hd.2⟩

end WaveTurbulence.Reg.Skeleton
