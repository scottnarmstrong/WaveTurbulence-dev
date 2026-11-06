/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Spine.SkeletonDraft.ReconstructionTwoStageRaw
public import WaveTurbulence.Foundations.Spine.SkeletonDraft.ReconstructionEraseAllCouples
public import WaveTurbulence.Foundations.Spine.SkeletonDraft.BareInflationTrace
public import WaveTurbulence.Foundations.Spine.SkeletonDraft.ReconstructionIdentityCore

/-! # Every literal regular reconstruction contracts to its exact original core

DH21 Proposition 4.13 and DH21-2 Proposition 4.4, construction-to-reduction direction.
-/

public section
namespace WaveTurbulence.Reg.Skeleton

theorem ReconstructionData.reduction_trace {w : ℕ} {S : Garden w}
    (D : ReconstructionData S) (hS : S.IsPlain) (G : Garden w) (hd : D.Decodes hS G) :
    ∃ T : ReductionTrace G S, ∀ b : GBranch S.tree, (T.branches b).1 = D.corePosition b := by
  let H := D.barePart.garden hS
  let E := D.secondStage hS
  have hE : E.Decodes (D.barePart.garden_plain hS) G := D.secondStage_decodes hS hd
  obtain ⟨K,hK,T,hT⟩ := E.eraseAllCouples_trace (D.barePart.garden_plain hS) G hE
  have hidentity : E.eraseAllCouples = ReconstructionData.identity H :=
    ReconstructionData.ext_tree_couple _ _ rfl rfl
  have heq : K = H := rawOfGarden_injective_plain hK.1 (D.barePart.garden_plain hS)
    (hK.2.symm.trans ((congrArg (fun E : ReconstructionData H => E.raw (D.barePart.garden_plain hS)) hidentity).trans
      (ReconstructionData.identity_raw H (D.barePart.garden_plain hS))))
  subst K
  obtain ⟨U,hU⟩ := D.barePart.bareInflation_trace hS D.barePart_isBare H (D.barePart.garden_decodes hS)
  refine ⟨ReductionTrace.trans T U,?_⟩
  intro b
  change (T.branches (U.branches b)).1 = _
  exact (hT _).trans ((hU b).trans (D.barePart_corePosition b))

end WaveTurbulence.Reg.Skeleton
