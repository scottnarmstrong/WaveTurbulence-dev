/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.RegRedDraft.NativeChainLayering
public import WaveTurbulence.Foundations.RegStruct.ReverseRange

/-! # Native starred kernels are carried by actual source-regular objects -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.RegRed
open TTree Reg Reg.Skeleton

theorem nativeCoupleLayered_isRegular {w : ℕ} {S : Garden w} (D : ReconstructionData S)
    (hS : S.IsPlain) (layer : GNode (D.forest hS) → ℕ)
    (hLayer : IsLayering (D.garden hS) layer) (p : SourcePair S) :
    IsRegularCouple (nativeCoupleLayered D hS layer hLayer p).garden := by
  rw [nativeCoupleLayered_garden]
  exact wf_decodedCouple_isRegular _ (D.couple_wf p)

theorem nativeChainLayered_isRegular {w : ℕ} {S : Garden w} (D : ReconstructionData S)
    (hS : S.IsPlain) (layer : GNode (D.forest hS) → ℕ)
    (hLayer : IsLayering (D.garden hS) layer) (b : GBranch S.tree) :
    IsRegularTree (nativeChainLayered D hS layer hLayer b).garden :=
  wf_decodedTree_isRegular _ (D.tree_wf b) _

end WaveTurbulence.RegRed
