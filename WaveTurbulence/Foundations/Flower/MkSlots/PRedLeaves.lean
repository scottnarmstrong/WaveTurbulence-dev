/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Flower.MkSlots.PRedRed
public import WaveTurbulence.Foundations.Flower.Stage1WNoVine.WLeaves

/-! # B3s MK-SLOTS: the pinned weighted leafwise skeleton reduction (PRED, part 3)

The pinned twin of `Stage1WNoVine.WLeaves`.  For a leaf profile `H`, a node weight `W` bounded by `Cw` and ANY pins
`fixG` on the branches of the reconstructed garden, the decoration-restricted pinned weighted leaf kernel
`kernelLeavesSelNWF … fixG` of the reconstruction is the skeleton sum of the core integral against
`fixMeasure (fixCore D hS fixG)` of the core phase times the product over the replacement slots of the pinned weighted
slot kernels `slotFnNWF … fixG` (native pins `fixNative D hS fixG s`): `kernelLeaves_skeleton_reduction_selNWF`.

* `kernelLeavesSelNWF`, `kernelLeavesSelNWF_none` (no pins: `WLeaves.kernelLeavesSelNW`);
* `slotFnNWF`, `slotFnNWF_none` (no pins: `WLeaves.slotFnNW`), `prod_slotFnNWF`;
* **`kernelLeaves_skeleton_reduction_selNWF`**. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace WaveTurbulence.Flower.MkSlots
open WaveTurbulence TTree Reg Reg.Skeleton MeasureTheory WaveTurbulence.RegRed WaveTurbulence.RegRedLeaf
  WaveTurbulence.LGSpine WaveTurbulence.Flower.Stage1WNoVine

/-! ### The pinned weighted slot kernels as functions of the two clock times -/

/-- **The pinned weighted slot kernels**: `WLeaves.slotFnNW` with the native kernel `kernelNodeWF` at the native
pins `fixNative D hS fixG s` (for a chain slot the native branches are `NativeClockBranch D (.inr b)`, the pins read
through `chainBranchEquiv` inside `replacementTimeIndexEquiv`). -/
def slotFnNWF {w d : ℕ} {S : Garden w} (D : ReconstructionData S) (hS : S.IsPlain) (L γ δ : ℝ)
    (H : LeafProfiles w d) (W : GNode (D.forest hS) → Mom d → ℂ)
    (layer : GNode (D.forest hS) → ℕ) (hLayer : IsLayering (D.garden hS) layer)
    (fixG : GBranch (D.forest hS) → Option ℝ) :
    ReplacementSlot S → (Fin 2 → ℝ) → Mom d → ℂ
  | .inl p => fun ts k => kernelNodeWF L γ δ (nativeCoupleLayered D hS layer hLayer p)
      (fun a => H ((nativeCoupleForest D hS p).nodeEmbedding a).1)
      (fun k' => ∏ a, W ((nativeCoupleForest D hS p).nodeEmbedding a) (k' a))
      (fun b => if b.1.1 = 0 then ts 0 else ts 1) 0 k (fun _ => 0) 0 (fixNative D hS fixG (.inl p))
  | .inr b => fun ts k => kernelNodeWF L γ δ (nativeChainLayered D hS layer hLayer b)
      (fun a => H (chainContextNode D hS b a).1)
      (fun k' => ∏ a, W (chainContextNode D hS b a) (k' a))
      (fun _ => ts 0) (ts 1) k (fun _ => 0) 0 (fixNative D hS fixG (.inr b))

/-- **No pins: the pinned weighted slot kernels are `WLeaves.slotFnNW`.** -/
theorem slotFnNWF_none {w d : ℕ} {S : Garden w} (D : ReconstructionData S) (hS : S.IsPlain) (L γ δ : ℝ)
    (H : LeafProfiles w d) (W : GNode (D.forest hS) → Mom d → ℂ)
    (layer : GNode (D.forest hS) → ℕ) (hLayer : IsLayering (D.garden hS) layer) :
    slotFnNWF D hS L γ δ H W layer hLayer (fun _ => none) = slotFnNW D hS L γ δ H W layer hLayer := by
  funext s ts k
  cases s with
  | inl p =>
    exact kernelNodeWF_none L γ δ (nativeCoupleLayered D hS layer hLayer p)
      (fun a => H ((nativeCoupleForest D hS p).nodeEmbedding a).1)
      (fun k' => ∏ a, W ((nativeCoupleForest D hS p).nodeEmbedding a) (k' a))
      (fun b => if b.1.1 = 0 then ts 0 else ts 1) 0 k
      (noFlowerParent_of_noFlower _ (nativeCouple_noFlower D hS p)) (fun _ => 0) 0
  | inr b =>
    exact kernelNodeWF_none L γ δ (nativeChainLayered D hS layer hLayer b)
      (fun a => H (chainContextNode D hS b a).1)
      (fun k' => ∏ a, W (chainContextNode D hS b a) (k' a))
      (fun _ => ts 0) (ts 1) k
      (noFlowerParent_of_noFlower _ (decodedTree_noFlower _ _)) (fun _ => 0) 0

end WaveTurbulence.Flower.MkSlots
