/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.Stage1WNoVine.WRed
public import WaveTurbulence.Foundations.Stage1.Represents.RepAsm2
public import WaveTurbulence.Foundations.Stage1.Represents.RepSlot2

/-! # STAGE1W-O4: the weighted leafwise skeleton reduction (row T2, part 3)

For a leaf profile `H` and a node weight `W` (bounded by `Cw`), the decoration-restricted weighted leaf kernel of a
reconstructed garden is the skeleton sum of the core integral against the product over the replacement slots of
the weighted native kernels `slotFnNW` (`kernelLeaves_skeleton_reduction_selNW`, `prod_slotFnNW`); this is the shape
consumed by the assembly (`asmOf`, with `Rep.Fn = slotFnNW`). -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace WaveTurbulence.Flower.Stage1WNoVine
open WaveTurbulence TTree Reg Reg.Skeleton MeasureTheory WaveTurbulence.RegRed WaveTurbulence.RegRedLeaf
  WaveTurbulence.LGSpine

/-! ### The weighted slot kernels as functions of the two clock times -/

/-- The weighted native kernel of a slot as a function of its two clock times and its momentum. -/
def slotFnNW {w d : ℕ} {S : Garden w} (D : ReconstructionData S) (hS : S.IsPlain) (L γ δ : ℝ)
    (H : LeafProfiles w d) (W : GNode (D.forest hS) → Mom d → ℂ)
    (layer : GNode (D.forest hS) → ℕ) (hLayer : IsLayering (D.garden hS) layer) :
    ReplacementSlot S → (Fin 2 → ℝ) → Mom d → ℂ
  | .inl p => fun ts k => kernelNodeW L γ δ (nativeCoupleLayered D hS layer hLayer p)
      (fun a => H ((nativeCoupleForest D hS p).nodeEmbedding a).1)
      (fun k' => ∏ a, W ((nativeCoupleForest D hS p).nodeEmbedding a) (k' a))
      (fun b => if b.1.1 = 0 then ts 0 else ts 1) 0 k (fun _ => 0) 0
  | .inr b => fun ts k => kernelNodeW L γ δ (nativeChainLayered D hS layer hLayer b)
      (fun a => H (chainContextNode D hS b a).1)
      (fun k' => ∏ a, W (chainContextNode D hS b a) (k' a))
      (fun _ => ts 0) (ts 1) k (fun _ => 0) 0

end WaveTurbulence.Flower.Stage1WNoVine
