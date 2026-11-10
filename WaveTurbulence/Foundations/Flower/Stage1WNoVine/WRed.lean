/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.Stage1WNoVine.WNode

/-! # STAGE1W-O4: the node-weighted skeleton reduction (row T2, part 2)

The weighted analogue of REGRED-LEAF's `tsum_integral_sel_reduction` and `kernelNode_native_reduction_sel`:
for a node weight `W` bounded by `Cw`, the decoration-restricted weighted sum of the reconstructed garden is the
skeleton sum of the core integral against the product of the weighted native kernels
(`kernelNodeW_native_reduction_sel`).  Since the weight depends only on the decoration, every step is main's step
multiplied by the (bounded) decoration weight. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace WaveTurbulence.Flower.Stage1WNoVine
open WaveTurbulence TTree Reg Reg.Skeleton MeasureTheory WaveTurbulence.RegRed WaveTurbulence.RegRedLeaf

section Reduction

variable {w d : ℕ} {S : Garden w} (D : ReconstructionData S) (hS : S.IsPlain) (L γ δ : ℝ)
    (A : GNode (D.forest hS) → Mom d → ℝ) (W : GNode (D.forest hS) → Mom d → ℂ)
    (layer : GNode (D.forest hS) → ℕ) (hLayer : IsLayering (D.garden hS) layer)
    (tt : Fin w → ℝ) (k₀ : Mom d)

theorem norm_fullWeight_le (Cw : ℝ) (hCw : 0 ≤ Cw) (hW : ∀ z x, ‖W z x‖ ≤ Cw)
    (k : GNode (D.forest hS) → Mom d) :
    ‖∏ z, W z (k z)‖ ≤ Cw ^ Fintype.card (GNode (D.forest hS)) := by
  refine (Finset.norm_prod_le _ _).trans ?_
  exact (Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) (fun a _ => hW _ _)).trans_eq
    (by rw [Finset.prod_const, Finset.card_univ])

end Reduction

end WaveTurbulence.Flower.Stage1WNoVine
