/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Flower.MkSlots.PRedNode
public import WaveTurbulence.Foundations.Flower.MkSlots.RedFix
public import WaveTurbulence.Foundations.Flower.Stage1WNoVine.WRed

/-! # B3s MK-SLOTS: the pinned node-weighted skeleton reduction (PRED, part 2)

The pinned twin of `Stage1WNoVine.WNode` (native part) and `Stage1WNoVine.WRed`.  For pins
`fixG : GBranch (D.forest hS) → Option ℝ` on the reconstructed garden, the decoration-restricted weighted sum of the
`fixMeasure fixG` integrals of the literal summand is the skeleton sum of the core integral against
`fixMeasure (fixCore D hS fixG)` of the core integrand times the pinned weighted native kernels, each native time
integral being against `fixMeasure (fixNative D hS fixG s)` (`kernelNodeWF_native_reduction_selNWF`).

The steps are those of `WRed` with `∂(fixMeasure …)` inserted: the time factorization is
`RedFix.integral_kernelAllIntegrandN_reconstruction_fix`, integrability and the L¹ bounds come from
`PRedNode` (support in the unit layer box) through the pinned split `measurePreserving_sourceNativeTimeSplit_fix`. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace WaveTurbulence.Flower.MkSlots
open WaveTurbulence TTree Reg Reg.Skeleton MeasureTheory WaveTurbulence.RegRed WaveTurbulence.RegRedLeaf
  WaveTurbulence.Flower.Stage1WNoVine

theorem norm_prod_le_pow_card {ι : Type*} [Fintype ι] (f : ι → ℂ) (Cw : ℝ) (hf : ∀ i, ‖f i‖ ≤ Cw) :
    ‖∏ i, f i‖ ≤ Cw ^ Fintype.card ι := by
  refine (Finset.norm_prod_le _ _).trans ?_
  exact (Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) (fun a _ => hf a)).trans_eq
    (by rw [Finset.prod_const, Finset.card_univ])

/-! ### The pinned weighted native kernels -/

section Native

variable {w d : ℕ} {S : Garden w} (D : ReconstructionData S) (hS : S.IsPlain) (L γ δ : ℝ)
    (A : GNode (D.forest hS) → Mom d → ℝ) (W : GNode (D.forest hS) → Mom d → ℂ)
    (layer : GNode (D.forest hS) → ℕ) (hLayer : IsLayering (D.garden hS) layer)
    (tt : Fin w → ℝ) (k₀ : Mom d) (κ : GNode S.tree → (Fin d → ℤ)) (τ : GBranch S.tree → ℝ)
    (fixG : GBranch (D.forest hS) → Option ℝ)

end Native

/-! ### The pinned reduced decoration integrand -/

section Reduction

variable {w d : ℕ} {S : Garden w} (D : ReconstructionData S) (hS : S.IsPlain) (L γ δ : ℝ)
    (A : GNode (D.forest hS) → Mom d → ℝ) (W : GNode (D.forest hS) → Mom d → ℂ)
    (layer : GNode (D.forest hS) → ℕ) (hLayer : IsLayering (D.garden hS) layer)
    (tt : Fin w → ℝ) (k₀ : Mom d) (fixG : GBranch (D.forest hS) → Option ℝ)

end Reduction

end WaveTurbulence.Flower.MkSlots
