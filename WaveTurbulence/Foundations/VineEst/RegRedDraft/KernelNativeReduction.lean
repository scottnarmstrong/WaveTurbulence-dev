/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.RegRedDraft.KernelRawReduction
public import WaveTurbulence.Foundations.VineEst.RegRedDraft.KernelPrefactors

/-! # Skeleton reduction with the actual native starred kernels -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.RegRed
open TTree Reg Reg.Skeleton MeasureTheory

theorem kernelK_native_reduction {w d : ℕ} {S : Garden w} (D : ReconstructionData S)
    (hS : S.IsPlain) (L γ δ : ℝ) (F : ℕ → Mom d → ℝ)
    (layer : GNode (D.forest hS) → ℕ) (hLayer : IsLayering (D.garden hS) layer)
    (top : ℝ) (k₀ : Mom d) (n : Fin w → (Fin d → ℤ)) (nfl : Fin d → ℤ)
    (hF : ∀ ℓ ∈ inputLeaves (D.garden hS),
      Summable fun n : Fin d → ℤ => |F (layer ℓ.toNode) (k₀+latticePoint L n)|) :
    kernelK L γ δ F (layeredReconstruction D hS layer hLayer) (fun _ => top) 0 k₀ n nfl =
      (coupling d L γ δ : ℂ)^S.order * S.zeta *
        ∑' κ : GenDecoration S d n nfl, ∫ τ : GBranch S.tree → ℝ,
          coreKernelIntegrand D hS L γ δ layer top k₀ κ.1 τ *
            ∏ s : ReplacementSlot S, nativeKernelValue D hS L γ δ F layer hLayer top k₀ κ.1 τ s := by
  let P := ∏ s : ReplacementSlot S, nativeKernelPrefactor D hS layer hLayer (coupling d L γ δ) s
  have hp : (coupling d L γ δ : ℂ)^(D.garden hS).order * (D.garden hS).zeta =
      ((coupling d L γ δ : ℂ)^S.order * S.zeta) * P := by
    change _ = ((coupling d L γ δ : ℂ)^S.order * S.zeta) *
      (∏ s : ReplacementSlot S, nativeKernelPrefactor D hS layer hLayer (coupling d L γ δ) s)
    rw [Fintype.prod_sum_type]
    exact (kernelPrefactor_reconstruction D hS layer hLayer (coupling d L γ δ)).trans (mul_assoc _ _ _)
  rw [kernelK_raw_reduction D hS L γ δ F layer hLayer top k₀ n nfl hF,hp,mul_assoc]
  apply congrArg (fun z => ((coupling d L γ δ : ℂ)^S.order * S.zeta) * z)
  rw [← tsum_mul_left]
  apply tsum_congr
  intro κ
  rw [← integral_const_mul]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro τ
  have hv := nativeKernelValue_prod_eq D hS L γ δ F layer hLayer top k₀ κ.1 τ
  exact (mul_left_comm P (coreKernelIntegrand D hS L γ δ layer top k₀ κ.1 τ) _).trans
    (congrArg (fun z => coreKernelIntegrand D hS L γ δ layer top k₀ κ.1 τ * z) hv).symm

theorem nativeKernelValue_prod_star {w d : ℕ} {S : Garden w} (D : ReconstructionData S)
    (hS : S.IsPlain) (L γ δ : ℝ) (F : ℕ → Mom d → ℝ)
    (layer : GNode (D.forest hS) → ℕ) (hLayer : IsLayering (D.garden hS) layer)
    (top : ℝ) (k₀ : Mom d) (κ : GNode S.tree → (Fin d → ℤ)) (τ : GBranch S.tree → ℝ) :
    (∏ s : ReplacementSlot S, nativeKernelValue D hS L γ δ F layer hLayer top k₀ κ τ s) =
      (∏ p : SourcePair S, KQstar L γ δ F (nativeCoupleLayered D hS layer hLayer p)
        (parentClock top τ (p.firstLeaf hS).toNode) (parentClock top τ (p.secondLeaf hS).toNode)
        (k₀+latticePoint L (κ (p.firstLeaf hS).toNode))) *
      (∏ b : GBranch S.tree, KTstar L γ δ F (nativeChainLayered D hS layer hLayer b)
        (parentClock top τ b.toNode) (τ b) (k₀+latticePoint L (κ b.toNode))) := by
  rw [Fintype.prod_sum_type]
  apply congrArg₂ (· * ·)
  · exact Finset.prod_congr rfl (fun p _ => nativeKernelValue_couple_eq_KQstar D hS L γ δ F layer hLayer top k₀ κ τ p)
  · rfl

end WaveTurbulence.RegRed
