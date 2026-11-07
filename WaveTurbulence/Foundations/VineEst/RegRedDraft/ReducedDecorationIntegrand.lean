/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.RegRedDraft.FixedDecorationTimeIntegral
public import WaveTurbulence.Foundations.VineEst.RegRedDraft.AllTimeKernelNorm

/-! # Integrability of the actual reduced fixed-decoration summands -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.RegRed
open TTree Reg Reg.Skeleton MeasureTheory

noncomputable def reducedDecorationIntegrand {w d : ℕ} {S : Garden w} (D : ReconstructionData S)
    (hS : S.IsPlain) (L γ δ : ℝ) (F : ℕ → Mom d → ℝ)
    (layer : GNode (D.forest hS) → ℕ) (hLayer : IsLayering (D.garden hS) layer)
    (top : ℝ) (k₀ : Mom d) {n : Fin w → (Fin d → ℤ)} {nfl : Fin d → ℤ}
    (κ : GenDecoration (D.garden hS) d n nfl) (τ : GBranch S.tree → ℝ) : ℂ :=
  coreKernelIntegrand D hS L γ δ layer top k₀ (collapseGenDecoration D hS κ).1 τ *
    ∏ s : ReplacementSlot S, ∫ t, nativeKernelIntegrand D hS L γ δ F layer hLayer top k₀
      (collapseGenDecoration D hS κ).1 τ s (restrictRelativeDecorations D hS κ s) t

theorem integral_native_section_eq_reduced {w d : ℕ} {S : Garden w} (D : ReconstructionData S)
    (hS : S.IsPlain) (L γ δ : ℝ) (F : ℕ → Mom d → ℝ)
    (layer : GNode (D.forest hS) → ℕ) (hLayer : IsLayering (D.garden hS) layer)
    (top : ℝ) (k₀ : Mom d) {n : Fin w → (Fin d → ℤ)} {nfl : Fin d → ℤ}
    (κ : GenDecoration (D.garden hS) d n nfl) (τ : GBranch S.tree → ℝ) :
    (∫ t : (s : ReplacementSlot S) → NativeTimeBlock D s,
      kernelAllIntegrand L γ δ F (layeredReconstruction D hS layer hLayer) (fun _ => top) 0 k₀ κ
        ((sourceNativeTimeSplit D hS).symm (τ,t))) =
      reducedDecorationIntegrand D hS L γ δ F layer hLayer top k₀ κ τ := by
  have he : (fun t => kernelAllIntegrand L γ δ F (layeredReconstruction D hS layer hLayer)
      (fun _ => top) 0 k₀ κ ((sourceNativeTimeSplit D hS).symm (τ,t))) =
      (fun t : (s : ReplacementSlot S) → NativeTimeBlock D s =>
        coreKernelIntegrand D hS L γ δ layer top k₀ (collapseGenDecoration D hS κ).1 τ *
          ∏ s, nativeKernelIntegrand D hS L γ δ F layer hLayer top k₀
            (collapseGenDecoration D hS κ).1 τ s (restrictRelativeDecorations D hS κ s) (t s)) := by
    funext t
    have h := kernelAllIntegrand_reconstruction D hS L γ δ F layer hLayer top k₀ κ
      ((sourceNativeTimeSplit D hS).symm (τ,t))
    have hc := congrArg Prod.fst (sourceNativeTimeSplit_symm_clocks D hS τ t)
    have hn := congrArg Prod.snd (sourceNativeTimeSplit_symm_clocks D hS τ t)
    change nativeCoreClock D hS ((sourceNativeTimeSplit D hS).symm (τ,t)) = τ at hc
    change nativeTimeRestriction D hS ((sourceNativeTimeSplit D hS).symm (τ,t)) = t at hn
    rw [hc,hn] at h
    exact h
  apply (congrArg (fun g : (((s : ReplacementSlot S) → NativeTimeBlock D s) → ℂ) => ∫ t, g t) he).trans
  exact (integral_const_mul _ _).trans (congrArg
    (fun z => coreKernelIntegrand D hS L γ δ layer top k₀ (collapseGenDecoration D hS κ).1 τ * z)
      (integral_fintype_prod_volume_eq_prod _))

theorem integrable_reducedDecorationIntegrand {w d : ℕ} {S : Garden w} (D : ReconstructionData S)
    (hS : S.IsPlain) (L γ δ : ℝ) (F : ℕ → Mom d → ℝ)
    (layer : GNode (D.forest hS) → ℕ) (hLayer : IsLayering (D.garden hS) layer)
    (top : ℝ) (k₀ : Mom d) {n : Fin w → (Fin d → ℤ)} {nfl : Fin d → ℤ}
    (κ : GenDecoration (D.garden hS) d n nfl) :
    Integrable (reducedDecorationIntegrand D hS L γ δ F layer hLayer top k₀ κ) := by
  have hf := integrable_kernelAllIntegrand L γ δ F (layeredReconstruction D hS layer hLayer)
    (LGSpine.not_flowerParent_of_plain (D.garden hS) (D.garden_plain hS)) (fun _ => top) 0 k₀ κ
  have hi := (measurePreserving_sourceNativeTimeSplit D hS).symm.integrable_comp_of_integrable hf
  exact hi.integral_prod_left.congr (Filter.Eventually.of_forall
    (integral_native_section_eq_reduced D hS L γ δ F layer hLayer top k₀ κ))

theorem integral_norm_reducedDecorationIntegrand_le {w d : ℕ} {S : Garden w} (D : ReconstructionData S)
    (hS : S.IsPlain) (L γ δ : ℝ) (F : ℕ → Mom d → ℝ)
    (layer : GNode (D.forest hS) → ℕ) (hLayer : IsLayering (D.garden hS) layer)
    (top : ℝ) (k₀ : Mom d) {n : Fin w → (Fin d → ℤ)} {nfl : Fin d → ℤ}
    (κ : GenDecoration (D.garden hS) d n nfl) :
    (∫ τ, ‖reducedDecorationIntegrand D hS L γ δ F layer hLayer top k₀ κ τ‖) ≤
      ∫ τ, ‖kernelAllIntegrand L γ δ F (layeredReconstruction D hS layer hLayer) (fun _ => top) 0 k₀ κ τ‖ := by
  let f : (GBranch (D.forest hS) → ℝ) → ℂ :=
    kernelAllIntegrand L γ δ F (layeredReconstruction D hS layer hLayer) (fun _ => top) 0 k₀ κ
  have hf : Integrable f := integrable_kernelAllIntegrand L γ δ F (layeredReconstruction D hS layer hLayer)
    (LGSpine.not_flowerParent_of_plain (D.garden hS) (D.garden_plain hS)) _ _ _ κ
  have hmp := measurePreserving_sourceNativeTimeSplit D hS
  have hi := hmp.symm.integrable_comp_of_integrable hf
  have hr := integrable_reducedDecorationIntegrand D hS L γ δ F layer hLayer top k₀ κ
  have hm : (∫ τ, ‖reducedDecorationIntegrand D hS L γ δ F layer hLayer top k₀ κ τ‖) ≤
      ∫ τ, ∫ t, ‖f ((sourceNativeTimeSplit D hS).symm (τ,t))‖ := by
    apply integral_mono_ae hr.norm hi.norm.integral_prod_left
    apply Filter.Eventually.of_forall
    intro τ
    exact (congrArg norm (integral_native_section_eq_reduced D hS L γ δ F layer hLayer top k₀ κ τ)).symm.trans_le
      (norm_integral_le_integral_norm _)
  have ht : (∫ τ, ∫ t, ‖f ((sourceNativeTimeSplit D hS).symm (τ,t))‖) = ∫ τ, ‖f τ‖ :=
    (integral_prod _ hi.norm).symm.trans (hmp.symm.integral_comp' (fun τ => ‖f τ‖))
  exact hm.trans_eq ht

end WaveTurbulence.RegRed
