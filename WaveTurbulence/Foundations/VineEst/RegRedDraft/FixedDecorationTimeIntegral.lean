/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.RegRedDraft.KernelIntegrandFactorization

/-! # Actual time integration of a fixed full decoration in native coordinates -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.RegRed
open TTree Reg Reg.Skeleton MeasureTheory

theorem sourceNativeTimeSplit_symm_clocks {w : ℕ} {S : Garden w} (D : ReconstructionData S)
    (hS : S.IsPlain) (τ : GBranch S.tree → ℝ) (t : (s : ReplacementSlot S) → NativeTimeBlock D s) :
    (nativeCoreClock D hS ((sourceNativeTimeSplit D hS).symm (τ,t)),
      nativeTimeRestriction D hS ((sourceNativeTimeSplit D hS).symm (τ,t))) = (τ,t) :=
  (sourceNativeTimeSplit_apply D hS _).symm.trans ((sourceNativeTimeSplit D hS).apply_symm_apply (τ,t))

/-- The actual full time integral of every fixed decoration factors into a core
integral and independent native time integrals. Integrability is derived from the
source kernel summand; there is no Fubini or factorization hypothesis. -/
theorem integral_kernelAllIntegrand_reconstruction {w d : ℕ} {S : Garden w} (D : ReconstructionData S)
    (hS : S.IsPlain) (L γ δ : ℝ) (F : ℕ → Mom d → ℝ)
    (layer : GNode (D.forest hS) → ℕ) (hLayer : IsLayering (D.garden hS) layer)
    (top : ℝ) (k₀ : Mom d) {n : Fin w → (Fin d → ℤ)} {nfl : Fin d → ℤ}
    (κ : GenDecoration (D.garden hS) d n nfl) :
    (∫ τ, kernelAllIntegrand L γ δ F (layeredReconstruction D hS layer hLayer) (fun _ => top) 0 k₀ κ τ) =
      ∫ τ : GBranch S.tree → ℝ, coreKernelIntegrand D hS L γ δ layer top k₀ (collapseGenDecoration D hS κ).1 τ *
        ∏ s : ReplacementSlot S, ∫ t, nativeKernelIntegrand D hS L γ δ F layer hLayer top k₀
          (collapseGenDecoration D hS κ).1 τ s (restrictRelativeDecorations D hS κ s) t := by
  let f : (GBranch (D.forest hS) → ℝ) → ℂ := kernelAllIntegrand L γ δ F (layeredReconstruction D hS layer hLayer) (fun _ => top) 0 k₀ κ
  have hf : Integrable f := integrable_kernelAllIntegrand L γ δ F (layeredReconstruction D hS layer hLayer)
    (LGSpine.not_flowerParent_of_plain (D.garden hS) (D.garden_plain hS)) _ _ _ κ
  apply (integral_sourceNativeTimeSplit D hS f hf).trans
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro τ
  have he : (fun t => f ((sourceNativeTimeSplit D hS).symm (τ,t))) =
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
  change (∫ t : (s : ReplacementSlot S) → NativeTimeBlock D s,
    f ((sourceNativeTimeSplit D hS).symm (τ,t))) = _
  apply (congrArg (fun g : (((s : ReplacementSlot S) → NativeTimeBlock D s) → ℂ) => ∫ t, g t) he).trans
  rw [integral_const_mul,integral_fintype_prod_volume_eq_prod]

end WaveTurbulence.RegRed
