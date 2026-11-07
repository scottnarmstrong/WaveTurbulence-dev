/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.RegRedLeaf.NativeSummable

/-! # Time integration of a fixed decoration with a node profile (REGRED-LEAF)

REGRED `FixedDecorationTimeIntegral` for a node profile `A`. -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.RegRedLeaf
open TTree Reg Reg.Skeleton MeasureTheory WaveTurbulence.RegRed


/-- The actual full time integral of every fixed decoration factors into a core
integral and independent native time integrals. Integrability is derived from the
source kernel summand; there is no Fubini or factorization hypothesis. -/
theorem integral_kernelAllIntegrandN_reconstruction {w d : ℕ} {S : Garden w} (D : ReconstructionData S)
    (hS : S.IsPlain) (L γ δ : ℝ) (A : GNode (D.forest hS) → Mom d → ℝ)
    (layer : GNode (D.forest hS) → ℕ) (hLayer : IsLayering (D.garden hS) layer)
    (tt : Fin w → ℝ) (k₀ : Mom d) {n : Fin w → (Fin d → ℤ)} {nfl : Fin d → ℤ}
    (κ : GenDecoration (D.garden hS) d n nfl) :
    (∫ τ, kernelAllIntegrandN L γ δ (layeredReconstruction D hS layer hLayer) A (fun b => tt b.1.1) 0 k₀ κ τ) =
      ∫ τ : GBranch S.tree → ℝ, coreKernelIntegrandW D hS L γ δ layer tt k₀ (collapseGenDecoration D hS κ).1 τ *
        ∏ s : ReplacementSlot S, ∫ t, nativeKernelIntegrandN D hS L γ δ A layer hLayer tt k₀
          (collapseGenDecoration D hS κ).1 τ s (restrictRelativeDecorations D hS κ s) t := by
  let f : (GBranch (D.forest hS) → ℝ) → ℂ := kernelAllIntegrandN L γ δ (layeredReconstruction D hS layer hLayer) A (fun b => tt b.1.1) 0 k₀ κ
  have hf : Integrable f := integrable_kernelAllIntegrandN L γ δ (layeredReconstruction D hS layer hLayer) A
    (LGSpine.not_flowerParent_of_plain (D.garden hS) (D.garden_plain hS)) _ _ _ κ
  apply (integral_sourceNativeTimeSplit D hS f hf).trans
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro τ
  have he : (fun t => f ((sourceNativeTimeSplit D hS).symm (τ,t))) =
      (fun t : (s : ReplacementSlot S) → NativeTimeBlock D s =>
        coreKernelIntegrandW D hS L γ δ layer tt k₀ (collapseGenDecoration D hS κ).1 τ *
          ∏ s, nativeKernelIntegrandN D hS L γ δ A layer hLayer tt k₀
            (collapseGenDecoration D hS κ).1 τ s (restrictRelativeDecorations D hS κ s) (t s)) := by
    funext t
    have h := kernelAllIntegrandN_reconstruction D hS L γ δ A layer hLayer tt k₀ κ
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


end WaveTurbulence.RegRedLeaf
