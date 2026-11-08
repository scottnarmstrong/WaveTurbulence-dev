/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Flower.MkSlots.FixMeasure
public import WaveTurbulence.Foundations.Stage1.RegRedLeaf.TimeIntegral

/-! # B3s MK-SLOTS: the pinned time factorization of a reconstructed garden (REGRED-LEAF, pinned)

Main's `RegRedLeaf.integral_kernelAllIntegrandN_reconstruction` factors the full time integral of a fixed decoration
of a reconstructed garden into the skeleton core integral and the native (slot) integrals, through the coordinate
relabeling `sourceNativeTimeSplit`. Here the same factorization holds for the PINNED measure `fixMeasure fixG` on
the garden's time vectors: the core pins `fixCore` and the native pins `fixNative s` are the pins read through the
same relabeling.

* `fixCore`, `fixNative`;
* `measurePreserving_sourceNativeTimeSplit_fix`;
* **`integral_kernelAllIntegrandN_reconstruction_fix`**. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open MeasureTheory
open WaveTurbulence WaveTurbulence.RegRed WaveTurbulence.RegRedLeaf WaveTurbulence.Reg WaveTurbulence.Reg.Skeleton

namespace WaveTurbulence.Flower.MkSlots

variable {w : ℕ} {S : Garden w} (D : ReconstructionData S) (hS : S.IsPlain)

/-- The pins of the skeleton core branches. -/
def fixCore (fixG : GBranch (D.forest hS) → Option ℝ) : GBranch S.tree → Option ℝ :=
  fun b => fixG (D.coreBranch hS b)

/-- The pins of the native branches of a slot. -/
def fixNative (fixG : GBranch (D.forest hS) → Option ℝ) (s : ReplacementSlot S) :
    NativeClockBranch D s → Option ℝ :=
  fun q => fixG (sourceBranchEquiv D hS (.inr ((replacementTimeIndexEquiv D).symm ⟨s, q⟩)))

/-- **The pinned time split.** -/
theorem measurePreserving_sourceNativeTimeSplit_fix (fixG : GBranch (D.forest hS) → Option ℝ) :
    MeasurePreserving (sourceNativeTimeSplit D hS) (fixMeasure fixG)
      ((fixMeasure (fixCore D hS fixG)).prod (Measure.pi fun s => fixMeasure (fixNative D hS fixG s))) := by
  let e := sourceBranchEquiv D hS
  let fixSig : (Σ s : ReplacementSlot S, NativeClockBranch D s) → Option ℝ := fun z => fixNative D hS fixG z.1 z.2
  have h₁ : MeasurePreserving (MeasurableEquiv.piCongrLeft (fun _ => ℝ) e).symm (fixMeasure fixG)
      (fixMeasure (fixG ∘ e)) := (measurePreserving_piCongrLeft_fix e fixG).symm
  have h₂ := measurePreserving_sumPiEquivProdPi_fix (fixG ∘ e)
  have hS1 : MeasurePreserving (sourceTimeSplit D hS) (fixMeasure fixG)
      ((fixMeasure (fixG ∘ e ∘ Sum.inl)).prod (fixMeasure (fixG ∘ e ∘ Sum.inr))) := h₂.comp h₁
  have heq : (fixSig ∘ (replacementTimeIndexEquiv D)) = (fixG ∘ e ∘ Sum.inr) := by
    funext x
    simp [fixSig, fixNative, e]
  have h₃ : MeasurePreserving (MeasurableEquiv.piCongrLeft (fun _ => ℝ) (replacementTimeIndexEquiv D))
      (fixMeasure (fixG ∘ e ∘ Sum.inr)) (fixMeasure fixSig) := by
    rw [← heq]
    exact measurePreserving_piCongrLeft_fix (replacementTimeIndexEquiv D) fixSig
  have h₄ := measurePreserving_piCurry_fix (NativeClockBranch D) fixSig
  have hR : MeasurePreserving (replacementTimeSplit D) (fixMeasure (fixG ∘ e ∘ Sum.inr))
      (Measure.pi fun s => fixMeasure (fixNative D hS fixG s)) := h₄.comp h₃
  have hp : MeasurePreserving (Prod.map (id : (GBranch S.tree → ℝ) → _) (replacementTimeSplit D))
      ((fixMeasure (fixG ∘ e ∘ Sum.inl)).prod (fixMeasure (fixG ∘ e ∘ Sum.inr)))
      ((fixMeasure (fixCore D hS fixG)).prod (Measure.pi fun s => fixMeasure (fixNative D hS fixG s))) := by
    refine ⟨measurable_id.prodMap (replacementTimeSplit D).measurable, ?_⟩
    rw [← Measure.map_prod_map _ _ measurable_id (replacementTimeSplit D).measurable, Measure.map_id, hR.map_eq]
    rfl
  exact hp.comp hS1

/-- **The pinned time factorization** of a fixed decoration: the `fixMeasure` integral of the full integrand is the
pinned core integral of the core integrand times the pinned native integrals. -/
theorem integral_kernelAllIntegrandN_reconstruction_fix {d : ℕ} (L γ δ : ℝ) (A : GNode (D.forest hS) → Mom d → ℝ)
    (layer : GNode (D.forest hS) → ℕ) (hLayer : IsLayering (D.garden hS) layer)
    (tt : Fin w → ℝ) (k₀ : Mom d) {n : Fin w → (Fin d → ℤ)} {nfl : Fin d → ℤ}
    (κ : GenDecoration (D.garden hS) d n nfl) (fixG : GBranch (D.forest hS) → Option ℝ)
    (hf : Integrable (kernelAllIntegrandN L γ δ (layeredReconstruction D hS layer hLayer) A (fun b => tt b.1.1) 0
      k₀ κ) (fixMeasure fixG)) :
    (∫ τ, kernelAllIntegrandN L γ δ (layeredReconstruction D hS layer hLayer) A (fun b => tt b.1.1) 0 k₀ κ τ
        ∂(fixMeasure fixG)) =
      ∫ τ, coreKernelIntegrandW D hS L γ δ layer tt k₀ (collapseGenDecoration D hS κ).1 τ *
        ∏ s : ReplacementSlot S, ∫ t, nativeKernelIntegrandN D hS L γ δ A layer hLayer tt k₀
          (collapseGenDecoration D hS κ).1 τ s (restrictRelativeDecorations D hS κ s) t
            ∂(fixMeasure (fixNative D hS fixG s))
        ∂(fixMeasure (fixCore D hS fixG)) := by
  let f : (GBranch (D.forest hS) → ℝ) → ℂ :=
    kernelAllIntegrandN L γ δ (layeredReconstruction D hS layer hLayer) A (fun b => tt b.1.1) 0 k₀ κ
  have hmp := measurePreserving_sourceNativeTimeSplit_fix D hS fixG
  have hi := hmp.symm.integrable_comp_of_integrable hf
  change ∫ τ, f τ ∂(fixMeasure fixG) = _
  apply ((hmp.symm.integral_comp' f).symm.trans (integral_prod _ hi)).trans
  refine integral_congr_ae (ae_of_all _ fun τ => ?_)
  have he : (fun t => f ((sourceNativeTimeSplit D hS).symm (τ, t))) =
      (fun t : (s : ReplacementSlot S) → NativeTimeBlock D s =>
        coreKernelIntegrandW D hS L γ δ layer tt k₀ (collapseGenDecoration D hS κ).1 τ *
          ∏ s, nativeKernelIntegrandN D hS L γ δ A layer hLayer tt k₀
            (collapseGenDecoration D hS κ).1 τ s (restrictRelativeDecorations D hS κ s) (t s)) := by
    funext t
    have h := kernelAllIntegrandN_reconstruction D hS L γ δ A layer hLayer tt k₀ κ
      ((sourceNativeTimeSplit D hS).symm (τ, t))
    have hc := congrArg Prod.fst (sourceNativeTimeSplit_symm_clocks D hS τ t)
    have hn := congrArg Prod.snd (sourceNativeTimeSplit_symm_clocks D hS τ t)
    change nativeCoreClock D hS ((sourceNativeTimeSplit D hS).symm (τ, t)) = τ at hc
    change nativeTimeRestriction D hS ((sourceNativeTimeSplit D hS).symm (τ, t)) = t at hn
    rw [hc, hn] at h
    exact h
  change (∫ t, f ((sourceNativeTimeSplit D hS).symm (τ, t)) ∂(Measure.pi fun s => fixMeasure (fixNative D hS fixG s)))
    = _
  rw [he, integral_const_mul, integral_fintype_prod_eq_prod]

end WaveTurbulence.Flower.MkSlots
