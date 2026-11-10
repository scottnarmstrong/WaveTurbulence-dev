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

end WaveTurbulence.Flower.MkSlots
