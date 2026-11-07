/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.RegRedDraft.NativeTimeCoordinates
public import WaveTurbulence.Foundations.VineEst.RegRedDraft.BranchFactorization

/-! # Full time coordinates split into the skeleton and independent native time blocks -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.RegRed
open TTree Reg Reg.Skeleton MeasureTheory

noncomputable def nativeTimeRestriction {w : ℕ} {S : Garden w} (D : ReconstructionData S)
    (hS : S.IsPlain) (τ : GBranch (D.forest hS) → ℝ) :
    (s : ReplacementSlot S) → NativeTimeBlock D s
  | .inl p => nativeCoupleClock D hS τ p
  | .inr b => nativeChainClock D hS τ b

theorem replacementTimeSplit_sourceTimeSplit {w : ℕ} {S : Garden w} (D : ReconstructionData S)
    (hS : S.IsPlain) (τ : GBranch (D.forest hS) → ℝ) :
    replacementTimeSplit D (sourceTimeSplit D hS τ).2 = nativeTimeRestriction D hS τ := by
  funext s
  cases s with
  | inl p => rfl
  | inr b =>
    funext q
    change (Equiv.piCongrLeft (fun _ => ℝ) (replacementTimeIndexEquiv D)
      (sourceTimeSplit D hS τ).2) ⟨.inr b,q⟩ = _
    rw [Equiv.piCongrLeft_apply_eq_cast,cast_eq]
    rfl

noncomputable def sourceNativeTimeSplit {w : ℕ} {S : Garden w} (D : ReconstructionData S)
    (hS : S.IsPlain) : (GBranch (D.forest hS) → ℝ) ≃ᵐ
      ((GBranch S.tree → ℝ) × ((s : ReplacementSlot S) → NativeTimeBlock D s)) :=
  (sourceTimeSplit D hS).trans
    ((MeasurableEquiv.refl (GBranch S.tree → ℝ)).prodCongr (replacementTimeSplit D))

theorem sourceNativeTimeSplit_apply {w : ℕ} {S : Garden w} (D : ReconstructionData S)
    (hS : S.IsPlain) (τ : GBranch (D.forest hS) → ℝ) :
    sourceNativeTimeSplit D hS τ = (nativeCoreClock D hS τ,nativeTimeRestriction D hS τ) :=
  Prod.ext rfl (replacementTimeSplit_sourceTimeSplit D hS τ)

theorem measurePreserving_sourceNativeTimeSplit {w : ℕ} {S : Garden w} (D : ReconstructionData S)
    (hS : S.IsPlain) : MeasurePreserving (sourceNativeTimeSplit D hS) volume (volume.prod volume) := by
  have hp : MeasurePreserving (Prod.map (id : (GBranch S.tree → ℝ) → _) (replacementTimeSplit D))
      ((volume : Measure (GBranch S.tree → ℝ)).prod (volume : Measure (ReplacementBranchIndex D → ℝ)))
      ((volume : Measure (GBranch S.tree → ℝ)).prod
        (volume : Measure ((s : ReplacementSlot S) → NativeTimeBlock D s))) := by
    refine ⟨measurable_id.prodMap (replacementTimeSplit D).measurable,?_⟩
    rw [← Measure.map_prod_map _ _ measurable_id (replacementTimeSplit D).measurable,
      Measure.map_id,(measurePreserving_replacementTimeSplit D).map_eq]
  exact hp.comp (measurePreserving_sourceTimeSplit D hS)

/-- Conditional integration helper used with the proved integrability of the
actual kernel integrand. No Fubini premise enters the source reduction. -/
theorem integral_sourceNativeTimeSplit {w : ℕ} {S : Garden w} (D : ReconstructionData S)
    (hS : S.IsPlain) (f : (GBranch (D.forest hS) → ℝ) → ℂ) (hf : Integrable f) :
    (∫ τ, f τ) = ∫ τcore, ∫ τnative, f ((sourceNativeTimeSplit D hS).symm (τcore,τnative)) := by
  have hmp := measurePreserving_sourceNativeTimeSplit D hS
  have hi := hmp.symm.integrable_comp_of_integrable hf
  exact (hmp.symm.integral_comp' f).symm.trans (integral_prod _ hi)

end WaveTurbulence.RegRed
