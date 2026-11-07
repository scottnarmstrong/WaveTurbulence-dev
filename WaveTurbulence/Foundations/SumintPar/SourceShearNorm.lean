/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.SumintPar.SourceShearFourier
public import WaveTurbulence.Foundations.SumintPar.SourceShearWeight
public import WaveTurbulence.Foundations.Sumint.TimeBridge

/-!
# The source time shear in the exact drafted Fourier norm

The output supremum remains inside the frequency integral. The only
cost at nonnegative regularity is the absolute factor four to that power.
-/

@[expose] public section
set_option autoImplicit false
open MeasureTheory
namespace WaveTurbulence.SumintPar

/-- Common source time shearing has the same absolute cost for an arbitrary output carrier. -/
theorem XNorm00_sourceTimeShear_le {V : Type*} {θ : ℝ} (hθ : 0 ≤ θ)
    (F : (Fin 3 → ℝ) → V → ℂ) :
    XNorm00 θ (fun t v => F (sourceTimeShear t) v) ≤ ENNReal.ofReal (4^θ)*XNorm00 θ F := by
  simp_rw [NormBridgeScratch.XNorm00_eq_mixedFourierNorm00]
  have hi : (∀ v, Integrable (fun t => F (sourceTimeShear t) v)) ↔
      (∀ v, Integrable (fun t => F t v)) :=
    forall_congr' (fun v => integrable_sourceTimeShear_iff (fun t => F t v))
  unfold Fourier.mixedFourierNorm00
  rw [hi]
  split_ifs with hF
  · have he (ξ : Fin 3 → ℝ) :
        Fourier.mixedFourierEnvelope00 (fun t v => F (sourceTimeShear t) v) ξ =
          Fourier.mixedFourierEnvelope00 F (sourceFrequencyShear ξ) := by
      unfold Fourier.mixedFourierEnvelope00
      apply iSup_congr
      intro v
      exact congrArg (fun w : ℂ => ‖w‖ₑ) (timeFourier_sourceTimeShear (fun t => F t v) ξ)
    simp_rw [he]
    calc
      _ ≤ ∫⁻ ξ, ENNReal.ofReal (4^θ) *
          (Fourier.timeWeight θ (sourceFrequencyShear ξ)*
            Fourier.mixedFourierEnvelope00 F (sourceFrequencyShear ξ)) := by
        apply lintegral_mono
        intro ξ
        exact (mul_le_mul' (timeWeight_sourceShear_le hθ ξ) le_rfl).trans_eq (mul_assoc _ _ _)
      _ = ENNReal.ofReal (4^θ)*(∫⁻ ξ, Fourier.timeWeight θ ξ*Fourier.mixedFourierEnvelope00 F ξ) := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        congr 1
        exact measurePreserving_sourceFrequencyShear.lintegral_comp_emb
          sourceFrequencyShearEquiv.measurableEmbedding
          (fun ξ => Fourier.timeWeight θ ξ*Fourier.mixedFourierEnvelope00 F ξ)
  · rw [ENNReal.mul_top (ne_of_gt (ENNReal.ofReal_pos.mpr (Real.rpow_pos_of_pos (by norm_num) _)))]

end WaveTurbulence.SumintPar
