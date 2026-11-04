/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.RegAsymp.PairedFrequencyWeight
public import WaveTurbulence.Foundations.RegAsymp.UnitSquareCutoff
import WaveTurbulence.Foundations.ClassJR.MCCase1

/-! # The fixed temporal kernel for the full spatial NT mixture -/

@[expose] public section
noncomputable section
namespace WaveTurbulence.RegAsymp
open MeasureTheory ClassJR WaveTurbulence.Fourier
open scoped ENNReal

/-- The original pi-normalized source character with the fixed unit-square extension. -/
def pairedCutoffCharacter (lam : ℝ × ℝ) (t : Fin 2 → ℝ) : ℂ :=
  unitSquareCutoff t * e2 lam (t 0) (t 1)

theorem norm_pairedCutoffCharacter (lam : ℝ × ℝ) (t : Fin 2 → ℝ) :
    ‖pairedCutoffCharacter lam t‖ = ‖unitSquareCutoff t‖ := by
  rw [pairedCutoffCharacter,norm_mul,norm_e2,mul_one]

theorem continuous_pairedCutoffCharacter :
    Continuous (fun p : (Fin 2 → ℝ) × (ℝ × ℝ) => pairedCutoffCharacter p.2 p.1) := by
  unfold pairedCutoffCharacter
  apply Continuous.mul (contDiff_unitSquareCutoff.continuous.comp continuous_fst)
  unfold e2
  fun_prop

theorem integrable_pairedCutoffCharacter (lam : ℝ × ℝ) : Integrable (pairedCutoffCharacter lam) := by
  apply integrable_unitSquareCutoff.mul_bdd (c := 1)
  · exact (show Continuous (fun t : Fin 2 → ℝ => e2 lam (t 0) (t 1)) by unfold e2; fun_prop).aestronglyMeasurable
  · exact ae_of_all _ (fun t => (norm_e2 lam (t 0) (t 1)).le)

/-- One finite physical-time mass works for every temporal frequency. -/
theorem eLpNorm_pairedCutoffCharacter_one (lam : ℝ × ℝ) :
    eLpNorm (pairedCutoffCharacter lam) 1 = ENNReal.ofReal (∫ t, ‖unitSquareCutoff t‖) := by
  rw [eLpNorm_one_eq_lintegral_enorm (integrable_pairedCutoffCharacter lam).aestronglyMeasurable,
    ← ofReal_integral_norm_eq_lintegral_enorm (integrable_pairedCutoffCharacter lam)]
  congr 1
  exact integral_congr_ae (ae_of_all _ (norm_pairedCutoffCharacter lam))

/-- Modulation costs precisely the source lambda weight, up to the fixed 2^eta constant. -/
theorem timeFourierNorm_pairedCutoffCharacter_le {η : ℝ} (hη : 0 ≤ η) (lam : ℝ × ℝ) :
    timeFourierNorm η (pairedCutoffCharacter lam) ≤
      ENNReal.ofReal (2^η)*wL η lam*timeFourierNorm η unitSquareCutoff := by
  have he : pairedCutoffCharacter lam = fun t =>
      Real.fourierChar (timePairing 2 t (pairedTimeFrequency lam)) • unitSquareCutoff t := by
    funext t
    rw [pairedCutoffCharacter,e2_eq_pairedTimeFrequency]
    simp only [Circle.smul_def,smul_eq_mul,mul_comm]
  rw [he]
  exact (timeFourierNorm_modulate_le hη unitSquareCutoff (pairedTimeFrequency lam)).trans
    (mul_le_mul' (mul_le_mul' le_rfl (timeWeight_pairedTimeFrequency_le hη lam)) le_rfl)

end WaveTurbulence.RegAsymp
