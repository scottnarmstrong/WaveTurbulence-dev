/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.RegAsymp.PairedProfile

/-! # A cutoff of the actual source inverse profile is integrable -/

@[expose] public section
noncomputable section
namespace WaveTurbulence.RegAsymp
open MeasureTheory WaveTurbulence.Fourier ClassJR

/-- The literal source inverse profile on its original two frequency variables. -/
def pairedInverseProfile (A : (ℝ × ℝ) → ℂ) (t : Fin 2 → ℝ) : ℂ :=
  ∫ lam, A lam*e2 lam (t 0) (t 1)

theorem pairedInverseProfile_eq_fourierIntegral (A : (ℝ × ℝ) → ℂ) (t : Fin 2 → ℝ) :
    pairedInverseProfile A t =
      VectorFourier.fourierIntegral Real.fourierChar volume pairedProfilePairing.flip A t := by
  unfold pairedInverseProfile VectorFourier.fourierIntegral
  apply integral_congr_ae
  exact ae_of_all _ (fun lam => by
    simp only [LinearMap.flip_apply,pairedProfilePairing_apply,neg_neg,e2_eq_pairedTimeFrequency,
      Circle.smul_def,smul_eq_mul,mul_comm])

/-- Only integrability of the density is required for continuity of the uncut profile. -/
theorem continuous_pairedInverseProfile {A : (ℝ × ℝ) → ℂ} (hA : Integrable A) :
    Continuous (pairedInverseProfile A) := by
  have hL : Continuous (fun p : (ℝ × ℝ) × (Fin 2 → ℝ) => pairedProfilePairing.flip p.1 p.2) := by
    simp only [LinearMap.flip_apply,pairedProfilePairing_apply,timePairing_pairedTimeFrequency]
    fun_prop
  have he : pairedInverseProfile A =
      VectorFourier.fourierIntegral Real.fourierChar volume pairedProfilePairing.flip A :=
    funext (pairedInverseProfile_eq_fourierIntegral A)
  rw [he]
  exact VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar hL hA

/-- The uncut profile is uniformly bounded by the actual frequency mass. -/
theorem norm_pairedInverseProfile_le (A : (ℝ × ℝ) → ℂ) (t : Fin 2 → ℝ) :
    ‖pairedInverseProfile A t‖ ≤ ∫ lam, ‖A lam‖ := by
  apply (norm_integral_le_integral_norm _).trans_eq
  apply integral_congr_ae
  exact ae_of_all _ (fun lam => by
    dsimp only
    rw [norm_mul,e2_eq_pairedTimeFrequency,Circle.norm_coe,mul_one])

/-- Multiplying by an L1 cutoff yields an L1 time profile. No assertion
that the uncut inverse transform is time-integrable is needed. -/
theorem integrable_mul_pairedInverseProfile {f : (Fin 2 → ℝ) → ℂ} {A : (ℝ × ℝ) → ℂ}
    (hf : Integrable f) (hA : Integrable A) : Integrable (fun t => f t*pairedInverseProfile A t) :=
  hf.mul_bdd (continuous_pairedInverseProfile hA).aestronglyMeasurable
    (ae_of_all _ (norm_pairedInverseProfile_le A))

end WaveTurbulence.RegAsymp
