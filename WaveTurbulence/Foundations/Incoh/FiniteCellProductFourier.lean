/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Incoh.CellFourierInversion

/-!
# Joint Fourier representation of finite families of actual cells

The positive Fourier density is integrable on the literal product spectral
measure. This transport helper keeps all momentum parameters outside the
spectral measure and does not exchange a supremum with an integral.
-/

public section
noncomputable section
open MeasureTheory
open scoped ENNReal

namespace WaveTurbulence.Incoh

/-- Actual positive Fourier integrand for a finite family of momentum profiles. -/
@[expose] def cellProductFourierIntegrand {d : ℕ} {I : Type*} [Fintype I]
    (f : I → (Fin d → ℝ) → ℂ) (x ξ : I → Fin d → ℝ) : ℂ :=
  ∏ i, Real.fourierChar (Fourier.timePairing d (ξ i) (x i)) • Fourier.timeFourier (f i) (ξ i)

/-- Conditional finite-product inversion helper; actual cell bounds discharge its premises. -/
theorem prod_eq_cellProductFourierIntegral {d : ℕ} {I : Type*} [Fintype I]
    (f : I → (Fin d → ℝ) → ℂ) (hc : ∀ i, Continuous (f i))
    (hf : ∀ i, Fourier.timeFourierNorm 0 (f i) < ⊤) (x : I → Fin d → ℝ) :
    (∏ i, f i (x i)) = ∫ ξ : I → Fin d → ℝ, cellProductFourierIntegrand f x ξ := by
  unfold cellProductFourierIntegrand
  rw [integral_fintype_prod_volume_eq_prod
    (fun i ξ => Real.fourierChar (Fourier.timePairing d ξ (x i)) • Fourier.timeFourier (f i) ξ)]
  apply Finset.prod_congr rfl
  intro i _
  exact eq_positiveFourierIntegral_of_norm_lt_top (hc i) (hf i) (x i)

/-- The joint positive Fourier integrand is integrable, without a representation premise. -/
theorem integrable_cellProductFourierIntegrand {d : ℕ} {I : Type*} [Fintype I]
    (f : I → (Fin d → ℝ) → ℂ)
    (hf : ∀ i, Fourier.timeFourierNorm 0 (f i) < ⊤) (x : I → Fin d → ℝ) :
    Integrable (cellProductFourierIntegrand f x) := by
  change Integrable (fun ξ : I → Fin d → ℝ => ∏ i,
    Real.fourierChar (Fourier.timePairing d (ξ i) (x i)) • Fourier.timeFourier (f i) (ξ i))
    (Measure.pi (fun _ : I => (volume : Measure (Fin d → ℝ))))
  apply Integrable.fintype_prod (f := fun i ξ =>
    Real.fourierChar (Fourier.timePairing d ξ (x i)) • Fourier.timeFourier (f i) ξ)
  intro i
  have hi := Fourier.integrable_of_timeFourierNorm_lt_top (hf i)
  have hF := Fourier.integrable_timeFourier_of_norm_lt_top (le_refl (0 : ℝ)) (hf i)
  apply hF.norm.mono'
  · exact ((by
      change Continuous (fun ξ : Fin d → ℝ =>
        (Real.fourierChar (∑ j, ξ j * x i j) : ℂ))
      fun_prop : Continuous (fun ξ : Fin d → ℝ =>
      (Real.fourierChar (Fourier.timePairing d ξ (x i)) : ℂ))).mul
        (Fourier.timeFourier_continuous hi)).aestronglyMeasurable
  · exact ae_of_all _ (fun ξ => by simp only [Circle.norm_smul]; exact le_refl _)

end WaveTurbulence.Incoh
