/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.SNormOperations
/-! Real-part projection is contractive for every source spatial norm. -/
public section
namespace WaveTurbulence.Induct
open scoped ENNReal

theorem SNorm_contraction_bound {d A B : ℕ} (T : ℂ →L[ℝ] ℂ)
    (hT : ∀ z, ‖T z‖ ≤ ‖z‖) (f : Mom d → ℂ) (hf : ContDiff ℝ A f)
    (C : ℝ) (hC : 0 ≤ C) (h : SNorm A B f ≤ ENNReal.ofReal C) :
    SNorm A B (T ∘ f) ≤ ENNReal.ofReal C := by
  apply SNorm_le_of_momentum_bounds _ (T.contDiff.comp hf)
  intro n hn ρ x
  have he : Fourier.momentumDerivative ρ (T ∘ f) x = T (Fourier.momentumDerivative ρ f x) := by
    unfold Fourier.momentumDerivative
    rw [T.iteratedFDeriv_comp_left hf.contDiffAt (by exact_mod_cast hn)]
    rfl
  rw [he]
  exact (mul_le_mul_of_nonneg_left (hT _) (pow_nonneg (jbr_pos x).le B)).trans
    (SNorm_momentum_pointwise f hf C hC h hn ρ x)

theorem SNormR_realPart_bound {d A B : ℕ} (f : Mom d → ℂ) (hf : ContDiff ℝ A f)
    (C : ℝ) (hC : 0 ≤ C) (h : SNorm A B f ≤ ENNReal.ofReal C) :
    SNormR A B (fun x => (f x).re) ≤ ENNReal.ofReal C := by
  let T : ℂ →L[ℝ] ℂ := Complex.ofRealCLM.comp Complex.reCLM
  have hT (z : ℂ) : ‖T z‖ ≤ ‖z‖ := by
    change ‖(z.re : ℂ)‖ ≤ ‖z‖
    simpa only [Complex.norm_real, Real.norm_eq_abs] using Complex.abs_re_le_norm z
  exact SNorm_contraction_bound T hT f hf C hC h

end WaveTurbulence.Induct
