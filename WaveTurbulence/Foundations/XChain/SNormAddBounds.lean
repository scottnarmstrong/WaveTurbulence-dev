/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.SNormRealPart
public import WaveTurbulence.Foundations.XChain.SNormGeometricTail
/-! Additive spatial-norm bounds for the actual smooth remainder candidates. -/
public section
namespace WaveTurbulence.Induct
open scoped ENNReal

theorem SNorm_add_bound {d A B : ℕ} (f g : Mom d → ℂ)
    (hf : ContDiff ℝ A f) (hg : ContDiff ℝ A g) (C D : ℝ) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (h : SNorm A B f ≤ ENNReal.ofReal C) (h' : SNorm A B g ≤ ENNReal.ofReal D) :
    SNorm A B (f + g) ≤ ENNReal.ofReal (C + D) := by
  apply SNorm_le_of_momentum_bounds _ (hf.add hg)
  intro n hn ρ x
  have he : Fourier.momentumDerivative ρ (f + g) x =
      Fourier.momentumDerivative ρ f x + Fourier.momentumDerivative ρ g x := by
    unfold Fourier.momentumDerivative
    rw [iteratedFDeriv_add_apply (hf.contDiffAt.of_le (by exact_mod_cast hn))
      (hg.contDiffAt.of_le (by exact_mod_cast hn))]
    rfl
  change jbr x ^ B * ‖Fourier.momentumDerivative ρ (f + g) x‖ ≤ C + D
  rw [he]
  have h1 := SNorm_momentum_pointwise f hf C hC h hn ρ x
  have h2 := SNorm_momentum_pointwise g hg D hD h' hn ρ x
  have ht := mul_le_mul_of_nonneg_left (norm_add_le
    (Fourier.momentumDerivative ρ f x) (Fourier.momentumDerivative ρ g x))
      (pow_nonneg (jbr_pos x).le B)
  nlinarith

theorem SNorm_neg_bound {d A B : ℕ} (f : Mom d → ℂ) (hf : ContDiff ℝ A f)
    (C : ℝ) (hC : 0 ≤ C) (h : SNorm A B f ≤ ENNReal.ofReal C) :
    SNorm A B (-f) ≤ ENNReal.ofReal C := by
  exact SNorm_contraction_bound (-ContinuousLinearMap.id ℝ ℂ)
    (fun z => by simp) f hf C hC h

end WaveTurbulence.Induct
