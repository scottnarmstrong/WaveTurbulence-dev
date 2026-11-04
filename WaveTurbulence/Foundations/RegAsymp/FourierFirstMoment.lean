/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Fourier.FourierL1Sobolev

/-! # One Fourier moment from one extra spatial derivative

DH23 (propertyw1) in the regular-couple localization. The constant depends
only on the fixed spatial dimension and derivative order, never on the
number of leaves or on a cell center.
-/

public section
namespace WaveTurbulence.RegAsymp
open MeasureTheory Module
open scoped FourierTransform
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

/-- The absolute constant for a first frequency moment with N derivatives. -/
@[expose] noncomputable def firstMomentFourierConstant (V : Type*)
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    [MeasurableSpace V] [BorelSpace V] (N : ℕ) : ℝ :=
  (2 : ℝ) ^ (N-1) * (1+2^N) * ∫ ξ : V, (1+‖ξ‖) ^ (-((N-1 : ℕ) : ℝ))

/-- W^(N,1), with N>dim+1, controls the actual first Fourier moment. -/
theorem fourier_firstMoment_integrable_and_bound {N : ℕ} {f : V → ℂ}
    (hN : finrank ℝ V + 1 < N) (hf : ContDiff ℝ N f)
    (hi : ∀ j ≤ N, Integrable (iteratedFDeriv ℝ j f)) :
    Integrable (fun ξ => (1+‖ξ‖) * ‖𝓕 f ξ‖) ∧
      (∫ ξ, (1+‖ξ‖) * ‖𝓕 f ξ‖) ≤
        firstMomentFourierConstant V N * Fourier.derivativeL1Sum N f := by
  have hNp : 0 < N := by omega
  have henv : Integrable (fun ξ : V => (1+‖ξ‖) ^ (-((N-1 : ℕ) : ℝ))) :=
    integrable_one_add_norm (by
      have h : finrank ℝ V < N-1 := by omega
      exact_mod_cast h)
  let B : ℝ := (2 : ℝ) ^ (N-1) * (1+2^N) * Fourier.derivativeL1Sum N f
  have hbound (ξ : V) : (1+‖ξ‖) * ‖𝓕 f ξ‖ ≤ B * (1+‖ξ‖) ^ (-((N-1 : ℕ) : ℝ)) := by
    have h := Fourier.fourier_polynomial_weight_le hf hi ξ
    have hp : 0 < (1+‖ξ‖) ^ (N-1) := pow_pos (by positivity) _
    have hh : (1+‖ξ‖) * ‖𝓕 f ξ‖ ≤ B / (1+‖ξ‖) ^ (N-1) := by
      apply (le_div_iff₀ hp).mpr
      have hn : N = (N-1)+1 := by omega
      have hpow : (1+‖ξ‖)^N = (1+‖ξ‖)^(N-1)*(1+‖ξ‖) := by
        conv_lhs => rw [hn,pow_succ]
      rw [hpow] at h
      simpa only [B,mul_assoc,mul_left_comm,mul_comm] using h
    rw [Real.rpow_neg (by positivity),Real.rpow_natCast]
    simpa only [div_eq_mul_inv] using hh
  have hfi : Integrable f := by
    have h : Integrable (fun x => ‖f x‖) := by
      simpa only [norm_iteratedFDeriv_zero] using (hi 0 (Nat.zero_le _)).norm
    exact (integrable_norm_iff hf.continuous.aestronglyMeasurable).mp h
  have hFc : Continuous (𝓕 f) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar (innerSL ℝ).continuous₂ hfi
  have hF : Integrable (fun ξ => (1+‖ξ‖) * ‖𝓕 f ξ‖) :=
    (henv.const_mul B).mono' ((continuous_const.add continuous_norm).mul hFc.norm).aestronglyMeasurable
      (ae_of_all _ fun ξ => by
        rw [Real.norm_eq_abs,abs_of_nonneg (by positivity)]
        exact hbound ξ)
  refine ⟨hF,?_⟩
  calc
    _ ≤ ∫ ξ : V, B * (1+‖ξ‖) ^ (-((N-1 : ℕ) : ℝ)) :=
      integral_mono hF (henv.const_mul B) hbound
    _ = _ := by rw [integral_const_mul]; unfold B firstMomentFourierConstant; ring

end WaveTurbulence.RegAsymp
