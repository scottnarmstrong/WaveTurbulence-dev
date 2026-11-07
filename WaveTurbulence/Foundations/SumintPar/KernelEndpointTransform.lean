/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.SumintPar.SourceExitTransform
public import WaveTurbulence.Foundations.SumintPar.KernelExtension

/-!
# Exact sparse endpoint transform of the actual rectangular extension

Fourier Fubini and the measurable exit partitions express the transform
as a finite difference of sparse transforms divided by the three
nonvanishing endpoint rates. All native input integrability needed for
splitting the sums and the difference is proved explicitly.
-/

@[expose] public section
set_option autoImplicit false

open MeasureTheory Set

namespace WaveTurbulence.SumintPar

/-- Exact sparse endpoint-transform formula for the actual rectangular kernel extension. -/
theorem timeFourier_kernelExtension_eq_exit_transforms {d : ℕ} (D : SumintDatum d)
    (hI : 0 < D.S.I) (c h : ℝ) (F : (D.S.TVar → ℝ) → ℂ)
    (hFm : Measurable F) (hFi : IntegrableOn F (localInputTimeDomain D c h)) (ξ : Fin 3 → ℝ) :
    Fourier.timeFourier (kernelExtension D hI c h F) ξ =
      ((∑ v, sourceExitOuterPhase D true v (ξ 0)*sourceExitTransform D hI true v F c h (ξ 0) (ξ 1+ξ 2))-
        (∑ v, sourceExitOuterPhase D false v (ξ 0)*sourceExitTransform D hI false v F c h (ξ 0) (ξ 1+ξ 2)))/
      boxEndpointDenominator ξ := by
  let T (upper : Bool) (v : D.S.TVar) (u : D.S.TVar → ℝ) :=
    sourceExitOuterPhase D upper v (ξ 0)*
      (sourceExitAmplitude D hI upper v F u*sourceExitPhase D hI v (ξ 0) (ξ 1+ξ 2) u)
  have hi (upper : Bool) (v : D.S.TVar) : IntegrableOn (T upper v) (localInputTimeDomain D c h) :=
    (integrableOn_sourceExitTransform_integrand D hI upper v F hFm c h hFi _ _).const_mul _
  have hs (upper : Bool) : IntegrableOn (fun u => ∑ v, T upper v u) (localInputTimeDomain D c h) :=
    integrable_finsetSum _ (fun v _ => hi upper v)
  rw [timeFourier_kernelExtension D hI c h F hFm hFi]
  have he (u : D.S.TVar → ℝ) : F u*
      Fourier.timeFourier (exponentialBox (lowerTimeExit D hI u) (upperTimeExit D hI u) (u (firstTime D hI))) ξ =
      (F u*boxEndpointNumerator (lowerTimeExit D hI u) (upperTimeExit D hI u) (u (firstTime D hI)) ξ)/
        boxEndpointDenominator ξ := by
    rw [timeFourier_exponentialBox_eq_endpoint_quotient]
    ring
  simp_rw [he]
  rw [integral_div]
  congr 1
  simp_rw [source_input_mul_endpoint_numerator_eq]
  change (∫ u in localInputTimeDomain D c h, (∑ v, T true v u)-(∑ v, T false v u)) = _
  rw [integral_sub (hs true) (hs false),integral_finsetSum _ (fun v _ => hi true v),
    integral_finsetSum _ (fun v _ => hi false v)]
  apply congrArg₂ (fun a b : ℂ => a-b)
  all_goals
    apply Finset.sum_congr rfl
    intro v _
    dsimp only [T]
    rw [integral_const_mul]
    rfl

/-- The endpoint denominator dominates the exact product of the three Japanese brackets. -/
theorem prod_scalarBracket_le_norm_boxEndpointDenominator (ξ : Fin 3 → ℝ) :
    (∏ j, scalarBracket (ξ j)) ≤ ‖boxEndpointDenominator ξ‖ := by
  rw [Fin.prod_univ_three,boxEndpointDenominator,norm_mul,norm_mul]
  have h0 := scalarBracket_le_norm_exponentialRate (σ := -1) (by norm_num) (ξ 0)
  have h1 := scalarBracket_le_norm_exponentialRate (σ := 1) (by norm_num) (ξ 1)
  have h2 := scalarBracket_le_norm_exponentialRate (σ := 1) (by norm_num) (ξ 2)
  exact mul_le_mul (mul_le_mul h0 h1 (zero_lt_one.trans_le (one_le_scalarBracket _)).le (norm_nonneg _)) h2
    (zero_lt_one.trans_le (one_le_scalarBracket _)).le (by positivity)

/-- The actual transform is controlled by sparse endpoint amplitudes and the three bracket denominators. -/
theorem norm_timeFourier_kernelExtension_le_exit_transforms {d : ℕ} (D : SumintDatum d)
    (hI : 0 < D.S.I) (c h : ℝ) (F : (D.S.TVar → ℝ) → ℂ)
    (hFm : Measurable F) (hFi : IntegrableOn F (localInputTimeDomain D c h)) (ξ : Fin 3 → ℝ) :
    ‖Fourier.timeFourier (kernelExtension D hI c h F) ξ‖ ≤
      ((∑ v, ‖sourceExitTransform D hI true v F c h (ξ 0) (ξ 1+ξ 2)‖)+
        (∑ v, ‖sourceExitTransform D hI false v F c h (ξ 0) (ξ 1+ξ 2)‖))*(∏ j, 1/scalarBracket (ξ j)) := by
  rw [timeFourier_kernelExtension_eq_exit_transforms D hI c h F hFm hFi,norm_div]
  have hs (upper : Bool) :
      ‖∑ v, sourceExitOuterPhase D upper v (ξ 0)*sourceExitTransform D hI upper v F c h (ξ 0) (ξ 1+ξ 2)‖ ≤
      ∑ v, ‖sourceExitTransform D hI upper v F c h (ξ 0) (ξ 1+ξ 2)‖ := by
    apply (norm_sum_le _ _).trans_eq
    apply Finset.sum_congr rfl
    intro v _
    rw [norm_mul,norm_sourceExitOuterPhase,one_mul]
  have hnum := (norm_sub_le _ _).trans (add_le_add (hs true) (hs false))
  have hp : 0 < ∏ j, scalarBracket (ξ j) := Finset.prod_pos (fun j _ => zero_lt_one.trans_le (one_le_scalarBracket _))
  have hsum : 0 ≤ (∑ v, ‖sourceExitTransform D hI true v F c h (ξ 0) (ξ 1+ξ 2)‖)+
      (∑ v, ‖sourceExitTransform D hI false v F c h (ξ 0) (ξ 1+ξ 2)‖) := by positivity
  calc
    _ ≤ _/‖boxEndpointDenominator ξ‖ := div_le_div_of_nonneg_right hnum (norm_nonneg _)
    _ ≤ _/(∏ j, scalarBracket (ξ j)) := div_le_div_of_nonneg_left hsum hp
      (prod_scalarBracket_le_norm_boxEndpointDenominator ξ)
    _ = _ := by simp only [div_eq_mul_inv,one_mul,Finset.prod_inv_distrib]

end WaveTurbulence.SumintPar
