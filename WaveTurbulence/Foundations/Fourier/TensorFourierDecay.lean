/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Fourier.CutoffFourierDecay
public import WaveTurbulence.Foundations.Fourier.TimeFourier
public import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Tactic

/-!
# Fourier decay of the tensor cutoff

The scalar estimate tensorizes, with explicit stretched exponential decay
in the sum of square roots of the coordinate frequencies.
-/

public section

open MeasureTheory
open scoped FourierTransform

namespace WaveTurbulence.Fourier

private theorem char_sum_coe {ι : Type*} (s : Finset ι) (a : ι → ℝ) :
    (Real.fourierChar (∑ i ∈ s, a i) : ℂ) = ∏ i ∈ s, (Real.fourierChar (a i) : ℂ) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => simp only [Finset.sum_insert hi, Finset.prod_insert hi,
      AddChar.map_add_eq_mul, Circle.coe_mul, ih]

/-- The Fourier transform of the tensor cutoff factorizes coordinatewise. -/
theorem timeFourier_chi0Tensor_eq_prod {r : ℕ} (ξ : Fin r → ℝ) :
    timeFourier (fun t : Fin r → ℝ => (chi0Tensor t : ℂ)) ξ =
      ∏ i, 𝓕 chi0Complex (ξ i) := by
  unfold timeFourier VectorFourier.fourierIntegral
  change (∫ t : Fin r → ℝ, Real.fourierChar (-(∑ i, t i * ξ i)) •
    (chi0Tensor t : ℂ)) = _
  simp_rw [chi0Tensor, Complex.ofReal_prod, Circle.smul_def,
    ← Finset.sum_neg_distrib, char_sum_coe, smul_eq_mul, ← Finset.prod_mul_distrib]
  have he := integral_fin_nat_prod_volume_eq_prod
    (fun i (t : ℝ) => (Real.fourierChar (-(t * ξ i)) : ℂ) * (chi0 t : ℂ))
  rw [he]
  apply Finset.prod_congr rfl
  intro i _
  rw [Real.fourier_real_eq]
  rfl

/-- Explicit tensor Fourier decay. This anisotropic bound implies the usual
stretched exponential bound in any fixed finite-dimensional norm. -/
theorem chi0Tensor_fourier_exp_decay {r : ℕ} (ξ : Fin r → ℝ) :
    ‖timeFourier (fun t : Fin r → ℝ => (chi0Tensor t : ℂ)) ξ‖ ≤
      (8 * Real.exp 4) ^ r * Real.exp
        (-(Real.log 4 / (4 * Real.sqrt (16 + 16 * Real.exp 2))) *
          ∑ i, Real.sqrt |ξ i|) := by
  rw [timeFourier_chi0Tensor_eq_prod, norm_prod]
  calc
    ∏ i, ‖𝓕 chi0Complex (ξ i)‖ ≤ ∏ i,
        (8 * Real.exp 4 * Real.exp
          (-(Real.log 4 / (4 * Real.sqrt (16 + 16 * Real.exp 2))) * Real.sqrt |ξ i|)) :=
      Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) (fun i _ => chi0_fourier_exp_decay (ξ i))
    _ = _ := by
      rw [Finset.prod_mul_distrib, ← Real.exp_sum, ← Finset.mul_sum]
      simp

/-- The usual stretched exponential Fourier decay in the coordinate-space
norm, with dimension dependence confined to the prefactor. -/
theorem chi0Tensor_fourier_norm_exp_decay {r : ℕ} (ξ : Fin r → ℝ) :
    ‖timeFourier (fun t : Fin r → ℝ => (chi0Tensor t : ℂ)) ξ‖ ≤
      (8 * Real.exp 4) ^ r * Real.exp
        (-(Real.log 4 / (4 * Real.sqrt (16 + 16 * Real.exp 2))) * Real.sqrt ‖ξ‖) := by
  let S := ∑ i, Real.sqrt |ξ i|
  have hS : 0 ≤ S := Finset.sum_nonneg (fun _ _ => Real.sqrt_nonneg _)
  have hn : ‖ξ‖ ≤ S ^ 2 := by
    apply (pi_norm_le_iff_of_nonneg (sq_nonneg S)).mpr
    intro i
    have hi : Real.sqrt |ξ i| ≤ S :=
      Finset.single_le_sum (f := fun j => Real.sqrt |ξ j|)
        (fun _ _ => Real.sqrt_nonneg _) (Finset.mem_univ i)
    have hs := Real.sq_sqrt (abs_nonneg (ξ i))
    have hsi := Real.sqrt_nonneg |ξ i|
    rw [Real.norm_eq_abs]
    nlinarith
  have hr : Real.sqrt ‖ξ‖ ≤ S := Real.sqrt_le_iff.mpr ⟨hS, hn⟩
  have hc : 0 ≤ Real.log 4 / (4 * Real.sqrt (16 + 16 * Real.exp 2)) := by
    exact div_nonneg (Real.log_nonneg (by norm_num)) (by positivity)
  apply (chi0Tensor_fourier_exp_decay ξ).trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Real.exp_le_exp.mpr
  exact mul_le_mul_of_nonpos_left hr (neg_nonpos.mpr hc)

end WaveTurbulence.Fourier
