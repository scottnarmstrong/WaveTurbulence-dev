/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Fourier.FourierL1Sobolev
public import Mathlib.Analysis.Calculus.ContDiff.Bounds
public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic

/-!
# Quantitative cutoff multiplication at finite derivative order

DH23 (NTphibounds) controls a finite number of derivatives of the amplitude.
Multiplication by a compact cutoff converts this bound to the Sobolev `L¹`
quantity needed for Fourier inversion, linearly in the amplitude bound.
-/

public section
open MeasureTheory Finset
namespace WaveTurbulence.WeylSums

/-- Each derivative integral is one nonnegative term of the Sobolev sum. -/
theorem integral_derivative_le_sum {ι : Type*} [Fintype ι] {N j : ℕ} (hj : j ≤ N)
    (g : EuclideanSpace ℝ ι → ℂ) :
    (∫ x, ‖iteratedFDeriv ℝ j g x‖) ≤ Fourier.derivativeL1Sum N g := by
  unfold Fourier.derivativeL1Sum
  apply single_le_sum _ (mem_range.mpr (show j < N+1 by omega))
  intro k hk
  exact integral_nonneg (fun x => norm_nonneg _)

/-- A bounded `C^N` multiplier times a compact `C^N` cutoff has controlled
Sobolev `L¹` norm. The constant is explicit and independent of translations. -/
theorem derivativeL1Sum_mul_le {ι : Type*} [Fintype ι] {N : ℕ}
    (f g : EuclideanSpace ℝ ι → ℂ) (hf : ContDiff ℝ N f) (hg : ContDiff ℝ N g)
    (hgc : HasCompactSupport g) {D : ℝ} (hD : 0 ≤ D)
    (hb : ∀ j ≤ N, ∀ x, ‖iteratedFDeriv ℝ j f x‖ ≤ D) :
    Fourier.derivativeL1Sum N (fun x => f x*g x) ≤
      ((N : ℝ)+1)*(2 : ℝ)^N * D * Fourier.derivativeL1Sum N g := by
  have hig (j : ℕ) (hj : j ≤ N) : Integrable (iteratedFDeriv ℝ j g) :=
    (hg.continuous_iteratedFDeriv (by exact_mod_cast hj)).integrable_of_hasCompactSupport (hgc.iteratedFDeriv j)
  have hifg (j : ℕ) (hj : j ≤ N) : Integrable (iteratedFDeriv ℝ j (fun x => f x*g x)) :=
    ((hf.mul hg).continuous_iteratedFDeriv (by exact_mod_cast hj)).integrable_of_hasCompactSupport
      (hgc.mul_left.iteratedFDeriv j)
  have hterm (j : ℕ) (hj : j ≤ N) :
      (∫ x, ‖iteratedFDeriv ℝ j (fun x => f x*g x) x‖) ≤
        (2 : ℝ)^N * D * Fourier.derivativeL1Sum N g := by
    have hpoint (x : EuclideanSpace ℝ ι) :
        ‖iteratedFDeriv ℝ j (fun x => f x*g x) x‖ ≤
          D * ∑ i ∈ range (j+1), (j.choose i : ℝ) * ‖iteratedFDeriv ℝ (j-i) g x‖ := by
      apply (norm_iteratedFDeriv_mul_le hf hg x (by exact_mod_cast hj)).trans
      rw [mul_sum]
      apply sum_le_sum
      intro i hi
      have hiN : i ≤ N := (Nat.le_of_lt_succ (mem_range.mp hi)).trans hj
      have hh := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (hb i hiN x) (Nat.cast_nonneg (j.choose i)))
        (norm_nonneg (iteratedFDeriv ℝ (j-i) g x))
      convert hh using 1
      ring
    have hi_rhs : Integrable (fun x => D * ∑ i ∈ range (j+1),
        (j.choose i : ℝ) * ‖iteratedFDeriv ℝ (j-i) g x‖) := by
      apply Integrable.const_mul
      apply integrable_finsetSum
      intro i hi
      exact ((hig (j-i) ((Nat.sub_le j i).trans hj)).norm).const_mul _
    calc
      _ ≤ ∫ x, D * ∑ i ∈ range (j+1), (j.choose i : ℝ) * ‖iteratedFDeriv ℝ (j-i) g x‖ :=
        integral_mono (hifg j hj).norm hi_rhs hpoint
      _ = D * ∑ i ∈ range (j+1), (j.choose i : ℝ) * ∫ x, ‖iteratedFDeriv ℝ (j-i) g x‖ := by
        rw [integral_const_mul, integral_finsetSum (range (j+1))
          (fun i hi => ((hig (j-i) ((Nat.sub_le j i).trans hj)).norm).const_mul _)]
        simp_rw [integral_const_mul]
      _ ≤ D * ∑ i ∈ range (j+1), (j.choose i : ℝ) * Fourier.derivativeL1Sum N g := by
        apply mul_le_mul_of_nonneg_left _ hD
        exact sum_le_sum (fun i hi => mul_le_mul_of_nonneg_left
          (integral_derivative_le_sum ((Nat.sub_le j i).trans hj) g) (Nat.cast_nonneg _))
      _ = (2 : ℝ)^j * D * Fourier.derivativeL1Sum N g := by
        rw [← sum_mul]
        have hchoose : (∑ i ∈ range (j+1), (j.choose i : ℝ)) = (2 : ℝ)^j := by
          exact_mod_cast Nat.sum_range_choose j
        rw [hchoose]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hj) hD)
        (Fourier.derivativeL1Sum_nonneg _ _)
  change (∑ j ∈ range (N+1), ∫ x, ‖iteratedFDeriv ℝ j (fun x => f x*g x) x‖) ≤ _
  calc
    _ ≤ ∑ j ∈ range (N+1), (2 : ℝ)^N * D * Fourier.derivativeL1Sum N g :=
      sum_le_sum (fun j hj => hterm j (Nat.le_of_lt_succ (mem_range.mp hj)))
    _ = _ := by rw [sum_const, card_range, nsmul_eq_mul]; push_cast; ring

end WaveTurbulence.WeylSums
