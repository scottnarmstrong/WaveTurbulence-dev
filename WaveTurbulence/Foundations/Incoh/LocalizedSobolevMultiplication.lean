/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.WeylSums.SobolevMultiplication

/-!
# Local multiplier bounds for smooth momentum cells

This support-local extension of the landed finite-order product estimate
uses multiplier bounds only on the actual cutoff support. It retains decay
in the cell center, rather than replacing it by a global constant.
-/

public section
noncomputable section
open MeasureTheory Finset

namespace WaveTurbulence.Incoh

/-- The finite-order Sobolev product estimate with support-local multiplier bounds. -/
theorem derivativeL1Sum_mul_le_on_support {ι : Type*} [Fintype ι] {N : ℕ}
    (f g : EuclideanSpace ℝ ι → ℂ) (hf : ContDiff ℝ N f) (hg : ContDiff ℝ N g)
    (hgc : HasCompactSupport g) {D : ℝ} (hD : 0 ≤ D)
    (hb : ∀ j ≤ N, ∀ x ∈ tsupport g, ‖iteratedFDeriv ℝ j f x‖ ≤ D) :
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
      have hlocal : ‖iteratedFDeriv ℝ i f x‖ * ‖iteratedFDeriv ℝ (j-i) g x‖ ≤
          D * ‖iteratedFDeriv ℝ (j-i) g x‖ := by
        by_cases hx : x ∈ tsupport g
        · exact mul_le_mul_of_nonneg_right (hb i hiN x hx) (norm_nonneg _)
        · have hz : iteratedFDeriv ℝ (j-i) g x = 0 := by
            by_contra hn
            exact hx (support_iteratedFDeriv_subset (j-i) hn)
          simp only [hz, norm_zero, mul_zero, le_refl]
      calc
        _ = (j.choose i : ℝ) * (‖iteratedFDeriv ℝ i f x‖ * ‖iteratedFDeriv ℝ (j-i) g x‖) := by ring
        _ ≤ (j.choose i : ℝ) * (D * ‖iteratedFDeriv ℝ (j-i) g x‖) :=
          mul_le_mul_of_nonneg_left hlocal (Nat.cast_nonneg _)
        _ = _ := by ring

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
          (WeylSums.integral_derivative_le_sum ((Nat.sub_le j i).trans hj) g) (Nat.cast_nonneg _))
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

end WaveTurbulence.Incoh
