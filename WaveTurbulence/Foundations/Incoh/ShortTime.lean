/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Incoh.PoissonLink

/-!
# The one-link short-time pointwise bound

TARGET (incohproof14): Poisson summation followed by the landed Lemma 5.2.
The constant depends only on the dimension; the Wick correction is explicit.
-/

public section
noncomputable section

namespace WaveTurbulence.Incoh

/-- Lemma 5.2 gives a single uniform constant for the unmasked localized lattice sum. -/
theorem exists_shortTime_bilinear_bound (d : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ L : ℝ, 1 ≤ L → ∀ s : ℝ, |s| ≤ L →
      ∀ A : LinkParameters d,
        ‖WeylSums.bilinearLatticeSum L s A.leftCenter A.rightCenter A.leftShift A.rightShift‖ ≤
          C * L ^ (2 * d) / Real.sqrt (1 + s ^ 2) ^ d := by
  obtain ⟨C, hC⟩ := NTSP.lemlayer1 d
  refine ⟨max C 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), ?_⟩
  intro L hL s hs A
  have hLp := zero_lt_one.trans_le hL
  obtain ⟨hsum, hbound⟩ := hC L hL s hs A.leftCenter A.rightCenter A.leftShift A.rightShift
  rw [bilinearLatticeSum_eq_poisson hLp, norm_mul, Complex.norm_pow,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos hLp]
  calc
    _ ≤ L ^ (2 * d) * ∑' gh : (Fin d → ℤ) × (Fin d → ℤ),
        ‖Fourier.bilinearPhaseIntegral (Fourier.chi0MomSchwartz d) (Fourier.chi0MomSchwartz d)
          A.leftCenter A.rightCenter (L • NTSP.intVec gh.1 + A.leftShift)
            (L • NTSP.intVec gh.2 + A.rightShift) s‖ :=
      mul_le_mul_of_nonneg_left (norm_tsum_le_tsum_norm hsum) (by positivity)
    _ ≤ L ^ (2 * d) * (C / Real.sqrt (1 + s ^ 2) ^ d) :=
      mul_le_mul_of_nonneg_left hbound (by positivity)
    _ ≤ _ := by
      calc
        _ = C * (L ^ (2 * d) / Real.sqrt (1 + s ^ 2) ^ d) := by ring
        _ ≤ max C 1 * (L ^ (2 * d) / Real.sqrt (1 + s ^ 2) ^ d) :=
          mul_le_mul_of_nonneg_right (le_max_left C 1) (by positivity)
        _ = _ := by ring

/-- TARGET's masked short-time estimate, valid uniformly in all four vector parameters. -/
theorem exists_shortTime_link_bound (d : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ L : ℝ, 1 ≤ L → ∀ s : ℝ, |s| ≤ L →
      ∀ A : LinkParameters d,
        ‖linkLatticeSum L s A‖ ≤ C * L ^ (2 * d) / Real.sqrt (1 + s ^ 2) ^ d := by
  obtain ⟨C, hC, hb⟩ := exists_shortTime_bilinear_bound d
  refine ⟨C + 2 * 10 ^ d, by positivity, ?_⟩
  intro L hL s hs A
  have hLp := zero_lt_one.trans_le hL
  have hden : 0 < Real.sqrt (1 + s ^ 2) ^ d := by positivity
  have hsqrt : Real.sqrt (1 + s ^ 2) ≤ 2 * L := by
    rw [Real.sqrt_le_left (by positivity)]
    have hs2 := (sq_le_sq₀ (abs_nonneg s) hLp.le).mpr hs
    rw [sq_abs] at hs2
    nlinarith [sq_nonneg (L - 1)]
  have herr : (2 * (5 * L) ^ d) * Real.sqrt (1 + s ^ 2) ^ d ≤
      (2 * 10 ^ d) * L ^ (2 * d) := by
    calc
      _ ≤ (2 * (5 * L) ^ d) * (2 * L) ^ d :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Real.sqrt_nonneg _) hsqrt d) (by positivity)
      _ = _ := by
        rw [show (10 : ℝ) ^ d = 5 ^ d * 2 ^ d by rw [← mul_pow]; norm_num]
        rw [mul_pow, mul_pow, pow_mul]
        ring
  have hsplit : ‖linkLatticeSum L s A‖ ≤
      ‖WeylSums.bilinearLatticeSum L s A.leftCenter A.rightCenter A.leftShift A.rightShift‖ +
        2 * (5 * L) ^ d := by
    calc
      _ ≤ ‖WeylSums.bilinearLatticeSum L s A.leftCenter A.rightCenter A.leftShift A.rightShift‖ +
          ‖linkLatticeSum L s A -
            WeylSums.bilinearLatticeSum L s A.leftCenter A.rightCenter A.leftShift A.rightShift‖ :=
        by
          simpa only [add_sub_cancel] using norm_add_le
            (WeylSums.bilinearLatticeSum L s A.leftCenter A.rightCenter A.leftShift A.rightShift)
            (linkLatticeSum L s A -
              WeylSums.bilinearLatticeSum L s A.leftCenter A.rightCenter A.leftShift A.rightShift)
      _ ≤ _ := add_le_add le_rfl (norm_linkLatticeSum_sub_bilinear_le hL s A)
  apply (le_div_iff₀ hden).mpr
  calc
    _ ≤ (‖WeylSums.bilinearLatticeSum L s A.leftCenter A.rightCenter A.leftShift A.rightShift‖ +
        2 * (5 * L) ^ d) * Real.sqrt (1 + s ^ 2) ^ d :=
      mul_le_mul_of_nonneg_right hsplit hden.le
    _ ≤ C * L ^ (2 * d) + (2 * 10 ^ d) * L ^ (2 * d) := by
      rw [add_mul]
      exact add_le_add ((le_div_iff₀ hden).mp (hb L hL s hs A)) herr
    _ = _ := by ring

end WaveTurbulence.Incoh
