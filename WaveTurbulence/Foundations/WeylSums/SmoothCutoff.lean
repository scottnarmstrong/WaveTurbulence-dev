/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.WeylSums.GaussianSuperposition
public import WaveTurbulence.Foundations.WeylSums.CutoffFourier

/-!
# Log-free major-arc bound for smooth cutoff quadratic sums

This is the generic-cutoff form of TARGET equation `wyel` (L1564).
The constant depends only on the fixed smooth compactly supported cutoff;
it is uniform in the scale, center, quadratic and linear frequencies, and
the coprime rational approximation. The proof uses rational completion,
Gaussian Poisson summation with merged decaying tails, and Fourier inversion.
-/

public section

open MeasureTheory
open scoped BigOperators ContDiff

namespace WaveTurbulence.WeylSums

/-- Quadratic lattice sum with a fixed cutoff, translated by an integer center. -/
@[expose] noncomputable def smoothGaussSum (χ : ℝ → ℂ) (L s r : ℝ) (h : ℤ) : ℂ :=
  ∑' n : ℤ, χ (((n : ℝ) - h) / L) * e (s * (n : ℝ) ^ 2 + r * n)

/-- Translation changes only the linear frequency and a unit phase. -/
theorem smoothGaussSum_shift (χ : ℝ → ℂ) (L s r : ℝ) (h : ℤ) :
    smoothGaussSum χ L s r h = e (s * (h : ℝ) ^ 2 + r * h) *
      smoothGaussSum χ L s (r + 2 * s * h) 0 := by
  unfold smoothGaussSum
  rw [← (Equiv.addRight h).tsum_eq]
  rw [← tsum_mul_left]
  apply tsum_congr
  intro n
  simp only [Equiv.coe_addRight, Int.cast_add, Int.cast_zero, add_sub_cancel_right, sub_zero]
  have hphase : s * ((n : ℝ) + h) ^ 2 + r * ((n : ℝ) + h) =
      (s * (h : ℝ) ^ 2 + r * h) + (s * (n : ℝ) ^ 2 + (r + 2 * s * h) * n) := by ring
  rw [hphase, e_add]
  ring

theorem norm_smoothGaussSum_shift (χ : ℝ → ℂ) (L s r : ℝ) (h : ℤ) :
    ‖smoothGaussSum χ L s r h‖ = ‖smoothGaussSum χ L s (r + 2 * s * h) 0‖ := by
  rw [smoothGaussSum_shift, norm_mul, norm_e, one_mul]

/-- **Smooth-cutoff quadratic Weyl bound**, TARGET `wyel` (L1564).
For every smooth compactly supported complex cutoff there is a cutoff-dependent
positive constant. The bound is log-free and uniform in all other parameters,
including the integer center and real linear frequency. -/
theorem exists_norm_smoothGaussSum_le (χ : ℝ → ℂ)
    (hc : HasCompactSupport χ) (hs : ContDiff ℝ ∞ χ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (L s r : ℝ) (h a : ℤ) (q : ℕ),
      1 ≤ L → 1 ≤ q → (q : ℝ) ≤ L → a.natAbs.Coprime q →
      |s - (a : ℝ) / q| ≤ 1 / ((q : ℝ) * L) →
      ‖smoothGaussSum χ L s r h‖ ≤ C * L /
        (Real.sqrt q * (1 + L * Real.sqrt |s - (a : ℝ) / q|)) := by
  obtain ⟨F, hF, hrep⟩ := exists_gaussian_fourier_representation χ hc hs
  let A : ℝ := ∫ ξ : ℝ, ‖F ξ‖
  have hA : 0 ≤ A := integral_nonneg (fun _ => norm_nonneg _)
  let C : ℝ := gaussianMajorArcConstant * (A + 1)
  refine ⟨C, mul_pos gaussianMajorArcConstant_pos (by linarith only [hA]), ?_⟩
  intro L s r h a q hL hq hqL ha happ
  have hLpos : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have hqpos : (0 : ℝ) < q := Nat.cast_pos.mpr (Nat.zero_lt_of_lt hq)
  let D : ℝ := Real.sqrt q * (1 + L * Real.sqrt |s - (a : ℝ) / q|)
  have hD : 0 < D := mul_pos (Real.sqrt_pos.mpr hqpos) (by positivity)
  let B : ℝ := gaussianMajorArcConstant * L / D
  have hB : 0 ≤ B := div_nonneg (mul_nonneg gaussianMajorArcConstant_pos.le hLpos.le) hD.le
  have hzero (ρ : ℝ) : ‖smoothGaussSum χ L s ρ 0‖ ≤ C * L / D := by
    have heq : smoothGaussSum χ L s ρ 0 =
        ∫ ξ : ℝ, F ξ * gaussianQuadraticSum L s (ρ + ξ / L) := by
      unfold smoothGaussSum
      simp only [Int.cast_zero, sub_zero]
      calc
        _ = ∑' n : ℤ, (gaussianWeight L n : ℂ) *
            (∫ ξ : ℝ, F ξ * e (ξ * ((n : ℝ) / L))) * e (s * (n : ℝ) ^ 2 + ρ * n) := by
          apply tsum_congr
          intro n
          rw [hrep ((n : ℝ) / L)]
          rfl
        _ = _ := gaussian_fourier_sum_integral F hF hLpos s ρ
    rw [heq]
    calc
      _ ≤ ∫ ξ : ℝ, ‖F ξ‖ * B := by
        apply norm_integral_le_of_norm_le (hF.norm.mul_const B)
        exact Filter.Eventually.of_forall (fun ξ => by
          rw [norm_mul]
          exact mul_le_mul_of_nonneg_left (norm_gaussianQuadraticSum_le L s (ρ + ξ / L) a
            hL hq hqL ha happ) (norm_nonneg _))
      _ = A * B := integral_mul_const _ _
      _ ≤ (A + 1) * B := mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one) hB
      _ = C * L / D := by dsimp [B, C]; ring
  rw [norm_smoothGaussSum_shift]
  exact hzero (r + 2 * s * h)

end WaveTurbulence.WeylSums
