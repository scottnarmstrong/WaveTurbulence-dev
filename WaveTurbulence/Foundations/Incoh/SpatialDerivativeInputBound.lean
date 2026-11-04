/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Incoh.CoordinateDerivativeComponent
public import WaveTurbulence.Foundations.Incoh.SpatialCenterDecay

/-!
# Source spatial norms after taking actual momentum derivatives

TARGET Prop 5.1 Step (1). Taking `j` actual coordinate derivatives consumes
only `j` of the source finite smoothness budget and does not consume decay.
-/

public section
noncomputable section
open scoped ContDiff ENNReal

namespace WaveTurbulence.Incoh

/-- The actual derivative input retains the remaining source spatial norm, with an explicit
fixed dimensional constant. No derivative norm is assumed as a hypothesis. -/
theorem spatialNorm_momentumDerivative_le {d N j K M M' : ℕ} {f : Mom d → ℂ} {B : ℝ}
    (hN : 0 < N) (hB : 0 ≤ B) (h : Fourier.spatialNorm N M f ≤ ENNReal.ofReal B)
    (hJK : j + K ≤ N) (hM : M' ≤ M) (ρ : Fin j → Fin d) :
    Fourier.spatialNorm K M' (Fourier.momentumDerivative ρ f) ≤
      ENNReal.ofReal ((max 1 (d : ℝ)) ^ N * B) := by
  have hf := contDiff_of_spatialNorm_le hN h
  have hdf := contDiff_momentumDerivative hf hJK ρ
  rw [Fourier.spatialNorm, ite_eq_left (Or.inr hdf)]
  apply iSup_le
  intro k
  apply iSup_le
  intro hk
  apply iSup_le
  intro σ
  apply iSup_le
  intro x
  have hjk : j + k ≤ N := (Nat.add_le_add_left hk j).trans hJK
  have hn := (norm_momentumDerivative_momentumDerivative_le hf hjk ρ σ x).trans
    (norm_iteratedFDeriv_le_of_spatialNorm hB h hjk x)
  have hx := one_le_momentumBracket x
  have hxpos : 0 < Fourier.momentumBracket x ^ M := pow_pos (zero_lt_one.trans_le hx) _
  have hd : (d : ℝ) ^ (j + k) ≤ (max 1 (d : ℝ)) ^ N :=
    (pow_le_pow_left₀ (Nat.cast_nonneg d) (le_max_right _ _) (j + k)).trans
      (pow_le_pow_right₀ (le_max_left _ _) hjk)
  have hw : Fourier.momentumBracket x ^ M' *
      ‖Fourier.momentumDerivative σ (Fourier.momentumDerivative ρ f) x‖ ≤ (max 1 (d : ℝ)) ^ N * B := by
    calc
      _ ≤ Fourier.momentumBracket x ^ M *
          ‖Fourier.momentumDerivative σ (Fourier.momentumDerivative ρ f) x‖ :=
        mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hx hM) (norm_nonneg _)
      _ ≤ Fourier.momentumBracket x ^ M * ((d : ℝ) ^ (j + k) * (B / Fourier.momentumBracket x ^ M)) :=
        mul_le_mul_of_nonneg_left hn hxpos.le
      _ = (d : ℝ) ^ (j + k) * B := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_right hd hB
  rw [← ofReal_norm, ← ENNReal.ofReal_mul (pow_nonneg (zero_lt_one.trans_le hx).le _)]
  exact ENNReal.ofReal_le_ofReal hw

end WaveTurbulence.Incoh
