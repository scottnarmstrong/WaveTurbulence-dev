/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Incoh.CoordinateMultilinearBound

/-!
# Consequences of the literal source spatial input norm

The hypotheses are the landed `spatialNorm` bounds, not assumed Fourier
bounds. Coordinate-word bounds give actual Fréchet operator bounds.
-/

public section
noncomputable section
open scoped ContDiff ENNReal

namespace WaveTurbulence.Incoh

/-- A finite positive-order source spatial norm includes the required finite smoothness. -/
theorem contDiff_of_spatialNorm_le {d K M : ℕ} {f : Mom d → ℂ} {B : ℝ}
    (hK : 0 < K) (h : Fourier.spatialNorm K M f ≤ ENNReal.ofReal B) : ContDiff ℝ K f := by
  by_contra hc
  have hh : ¬(K = 0 ∨ ContDiff ℝ K f) := by
    rintro (hz | hd)
    · exact (Nat.ne_of_gt hK) hz
    · exact hc hd
  rw [Fourier.spatialNorm, ite_eq_right hh] at h
  exact (not_le_of_gt ENNReal.ofReal_lt_top) h

/-- Extract the actual weighted coordinate derivative bound from the source norm. -/
theorem weighted_momentumDerivative_le_of_spatialNorm {d K M j : ℕ} {f : Mom d → ℂ} {B : ℝ}
    (hB : 0 ≤ B) (h : Fourier.spatialNorm K M f ≤ ENNReal.ofReal B)
    (hj : j ≤ K) (ρ : Fin j → Fin d) (x : Mom d) :
    Fourier.momentumBracket x ^ M * ‖Fourier.momentumDerivative ρ f x‖ ≤ B := by
  classical
  have hc : K = 0 ∨ ContDiff ℝ K f := by
    by_contra hn
    rw [Fourier.spatialNorm, ite_eq_right hn] at h
    exact (not_le_of_gt ENNReal.ofReal_lt_top) h
  have hb : ENNReal.ofReal (Fourier.momentumBracket x ^ M) *
      ‖Fourier.momentumDerivative ρ f x‖ₑ ≤ ENNReal.ofReal B := by
    apply le_trans (le_iSup (fun x => ENNReal.ofReal (Fourier.momentumBracket x ^ M) *
      ‖Fourier.momentumDerivative ρ f x‖ₑ) x)
    apply le_trans _ h
    rw [Fourier.spatialNorm, ite_eq_left hc]
    exact le_iSup_of_le j (le_iSup_of_le hj (le_iSup_of_le ρ le_rfl))
  have hw : 0 ≤ Fourier.momentumBracket x ^ M :=
    pow_nonneg (Real.sqrt_nonneg _) M
  rw [← ofReal_norm, ← ENNReal.ofReal_mul hw] at hb
  exact (ENNReal.ofReal_le_ofReal_iff hB).mp hb

/-- Actual operator derivatives inherit the source spatial decay with a finite dimension loss. -/
theorem norm_iteratedFDeriv_le_of_spatialNorm {d K M j : ℕ} {f : Mom d → ℂ} {B : ℝ}
    (hB : 0 ≤ B) (h : Fourier.spatialNorm K M f ≤ ENNReal.ofReal B)
    (hj : j ≤ K) (x : Mom d) :
    ‖iteratedFDeriv ℝ j f x‖ ≤ (d : ℝ) ^ j * (B / Fourier.momentumBracket x ^ M) := by
  have hw : 0 < Fourier.momentumBracket x ^ M :=
    pow_pos (Real.sqrt_pos.mpr (by positivity)) M
  apply multilinear_norm_le_of_coordinate_bound _ (div_nonneg hB hw.le)
  intro ρ
  apply (le_div_iff₀ hw).mpr
  simpa only [Fourier.momentumDerivative, mul_comm] using weighted_momentumDerivative_le_of_spatialNorm hB h hj ρ x

end WaveTurbulence.Incoh
