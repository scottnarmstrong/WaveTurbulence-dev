/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.SumintPar.SmallPairStrip

/-!
# The actual bilinear sum on the case-(a) small-region ordering strip

Uniformity in the spatial modulations allows them to depend on both time
variables. The pointwise stationary-phase bound is applied before Tonelli.
-/

@[expose] public section
set_option autoImplicit false

open MeasureTheory
open scoped ENNReal

namespace WaveTurbulence.SumintPar

/-- The ordering strip gains an extra reciprocal time scale for the actual
bilinear lattice sum, uniformly in all modulation functions. -/
theorem exists_bilinear_small_ordering_bound (d : ℕ) (hd : 3 ≤ d) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {L : ℝ}, 1 ≤ L → ∀ {c : ℝ}, 0 < c →
      ∀ (a b : Mom d) (ξ ζ : ℝ → ℝ → Mom d) (e : ℝ),
      (∫⁻ t : ℝ, ∫⁻ s : ℝ, if |s| ≤ L ∧ |t-e| ≤ |s|/c then
        ‖WeylSums.bilinearLatticeSum L s a b (ξ t s) (ζ t s)‖ₑ else 0) ≤
          ENNReal.ofReal (C*L^(2*d)/c) := by
  obtain ⟨Cs,hCs,hsmall⟩ := exists_bilinear_weyl_small_bound d
  let J := ∫ s : ℝ, (1+|s|)/scalarBracket s^d
  have hJ : 0 ≤ J := pair_kernel_mass_nonneg d
  refine ⟨2*Cs*J, mul_nonneg (mul_nonneg (by norm_num) hCs) hJ, ?_⟩
  intro L hL c hc a b ξ ζ e
  have hLp : 0 ≤ L := zero_le_one.trans hL
  have hK : 0 ≤ Cs*L^(2*d) := mul_nonneg hCs (pow_nonneg hLp _)
  calc
    _ ≤ ∫⁻ t : ℝ, ∫⁻ s : ℝ, ENNReal.ofReal (Cs*L^(2*d)) *
        (if |t-e| ≤ |s|/c then ENNReal.ofReal (1/scalarBracket s^d) else 0) := by
      apply lintegral_mono
      intro t
      apply lintegral_mono
      intro s
      dsimp only
      by_cases hh : |s| ≤ L ∧ |t-e| ≤ |s|/c
      · rw [ite_eq_left hh, ite_eq_left hh.2, ← ofReal_norm, ← ENNReal.ofReal_mul hK]
        apply ENNReal.ofReal_le_ofReal
        exact (hsmall hL s hh.1 a b (ξ t s) (ζ t s)).trans_eq (by ring)
      · rw [ite_eq_right hh]
        exact bot_le
    _ = ENNReal.ofReal (Cs*L^(2*d)) *
        (∫⁻ t : ℝ, ∫⁻ s : ℝ, if |t-e| ≤ |s|/c then
          ENNReal.ofReal (1/scalarBracket s^d) else 0) := by
      simp_rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ ≤ ENNReal.ofReal (Cs*L^(2*d)) *
        (ENNReal.ofReal (2/c)*ENNReal.ofReal J) :=
      mul_le_mul_right (small_pair_ordering_strip_le d hd hc e) _
    _ = _ := by
      rw [← ENNReal.ofReal_mul (div_nonneg (by norm_num) hc.le), ← ENNReal.ofReal_mul hK]
      congr 1
      dsimp [J]
      ring

end WaveTurbulence.SumintPar
