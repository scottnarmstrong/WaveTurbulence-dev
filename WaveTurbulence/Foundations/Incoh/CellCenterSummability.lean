/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Incoh.SpatialCenterDecay
public import WaveTurbulence.Foundations.Fourier.LatticeConvergence
public import WaveTurbulence.Foundations.NTSP.Basic

/-!
# Summability of the literal smooth-cell center coefficients

The source's radial Japanese-bracket decay is dominated by the landed
summable integer-lattice weight. No rapid-decay sequence is assumed.
-/

public section
noncomputable section

namespace WaveTurbulence.Incoh

/-- The actual coefficient carried by a cell center. -/
@[expose] def cellCenterWeight {d : ℕ} (M : ℕ) (c : Fin d → ℤ) : ℝ :=
  1 / Fourier.momentumBracket (NTSP.intVec c) ^ M

/-- The literal radial cell-center weights are summable at every source decay order. -/
theorem summable_cellCenterWeight {d M : ℕ} (hM : 2 * d ≤ M) :
    Summable (cellCenterWeight (d := d) M) := by
  have hnorm (c : Fin d → ℤ) : ‖c‖ ≤ ‖NTSP.intVec c‖ := by
    rw [← Fourier.norm_integerCast c]
    apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
    intro i
    exact PiLp.norm_apply_le (NTSP.intVec c) i
  have hb (c : Fin d → ℤ) : cellCenterWeight M c ≤
      (2 : ℝ) ^ M * (1 + ‖c‖) ^ (-((2 * d : ℕ) : ℤ)) := by
    have hbr := one_le_momentumBracket (NTSP.intVec c)
    have hnx : ‖NTSP.intVec c‖ ≤ Fourier.momentumBracket (NTSP.intVec c) := by
      unfold Fourier.momentumBracket
      exact (Real.le_sqrt (norm_nonneg _) (by positivity)).mpr (by linarith)
    have hbase : 1 + ‖c‖ ≤ 2 * Fourier.momentumBracket (NTSP.intVec c) := by
      linarith only [hnorm c, hbr, hnx]
    have hp : (1 + ‖c‖) ^ (2 * d) ≤ (2 : ℝ) ^ M * Fourier.momentumBracket (NTSP.intVec c) ^ M := by
      apply (pow_le_pow_right₀ (by linarith [norm_nonneg c] : 1 ≤ 1 + ‖c‖) hM).trans
      simpa only [mul_pow] using pow_le_pow_left₀ (by positivity : 0 ≤ 1 + ‖c‖) hbase M
    rw [cellCenterWeight, zpow_neg, zpow_natCast, ← div_eq_mul_inv]
    apply (div_le_div_iff₀ (pow_pos (lt_of_lt_of_le zero_lt_one hbr) M)
      (pow_pos (show (0 : ℝ) < 1 + ‖c‖ by positivity) (2 * d))).mpr
    simpa only [one_mul] using hp
  exact Summable.of_nonneg_of_le (fun c => div_nonneg zero_le_one
    (pow_nonneg (zero_le_one.trans (one_le_momentumBracket (NTSP.intVec c))) M)) hb
    (WaveTurbulence.summable_one_add_norm_zpow.mul_left ((2 : ℝ) ^ M))

end WaveTurbulence.Incoh
