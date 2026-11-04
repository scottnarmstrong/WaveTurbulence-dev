/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Incoh.LeafCellDerivativeDecay
public import WaveTurbulence.Foundations.Incoh.CellCenterSummability
public import WaveTurbulence.Foundations.Fourier.TimeSobolev

/-!
# Summable Fourier-L¹ coefficients of the actual smooth leaf cells

TARGET Step (2). The source spatial norm gives an actual Fourier bound
for every cell, with a summable center envelope independent of the input.
-/

public section
noncomputable section
open MeasureTheory WithLp
open scoped ContDiff ENNReal

namespace WaveTurbulence.Incoh

/-- The one-cell Fourier constant is independent of its center. -/
@[expose] def leafCellFourierConstant (d M : ℕ) : ℝ :=
  Fourier.coordinateFourierL1Constant d * leafCellSobolevConstant d (d + 1) M

/-- The actual Fourier norm of a localized leaf has rapid center decay. -/
theorem timeFourierNorm_leafCell_le {d K M : ℕ} {f : Mom d → ℂ} {B : ℝ}
    (hK : d + 1 ≤ K) (hB : 0 ≤ B) (h : Fourier.spatialNorm K M f ≤ ENNReal.ofReal B)
    (c : Fin d → ℤ) :
    Fourier.timeFourierNorm 0 (fun x : Fin d → ℝ => leafCell f c (toLp 2 x)) ≤
      ENNReal.ofReal (leafCellFourierConstant d M * B * cellCenterWeight M c) := by
  have hKpos : 0 < K := (Nat.zero_lt_succ d).trans_le hK
  have hf := contDiff_leafCell (contDiff_of_spatialNorm_le hKpos h) c
  have hfc := hasCompactSupport_leafCell f c
  have hs : ContDiff ℝ (d + 1) (fun x : Mom d => leafCell f c (toLp 2 (ofLp x))) := by
    simpa only [toLp_ofLp, Nat.cast_add, Nat.cast_one] using hf.of_le (show ((d + 1 : ℕ) : ℕ∞ω) ≤ K by exact_mod_cast hK)
  have hi (j : ℕ) (hj : j ≤ d + 1) :
      Integrable (iteratedFDeriv ℝ j (fun x : Mom d => leafCell f c (toLp 2 (ofLp x)))) := by
    simpa only [toLp_ofLp] using
      (hf.continuous_iteratedFDeriv (m := j) (by exact_mod_cast hj.trans hK)).integrable_of_hasCompactSupport
        (hfc.iteratedFDeriv j)
  apply (Fourier.timeFourierNorm_zero_le_sobolev hs hi).trans
  have hsob := derivativeL1Sum_leafCell_le hKpos hK hB h c
  have hsob' : Fourier.coordinateSobolevL1 (fun x : Fin d → ℝ => leafCell f c (toLp 2 x)) ≤
      leafCellSobolevConstant d (d + 1) M * B / Fourier.momentumBracket (NTSP.intVec c) ^ M := by
    simpa only [Fourier.coordinateSobolevL1, toLp_ofLp] using hsob
  calc
    _ ≤ ENNReal.ofReal (Fourier.coordinateFourierL1Constant d) * ENNReal.ofReal
        (leafCellSobolevConstant d (d + 1) M * B / Fourier.momentumBracket (NTSP.intVec c) ^ M) :=
      mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal hsob')
    _ = _ := by
      have hCd : 0 ≤ Fourier.coordinateFourierL1Constant d :=
        Fourier.fourierL1Constant_nonneg (V := Mom d) (d + 1)
      rw [← ENNReal.ofReal_mul hCd]
      congr 1
      simp only [leafCellFourierConstant, cellCenterWeight, div_eq_mul_inv]
      ring

/-- The actual localized Fourier norms have a finite total coefficient over all centers. -/
theorem tsum_timeFourierNorm_leafCell_lt_top {d K M : ℕ} {f : Mom d → ℂ} {B : ℝ}
    (hK : d + 1 ≤ K) (hM : 2 * d ≤ M) (hB : 0 ≤ B)
    (h : Fourier.spatialNorm K M f ≤ ENNReal.ofReal B) :
    (∑' c : Fin d → ℤ,
      Fourier.timeFourierNorm 0 (fun x : Fin d → ℝ => leafCell f c (toLp 2 x))) < ⊤ := by
  apply lt_of_le_of_lt (ENNReal.tsum_le_tsum (fun c => timeFourierNorm_leafCell_le hK hB h c))
  exact ((summable_cellCenterWeight hM).mul_left (leafCellFourierConstant d M * B)).tsum_ofReal_lt_top

end WaveTurbulence.Incoh
