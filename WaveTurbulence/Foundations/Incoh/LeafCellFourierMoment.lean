/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Incoh.WeightedFourierL1
public import WaveTurbulence.Foundations.Incoh.LeafCellDerivativeDecay
public import WaveTurbulence.Foundations.Fourier.TimeEuclidean

/-! # Actual leaf-cell Fourier moments from finite source smoothness

TARGET Proposition 5.1 Step (1): spectral moments needed for momentum
derivatives retain the original summable cell-center decay.
-/

public section
noncomputable section
open MeasureTheory WithLp
open scoped FourierTransform ContDiff

namespace WaveTurbulence.Incoh

/-- Fixed dimensional and derivative-order coefficient of a leaf-cell Fourier moment. -/
@[expose] def leafCellFourierMomentConstant (d J M : ℕ) : ℝ :=
  weightedFourierL1Constant (Mom d) (d + 1) J * leafCellSobolevConstant d (d + 1 + J) M

/-- Actual polynomial Fourier moments of a localized leaf have the full source center decay. -/
theorem integrable_fourierMoment_leafCell_and_integral_le {d K M J : ℕ}
    {f : Mom d → ℂ} {B : ℝ} (hK : d + 1 + J ≤ K) (hB : 0 ≤ B)
    (h : Fourier.spatialNorm K M f ≤ ENNReal.ofReal B) (c : Fin d → ℤ) :
    Integrable (fun ξ : Mom d => (1 + ‖ξ‖) ^ J * ‖𝓕 (leafCell f c) ξ‖) ∧
      (∫ ξ : Mom d, (1 + ‖ξ‖) ^ J * ‖𝓕 (leafCell f c) ξ‖) ≤
        leafCellFourierMomentConstant d J M * B / Fourier.momentumBracket (NTSP.intVec c) ^ M := by
  have hKpos : 0 < K := by omega
  have hf := contDiff_leafCell (contDiff_of_spatialNorm_le hKpos h) c
  have hfc := hasCompactSupport_leafCell f c
  have hs : ContDiff ℝ (d + 1 + J) (leafCell f c) := hf.of_le (by exact_mod_cast hK)
  have hi (j : ℕ) (hj : j ≤ d + 1 + J) : Integrable (iteratedFDeriv ℝ j (leafCell f c)) :=
    (hf.continuous_iteratedFDeriv (m := j) (by exact_mod_cast hj.trans hK)).integrable_of_hasCompactSupport
      (hfc.iteratedFDeriv j)
  have hn : Module.finrank ℝ (Mom d) < d + 1 := by simp [Mom]
  obtain ⟨hint, hb⟩ := integrable_weighted_fourier_and_integral_le (N := d + 1) (J := J) hn hs hi
  refine ⟨hint, hb.trans ?_⟩
  have hC : 0 ≤ weightedFourierL1Constant (Mom d) (d + 1) J := by
    unfold weightedFourierL1Constant
    exact mul_nonneg (by positivity) (integral_nonneg (fun ξ => Real.rpow_nonneg (by positivity) _))
  calc
    _ ≤ weightedFourierL1Constant (Mom d) (d + 1) J *
        (leafCellSobolevConstant d (d + 1 + J) M * B / Fourier.momentumBracket (NTSP.intVec c) ^ M) :=
      mul_le_mul_of_nonneg_left (derivativeL1Sum_leafCell_le hKpos hK hB h c) hC
    _ = _ := by unfold leafCellFourierMomentConstant; ring

/-- Coordinate-frequency form used by the literal source spectral density. -/
theorem integrable_coordinate_fourierMoment_leafCell_and_integral_le {d K M J : ℕ}
    {f : Mom d → ℂ} {B : ℝ} (hK : d + 1 + J ≤ K) (hB : 0 ≤ B)
    (h : Fourier.spatialNorm K M f ≤ ENNReal.ofReal B) (c : Fin d → ℤ) :
    Integrable (fun ξ : Fin d → ℝ => (1 + ‖toLp 2 ξ‖) ^ J *
      ‖Fourier.timeFourier (fun x => leafCell f c (toLp 2 x)) ξ‖) ∧
      (∫ ξ : Fin d → ℝ, (1 + ‖toLp 2 ξ‖) ^ J *
        ‖Fourier.timeFourier (fun x => leafCell f c (toLp 2 x)) ξ‖) ≤
        leafCellFourierMomentConstant d J M * B / Fourier.momentumBracket (NTSP.intVec c) ^ M := by
  obtain ⟨hi, hb⟩ := integrable_fourierMoment_leafCell_and_integral_le hK hB h c
  let G := fun ξ : Fin d → ℝ => (1 + ‖toLp 2 ξ‖) ^ J *
    ‖Fourier.timeFourier (fun x => leafCell f c (toLp 2 x)) ξ‖
  have he (ξ : Mom d) : G (ofLp ξ) = (1 + ‖ξ‖) ^ J * ‖𝓕 (leafCell f c) ξ‖ := by
    simp only [G, Fourier.timeFourier_eq_euclidean, toLp_ofLp]
  have hcomp : Integrable (fun ξ : Mom d => G (ofLp ξ)) := by
    simpa only [he] using hi
  refine ⟨((PiLp.volume_preserving_ofLp (Fin d)).integrable_comp_emb
    (MeasurableEquiv.toLp 2 (Fin d → ℝ)).symm.measurableEmbedding).mp hcomp, ?_⟩
  change (∫ ξ, G ξ) ≤ _
  rw [← (PiLp.volume_preserving_ofLp (Fin d)).integral_comp
    (MeasurableEquiv.toLp 2 (Fin d → ℝ)).symm.measurableEmbedding G]
  simpa only [he] using hb

end WaveTurbulence.Incoh
