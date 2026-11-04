/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Incoh.LeafFourierRepresentation
public import WaveTurbulence.Foundations.Incoh.SpatialDerivativeIntegrals

/-!
# The literal source spatial norm gives the leaf-product Fourier bound

TARGET (incohproof5)–(7). Smoothness and integrable derivative hypotheses
are derived from `spatialNorm`; none are postulated as carrier fields.
-/

public section
noncomputable section
open MeasureTheory WithLp
open scoped ContDiff ENNReal

namespace WaveTurbulence.Incoh

/-- The actual Euclidean momentum inputs in the flattened root/link coordinates. -/
@[expose] def IntegerLeafCoordinates.momentumLeafProduct {n d : ℕ} (P : IntegerLeafCoordinates n)
    (f : Fin (2 * n + 1) → Mom d → ℂ) : (Fin ((2 * n + 1) * d) → ℝ) → ℂ :=
  P.leafProduct (fun i x => f i (toLp 2 x))

/-- The Fourier-L¹ bound follows directly from the source's finite weighted spatial input bounds. -/
theorem IntegerLeafCoordinates.fourierL1_momentumLeafProduct_le {n d K M : ℕ}
    (P : IntegerLeafCoordinates n) (f : Fin (2 * n + 1) → Mom d → ℂ)
    (hK : d + 1 ≤ K) (hM : d < M) {B : ℝ} (hB : 0 ≤ B)
    (hf : ∀ i, Fourier.spatialNorm K M (f i) ≤ ENNReal.ofReal B) :
    Fourier.timeFourierNorm 0 (P.momentumLeafProduct f) ≤
      (ENNReal.ofReal (Fourier.coordinateFourierL1Constant d) *
        ENNReal.ofReal (sourceSobolevConstant d (d + 1) M * B)) ^ (2 * n + 1) := by
  have hKpos : 0 < K := (Nat.zero_lt_succ d).trans_le hK
  have hc (i : Fin (2 * n + 1)) : ContDiff ℝ (d + 1) (f i) :=
    (contDiff_of_spatialNorm_le hKpos (hf i)).of_le (by exact_mod_cast hK)
  apply P.fourierL1_leafProduct_le_pow (fun i x => f i (toLp 2 x))
  · intro i
    simpa only [toLp_ofLp] using hc i
  · intro i j hj
    simpa only [toLp_ofLp] using
      integrable_iteratedFDeriv_of_spatialNorm hKpos hM hB (hf i) (hj.trans hK)
  · intro i
    simpa only [Fourier.coordinateSobolevL1, toLp_ofLp] using
      derivativeL1Sum_le_of_spatialNorm hKpos hM hB (hf i) hK

end WaveTurbulence.Incoh
