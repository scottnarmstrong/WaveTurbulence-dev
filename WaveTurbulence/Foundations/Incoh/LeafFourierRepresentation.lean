/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Incoh.LeafProductFourier
public import WaveTurbulence.Foundations.Fourier.TimeProduct
public import WaveTurbulence.Foundations.Fourier.TimeEuclidean

/-!
# Fourier inversion of the literal leaf product

TARGET (incohproof6). The actual Fourier density is integrable and
recovers the product at every point, with the paper's positive phase.
-/

public section
noncomputable section
open MeasureTheory WithLp Matrix
open scoped ContDiff ENNReal

namespace WaveTurbulence.Incoh

/-- The coordinate change and continuous leaf inputs give a continuous literal product. -/
theorem IntegerLeafCoordinates.continuous_leafProduct {n d : ℕ} (P : IntegerLeafCoordinates n)
    (f : Fin (2 * n + 1) → (Fin d → ℝ) → ℂ) (hf : ∀ i, Continuous (f i)) :
    Continuous (P.leafProduct f) := by
  unfold leafProduct
  apply continuous_finsetProd
  intro i _
  apply (hf i).comp
  change Continuous (fun z : Fin ((2 * n + 1) * d) → ℝ =>
    fun j : Fin d => (P.blockMatrix d *ᵥ z) (finProdFinEquiv (i, j)))
  fun_prop

/-- The source leaf product is the integral of its actual Fourier density, pointwise. -/
theorem IntegerLeafCoordinates.leafProduct_eq_fourierIntegral {n d : ℕ} (P : IntegerLeafCoordinates n)
    (f : Fin (2 * n + 1) → (Fin d → ℝ) → ℂ)
    (hf : ∀ i, ContDiff ℝ (d + 1) (fun x : EuclideanSpace ℝ (Fin d) => f i (ofLp x)))
    (hi : ∀ i j, j ≤ d + 1 → Integrable (iteratedFDeriv ℝ j
      (fun x : EuclideanSpace ℝ (Fin d) => f i (ofLp x))))
    {B : ℝ} (hB : ∀ i, Fourier.coordinateSobolevL1 (f i) ≤ B)
    (z : Fin ((2 * n + 1) * d) → ℝ) :
    P.leafProduct f z = ∫ ξ : Fin ((2 * n + 1) * d) → ℝ,
      Real.fourierChar (Fourier.timePairing _ ξ z) • Fourier.timeFourier (P.leafProduct f) ξ := by
  have hfinite : Fourier.timeFourierNorm 0 (P.leafProduct f) < ⊤ :=
    lt_of_le_of_lt (P.fourierL1_leafProduct_le_pow f hf hi hB) (by finiteness)
  have hiW := Fourier.integrable_of_timeFourierNorm_lt_top hfinite
  have hiFW := Fourier.integrable_timeFourier_of_norm_lt_top (le_refl (0 : ℝ)) hfinite
  have hc (i : Fin (2 * n + 1)) : Continuous (f i) := by
    simpa only [Function.comp_def, ofLp_toLp] using (hf i).continuous.comp (PiLp.continuous_toLp 2 _)
  calc
    _ = Fourier.timeFourier (Fourier.timeFourier (P.leafProduct f)) (-z) :=
      (Fourier.timeFourier_inversion hiW hiFW (P.continuous_leafProduct f hc) z).symm
    _ = _ := by
      change (∫ ξ, Real.fourierChar (-Fourier.timePairing _ ξ (-z)) •
        Fourier.timeFourier (P.leafProduct f) ξ) = _
      apply integral_congr_ae
      filter_upwards [] with ξ
      have hp : -Fourier.timePairing _ ξ (-z) = Fourier.timePairing _ ξ z := by
        rw [map_neg, neg_neg]
      rw [hp]

end WaveTurbulence.Incoh
