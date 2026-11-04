/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Incoh.IntegerLeafCoordinates
public import WaveTurbulence.Foundations.Fourier.FourierL1Product

/-!
# Fourier-L¹ control of the actual leaf product in link coordinates

TARGET (incohproof5)–(7). The proof reuses the landed product Fourier
bound. Its one-factor constant is independent of all coordinate entries.
-/

public section
noncomputable section
open MeasureTheory WithLp Matrix
open scoped ContDiff ENNReal

namespace WaveTurbulence.Incoh

/-- The literal product of leaf inputs after the integer spatial block change. -/
@[expose] def IntegerLeafCoordinates.leafProduct {n d : ℕ} (P : IntegerLeafCoordinates n)
    (f : Fin (2 * n + 1) → (Fin d → ℝ) → ℂ) (z : Fin ((2 * n + 1) * d) → ℝ) : ℂ :=
  ∏ i, f i ((Fourier.flattenBlocks (2 * n + 1) d).symm (P.blockMatrix d *ᵥ z) i)

/-- The leaf-product Fourier norm is controlled by actual one-factor derivative integrals. -/
theorem IntegerLeafCoordinates.fourierL1_leafProduct_le {n d : ℕ} (P : IntegerLeafCoordinates n)
    (f : Fin (2 * n + 1) → (Fin d → ℝ) → ℂ)
    (hf : ∀ i, ContDiff ℝ (d + 1) (fun x : EuclideanSpace ℝ (Fin d) => f i (ofLp x)))
    (hi : ∀ i j, j ≤ d + 1 → Integrable (iteratedFDeriv ℝ j
      (fun x : EuclideanSpace ℝ (Fin d) => f i (ofLp x)))) :
    Fourier.timeFourierNorm 0 (P.leafProduct f) ≤
      ENNReal.ofReal (Fourier.coordinateFourierL1Constant d) ^ (2 * n + 1) *
        ∏ i, ENNReal.ofReal (Fourier.coordinateSobolevL1 (f i)) :=
  Fourier.fourierL1_product_comp_matrix_le f (P.blockMatrix d) (P.abs_det_blockMatrix d) hf hi

/-- Uniform one-factor source bounds give an exponential-in-order Fourier-L¹ bound. -/
theorem IntegerLeafCoordinates.fourierL1_leafProduct_le_pow {n d : ℕ} (P : IntegerLeafCoordinates n)
    (f : Fin (2 * n + 1) → (Fin d → ℝ) → ℂ)
    (hf : ∀ i, ContDiff ℝ (d + 1) (fun x : EuclideanSpace ℝ (Fin d) => f i (ofLp x)))
    (hi : ∀ i j, j ≤ d + 1 → Integrable (iteratedFDeriv ℝ j
      (fun x : EuclideanSpace ℝ (Fin d) => f i (ofLp x))))
    {B : ℝ} (hB : ∀ i, Fourier.coordinateSobolevL1 (f i) ≤ B) :
    Fourier.timeFourierNorm 0 (P.leafProduct f) ≤
      (ENNReal.ofReal (Fourier.coordinateFourierL1Constant d) * ENNReal.ofReal B) ^ (2 * n + 1) := by
  apply (P.fourierL1_leafProduct_le f hf hi).trans
  calc
    _ ≤ ENNReal.ofReal (Fourier.coordinateFourierL1Constant d) ^ (2 * n + 1) *
        ∏ _i : Fin (2 * n + 1), ENNReal.ofReal B :=
      mul_le_mul' le_rfl (Finset.prod_le_prod (fun i _ => ENNReal.ofReal_le_ofReal (hB i)))
    _ = _ := by simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, mul_pow]

end WaveTurbulence.Incoh
