/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Fourier.BlockCoordinates
public import WaveTurbulence.Foundations.Fourier.LinearChange
public import WaveTurbulence.Foundations.Fourier.TimeSobolev
import Mathlib.Tactic

/-!
# Fourier-L¹ product bounds under unimodular changes

TARGET L1007–L1012. The constant depends only on the block dimension, and
is raised to the number of independent factors. No dependence on the
matrix entries or on the number of factors enters the one-factor constant.
-/

public section

open MeasureTheory WithLp Matrix
open scoped ENNReal

namespace WaveTurbulence.Fourier

/-- TARGET L1007–L1012: factorized `W^{d+1,1}` control survives every
volume-preserving real linear change of variables. In particular, this
applies to the source's unimodular integer changes with coefficients in
`{-1,0,1}`. The hypotheses are ordinary smoothness and integrability of
all derivatives through order `d+1` of the individual factors. -/
theorem fourierL1_product_comp_matrix_le {n d : ℕ}
    (f : Fin n → (Fin d → ℝ) → ℂ) (A : Matrix (Fin (n * d)) (Fin (n * d)) ℝ)
    (hA : |A.det| = 1)
    (hf : ∀ i, ContDiff ℝ (d + 1)
      (fun x : EuclideanSpace ℝ (Fin d) => f i (ofLp x)))
    (hi : ∀ i j, j ≤ d + 1 → Integrable (iteratedFDeriv ℝ j
      (fun x : EuclideanSpace ℝ (Fin d) => f i (ofLp x)))) :
    timeFourierNorm 0 (fun z => ∏ i, f i ((flattenBlocks n d).symm (A *ᵥ z) i)) ≤
      ENNReal.ofReal (coordinateFourierL1Constant d) ^ n *
        ∏ i, ENNReal.ofReal (coordinateSobolevL1 (f i)) := by
  have hfi (i : Fin n) : Integrable (f i) := by
    have hE : Integrable (fun x : EuclideanSpace ℝ (Fin d) => f i (ofLp x)) := by
      apply (integrable_norm_iff (hf i).continuous.aestronglyMeasurable).mp
      simpa only [norm_iteratedFDeriv_zero] using (hi i 0 (Nat.zero_le _)).norm
    exact ((PiLp.volume_preserving_ofLp (Fin d)).integrable_comp_emb
      (MeasurableEquiv.toLp 2 (Fin d → ℝ)).symm.measurableEmbedding).mp hE
  rw [timeFourierNorm_zero_comp_matrix hA
    (fun z => ∏ i, f i ((flattenBlocks n d).symm z i))]
  rw [← blockFourierL1_eq_flattened (fun x => ∏ i, f i (x i)), blockFourierL1_prod f hfi]
  calc
    ∏ i, timeFourierNorm 0 (f i) ≤ ∏ i,
        (ENNReal.ofReal (coordinateFourierL1Constant d) *
          ENNReal.ofReal (coordinateSobolevL1 (f i))) :=
      Finset.prod_le_prod (fun i _ => timeFourierNorm_zero_le_sobolev (hf i) (hi i))
    _ = _ := by rw [Finset.prod_mul_distrib]; simp

end WaveTurbulence.Fourier
