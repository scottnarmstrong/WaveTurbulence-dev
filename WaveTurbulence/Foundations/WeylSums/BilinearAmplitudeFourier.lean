/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.WeylSums.BilinearBlocks
public import WaveTurbulence.Foundations.WeylSums.WeightedCutoffFourier
public import WaveTurbulence.Foundations.WeylSums.DerivativeContractions

/-!
# The quantitative Fourier coefficient in DH23 Lemma 6.6

After the sum/difference coordinate change, a `10d`-times differentiable
amplitude with derivative bound `D` has Fourier coefficient norm at most
`C_d D width^(2d)`. This is uniform in the spatial centers and width≥1.
-/

public section
open MeasureTheory
open scoped BigOperators ContDiff
namespace WaveTurbulence.WeylSums

/-- The original amplitude localized in the diagonal coordinate variables. -/
@[expose] noncomputable def weightedDiagonalAmplitude {d : ℕ}
    (Φ : EuclideanSpace ℝ (Fin d × Fin 2) → ℂ) (width : ℝ)
    (c z : EuclideanSpace ℝ (Fin d × Fin 2)) : ℂ :=
  Φ (bilinearDiagonalMap d z) * scaledTranslatedCutoff (bilinearJointCutoff d) width c z

/-- The derivative assumptions of DH23 (NTphibounds), in operator-norm
coordinates, give the required Fourier bound without an assumed number-
theoretic estimate. The coordinate change is proved contractive. -/
theorem exists_bilinear_amplitude_fourier_bound (d : ℕ) (hd : 3 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ width : ℝ, 1 ≤ width →
      ∀ (c : EuclideanSpace ℝ (Fin d × Fin 2))
        (Φ : EuclideanSpace ℝ (Fin d × Fin 2) → ℂ),
      ContDiff ℝ (10*d) Φ → ∀ D : ℝ, 0 ≤ D →
      (∀ j ≤ 10*d, ∀ x, ‖iteratedFDeriv ℝ j Φ x‖ ≤ D) →
      ∃ F : EuclideanSpace ℝ (Fin d × Fin 2) → ℂ, Integrable F ∧
        (∫ ξ, ‖F ξ‖) ≤ C*D*width^(2*d) ∧
        ∀ z, weightedDiagonalAmplitude Φ width c z = ∫ ξ, F ξ*e (∑ i, ξ i*z i) := by
  have hN : Fintype.card (Fin d × Fin 2) < 10*d := by
    simp only [Fintype.card_prod, Fintype.card_fin]
    omega
  have hκ : ContDiff ℝ (10*d) (bilinearJointCutoff d) :=
    (bilinearJointCutoff_contDiff d).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl _)
  obtain ⟨C,hC,hb⟩ := exists_weighted_cutoff_fourier_bound hN (bilinearJointCutoff d)
    (bilinearJointCutoff_hasCompactSupport d) hκ
  refine ⟨C,hC,?_⟩
  intro width hw c Φ hΦ D hD hderiv
  let f := Φ ∘ bilinearDiagonalMap d
  have hf : ContDiff ℝ (10*d) f := hΦ.comp (bilinearDiagonalMap d).contDiff
  have hfb (j : ℕ) (hj : j ≤ 10*d) (z : EuclideanSpace ℝ (Fin d × Fin 2)) :
      ‖iteratedFDeriv ℝ j f z‖ ≤ D :=
    (norm_iteratedFDeriv_comp_contraction_le hΦ (bilinearDiagonalMap d)
      (bilinearDiagonalMap_norm_le d) z hj).trans (hderiv j hj _)
  obtain ⟨F,hF,hnorm,hrep⟩ := hb width hw c f hf D hD hfb
  refine ⟨F,hF,?_,hrep⟩
  simpa only [Fintype.card_prod, Fintype.card_fin, Nat.mul_comm] using hnorm

end WaveTurbulence.WeylSums
