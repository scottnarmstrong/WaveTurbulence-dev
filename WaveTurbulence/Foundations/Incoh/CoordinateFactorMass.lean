/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Incoh.CoordinateFactorDerivative
public import WaveTurbulence.Foundations.Incoh.BoxCoordinateProducts

/-!
# Tensorized masses of coordinate factors and their first variation

The diagonal product rule replaces one scalar factor by its first
derivative. A common one-dimensional mass bound therefore suffices.
-/

public section
noncomputable section
open MeasureTheory Set
open scoped ENNReal ContDiff

namespace WaveTurbulence.Incoh

/-- Replace exactly one coordinate factor by its scalar derivative. -/
@[expose] def coordinateDerivativeReplacement {m : ℕ} (f : Fin m → ℝ → ℝ)
    (i j : Fin m) (x : ℝ) : ℝ := if j = i then deriv (f j) x else f j x

theorem coordinateFactorDiagonal_eq_sum {m : ℕ} (f : Fin m → ℝ → ℝ) (v : Fin m → ℝ) :
    coordinateFactorDiagonal f v = ∑ i, coordinateFactorProduct (coordinateDerivativeReplacement f i) v := by
  classical
  apply Finset.sum_congr rfl
  intro i _
  unfold coordinateFactorProduct
  rw [← Finset.mul_prod_erase Finset.univ
    (fun j => (coordinateDerivativeReplacement f i j (v j) : ℂ)) (Finset.mem_univ i)]
  simp only [coordinateDerivativeReplacement, ite_true]
  congr 1
  apply Finset.prod_congr rfl
  intro j hj
  simp only [Finset.ne_of_mem_erase hj, ite_false]

theorem enorm_coordinateFactorProduct {m : ℕ} (f : Fin m → ℝ → ℝ) (v : Fin m → ℝ) :
    ‖coordinateFactorProduct f v‖ₑ = ∏ i, ENNReal.ofReal ‖f i (v i)‖ := by
  rw [coordinateFactorProduct, ← ofReal_norm, norm_prod,
    ENNReal.ofReal_prod_of_nonneg (fun _ _ => norm_nonneg _)]
  simp only [Complex.norm_real]

/-- Independent scalar factor masses bound the actual box product. -/
theorem boxIntegral_coordinateFactorProduct_le {m : ℕ} {f : Fin m → ℝ → ℝ}
    (hf : ∀ i, Continuous (f i)) {B : ℝ≥0∞} (R : ℝ)
    (hm : ∀ i, (∫⁻ x in Icc (-R) R, ENNReal.ofReal ‖f i x‖) ≤ B) :
    Fourier.boxIntegral m (fun v => ‖coordinateFactorProduct f v‖ₑ) R ≤ B ^ m := by
  simp_rw [enorm_coordinateFactorProduct]
  have hmeas (i : Fin m) : Measurable (fun x : ℝ => ENNReal.ofReal ‖f i x‖) :=
    ENNReal.measurable_ofReal.comp (hf i).measurable.norm
  rw [boxIntegral_coordinate_product m (f := fun i x => ENNReal.ofReal ‖f i x‖) hmeas
    (fun _ _ => ENNReal.ofReal_ne_top)]
  exact (Finset.prod_le_prod (fun i _ => hm i)).trans_eq (by simp)

/-- The diagonal derivative costs at most `m` products of the same common mass. -/
theorem boxIntegral_coordinateFactorDiagonal_le {m : ℕ} {f : Fin m → ℝ → ℝ}
    (hf : ∀ i, ContDiff ℝ ∞ (f i)) {B : ℝ≥0∞} (R : ℝ)
    (hm : ∀ i, (∫⁻ x in Icc (-R) R, ENNReal.ofReal ‖f i x‖) ≤ B)
    (hdm : ∀ i, (∫⁻ x in Icc (-R) R, ENNReal.ofReal ‖deriv (f i) x‖) ≤ B) :
    Fourier.boxIntegral m (fun v => ‖coordinateFactorDiagonal f v‖ₑ) R ≤ (m : ℝ≥0∞) * B ^ m := by
  classical
  have hd (i j : Fin m) : ContDiff ℝ ∞ (coordinateDerivativeReplacement f i j) := by
    unfold coordinateDerivativeReplacement
    by_cases hij : j = i
    · simpa only [hij, ite_true] using
        (contDiff_infty_iff_deriv.mp (hf i)).2
    · simpa only [hij, ite_false] using hf j
  simp_rw [coordinateFactorDiagonal_eq_sum]
  apply (Fourier.boxIntegral_mono m (fun v => enorm_sum_le _ _) R).trans
  rw [boxIntegral_finset_sum m Finset.univ
    (fun i _ => (contDiff_coordinateFactorProduct (hd i)).continuous.measurable.enorm) R]
  calc
    _ ≤ ∑ _i : Fin m, B ^ m := by
      apply Finset.sum_le_sum
      intro i _
      apply boxIntegral_coordinateFactorProduct_le (fun j => (hd i j).continuous) R
      intro j
      by_cases hij : j = i
      · simpa only [coordinateDerivativeReplacement, hij, ite_true] using hdm i
      · simpa only [coordinateDerivativeReplacement, hij, ite_false] using hm j
    _ = _ := by simp [nsmul_eq_mul]

end WaveTurbulence.Incoh
