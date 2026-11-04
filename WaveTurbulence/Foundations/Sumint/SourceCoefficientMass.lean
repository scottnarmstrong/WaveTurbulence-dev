/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Sumint.TensorLabelMass

/-!
# Separating primary and alternative coefficient masses

The primary label sum retains spatial decay. Alternative labels are
counted separately and use the uniform order-zero weight bound. The
Fourier coefficient itself remains the exact source tensor product.
-/

public section

open MeasureTheory Finset
open scoped ENNReal FourierTransform

namespace WaveTurbulence.Sumint

/-- Exact real factorization of the source Fourier coefficient mass. -/
theorem integral_norm_sourceCoefficient_eq {d : ℕ} (D : SumintDatum d)
    (a b : D.S.VIdx → Fin d → ℤ) :
    (∫ ξ, ‖sourceCoefficient D a b ξ‖) =
      (∏ v, ∫ ξ : Mom d, ‖𝓕 (localizedWeight (a v) (D.wK v)) ξ‖) *
        ∏ v, ∫ ξ : Mom d, ‖𝓕 (localizedWeight (b v) (D.wL v)) ξ‖ := by
  unfold sourceCoefficient
  rw [integral_norm_tensor_fourier]
  simp only [Fintype.prod_sum_type,sourceWeight,Sum.elim_inl,Sum.elim_inr]

/-- Exact nonnegative factorization, suitable for Tonelli over labels. -/
theorem ofReal_integral_norm_sourceCoefficient_eq {d : ℕ} (D : SumintDatum d)
    (a b : D.S.VIdx → Fin d → ℤ) :
    ENNReal.ofReal (∫ ξ, ‖sourceCoefficient D a b ξ‖) =
      (∏ v, ENNReal.ofReal (∫ ξ : Mom d, ‖𝓕 (localizedWeight (a v) (D.wK v)) ξ‖)) *
        ∏ v, ENNReal.ofReal (∫ ξ : Mom d, ‖𝓕 (localizedWeight (b v) (D.wL v)) ξ‖) := by
  rw [integral_norm_sourceCoefficient_eq,
    ENNReal.ofReal_mul (Finset.prod_nonneg (fun _ _ => integral_nonneg (fun _ => norm_nonneg _))),
    ENNReal.ofReal_prod_of_nonneg (fun _ _ => integral_nonneg (fun _ => norm_nonneg _)),
    ENNReal.ofReal_prod_of_nonneg (fun _ _ => integral_nonneg (fun _ => norm_nonneg _))]

/-- Uniform alternative coefficient mass at every localization label. -/
theorem alternative_fourier_mass_le {d : ℕ} (hd : 1 ≤ d) (D : SumintDatum d)
    {A L γ η : ℝ} {Dsteps : ℕ} (hL : 0 < L) (hD : D.Admissible A L γ η Dsteps)
    (b : D.S.VIdx → Fin d → ℤ) :
    (∏ v, ENNReal.ofReal (∫ ξ : Mom d, ‖𝓕 (localizedWeight (b v) (D.wL v)) ξ‖)) ≤
      ENNReal.ofReal (cellFourierFactor d^D.S.M *
        ∏ v, L^(-(gammaWeight d γ-Real.sqrt η)*(D.g' v : ℝ))) := by
  let B := fun v : D.S.VIdx => L^(-(gammaWeight d γ-Real.sqrt η)*(D.g' v : ℝ))
  have hB (v : D.S.VIdx) : 0 ≤ B v := Real.rpow_nonneg hL.le _
  have hsingle (v : D.S.VIdx) :
      ENNReal.ofReal (∫ ξ : Mom d, ‖𝓕 (localizedWeight (b v) (D.wL v)) ξ‖) ≤
        ENNReal.ofReal (cellFourierFactor d*B v) :=
    ENNReal.ofReal_le_ofReal
      (localizedWeight_fourier_integrable_and_bound (by omega : 30*d ≠ 0) (by omega)
        (hB v) (hD.2.2.2.2.1 v).2 (b v)).2
  calc
    _ ≤ ∏ v, ENNReal.ofReal (cellFourierFactor d*B v) :=
      Finset.prod_le_prod (fun v _ => hsingle v)
    _ = _ := by
      rw [← ENNReal.ofReal_prod_of_nonneg (fun v _ => mul_nonneg (cellFourierFactor_nonneg _) (hB v))]
      congr 1
      rw [Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ,card_vector_index]

/-- The two drafted multiplicity products combine to exactly M1. -/
theorem prod_primary_alternative_decay {d : ℕ} (D : SumintDatum d) {L : ℝ} (hL : 0 < L)
    (s : ℝ) :
    (∏ v, L^(-s*(D.g v : ℝ))) * (∏ v, L^(-s*(D.g' v : ℝ))) = L^(-s*D.M₁) := by
  simpa only [Fintype.prod_sum_type,sourceWeightMultiplicity,Sum.elim_inl,Sum.elim_inr] using
    prod_source_decay D hL s

end WaveTurbulence.Sumint
