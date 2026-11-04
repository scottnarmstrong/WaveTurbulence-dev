/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Sumint.SourceTotalCoefficientMass
public import WaveTurbulence.Foundations.Sumint.WeightedCutoffInput

/-!
# Source coefficients normalized by the weight decay already inside the kernel

The actual kernel coefficient contains sourceWeightDecay. Divide the
spatial Fourier coefficient by this strictly positive real scalar, so
recombination restores the original source expression exactly and the
weight gain is counted once. The normalized total coefficient mass has
only a constant to the literal input count.
-/

public section
open MeasureTheory ENNReal
open scoped Classical
namespace WaveTurbulence.Sumint

/-- The actual source weight decay is strictly positive at positive lattice scale. -/
theorem sourceWeightDecay_pos {d : ℕ} (D : SumintDatum d) {L : ℝ} (hL : 0 < L) (γ η : ℝ) :
    0 < sourceWeightDecay D L γ η := Real.rpow_pos_of_pos hL _

/-- Normalize the spatial Fourier coefficient by the strictly positive decay already included in the time kernel. -/
@[expose] noncomputable def normalizedSourceCoefficient {d : ℕ} (D : SumintDatum d) (L γ η : ℝ)
    (a b : D.S.VIdx → Fin d → ℤ) (ξ : (D.S.VIdx ⊕ D.S.VIdx) → Mom d) : ℂ :=
  (((sourceWeightDecay D L γ η)⁻¹:ℝ):ℂ)*sourceCoefficient D a b ξ

/-- Restoring the source decay recovers the original spatial Fourier coefficient exactly. -/
theorem sourceWeightDecay_mul_normalizedSourceCoefficient {d : ℕ} (D : SumintDatum d)
    {L : ℝ} (hL : 0 < L) (γ η : ℝ) (a b : D.S.VIdx → Fin d → ℤ)
    (ξ : (D.S.VIdx ⊕ D.S.VIdx) → Mom d) :
    (sourceWeightDecay D L γ η:ℂ)*normalizedSourceCoefficient D L γ η a b ξ = sourceCoefficient D a b ξ := by
  unfold normalizedSourceCoefficient
  rw [← mul_assoc,← Complex.ofReal_mul,mul_inv_cancel₀ (sourceWeightDecay_pos D hL γ η).ne',Complex.ofReal_one,one_mul]

/-- The normalized coefficient is genuinely integrable. -/
theorem integrable_normalizedSourceCoefficient {d : ℕ} (hd : 1 ≤ d) (D : SumintDatum d)
    {A L γ η : ℝ} {N : ℕ} (hL : 0 < L) (hD : D.Admissible A L γ η N)
    (a b : D.S.VIdx → Fin d → ℤ) : Integrable (normalizedSourceCoefficient D L γ η a b) :=
  (integrable_sourceCoefficient hd D hL hD a b).const_mul _

/-- Normalization changes the actual absolute coefficient mass by exactly the reciprocal source decay. -/
theorem integral_norm_normalizedSourceCoefficient {d : ℕ} (D : SumintDatum d)
    {L : ℝ} (hL : 0 < L) (γ η : ℝ) (a b : D.S.VIdx → Fin d → ℤ) :
    (∫ ξ, ‖normalizedSourceCoefficient D L γ η a b ξ‖) =
      (sourceWeightDecay D L γ η)⁻¹*(∫ ξ, ‖sourceCoefficient D a b ξ‖) := by
  simp only [normalizedSourceCoefficient,norm_mul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr (sourceWeightDecay_pos D hL γ η))]
  exact integral_const_mul _ (fun ξ => ‖sourceCoefficient D a b ξ‖)

/-- Summing every normalized spatial Fourier coefficient costs only a constant to the actual input count. -/
theorem tsum_normalizedSourceCoefficient_mass_le {d : ℕ} (hd : 1 ≤ d) (D : SumintDatum d)
    {A L γ η : ℝ} {N : ℕ} (hA : 1 ≤ A) (hL : 0 < L) (hD : D.Admissible A L γ η N) :
    (∑' a : D.S.VIdx → Fin d → ℤ,
      ∑ b ∈ sourceAlternativeLabels D hD a,
        ENNReal.ofReal (∫ ξ, ‖normalizedSourceCoefficient D L γ η a b ξ‖)) ≤
      ENNReal.ofReal ((((9:ℝ)^d*A^d)*summedCellFourierFactor d (30*d)*cellFourierFactor d)^D.S.M) := by
  have hW := sourceWeightDecay_pos D hL γ η
  simp_rw [integral_norm_normalizedSourceCoefficient D hL γ η,
    ENNReal.ofReal_mul (inv_nonneg.mpr hW.le),← Finset.mul_sum]
  rw [ENNReal.tsum_mul_left]
  apply (mul_le_mul' le_rfl (tsum_sourceCoefficient_mass_le hd D hA hL hD)).trans_eq
  rw [← ENNReal.ofReal_mul (inv_nonneg.mpr hW.le)]
  congr 1
  change (sourceWeightDecay D L γ η)⁻¹*(_*sourceWeightDecay D L γ η) = _
  rw [mul_left_comm,inv_mul_cancel₀ hW.ne',mul_one]

end WaveTurbulence.Sumint
