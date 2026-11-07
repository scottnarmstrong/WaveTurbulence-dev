/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.SumintPar.SourceCoefficientMass
public import WaveTurbulence.Foundations.SumintPar.AlternativeLabelFamily

/-!
# Total Fourier coefficient mass after source localization

Primary labels are summed using the actual spatial decay before it is
discarded. Alternative labels are restricted to the fixed predecessor
family. The resulting loss is exponential in M and retains the exact
full M1 weight factor.
-/

@[expose] public section
set_option autoImplicit false

open MeasureTheory Finset
open scoped ENNReal FourierTransform

namespace WaveTurbulence.SumintPar

/-- Sum the alternative cell coefficients using only the fixed-family count. -/
theorem sum_alternative_sourceCoefficient_mass_le {d : ℕ} (hd : 1 ≤ d) (D : SumintDatum d)
    {A L γ η : ℝ} {Dsteps : ℕ} (hL : 0 < L) (hD : D.Admissible A L γ η Dsteps)
    (a : D.S.VIdx → Fin d → ℤ) (r : Mom d) :
    (∑ b ∈ sourceAlternativeLabels D hD a, ENNReal.ofReal (∫ ξ, ‖sourceCoefficient D a b r ξ‖)) ≤
      ENNReal.ofReal (((9:ℝ)^d*A^d)^D.S.M) *
        (∏ v, ENNReal.ofReal (∫ ξ : Mom d, ‖𝓕 (localizedWeight (a v) (D.wK v r)) ξ‖)) *
        ENNReal.ofReal (cellFourierFactor d^D.S.M *
          ∏ v, L^(-(gammaWeight d γ-Real.sqrt η)*(D.g' v : ℝ))) := by
  let P := ∏ v, ENNReal.ofReal (∫ ξ : Mom d, ‖𝓕 (localizedWeight (a v) (D.wK v r)) ξ‖)
  let Q := ENNReal.ofReal (cellFourierFactor d^D.S.M *
    ∏ v, L^(-(gammaWeight d γ-Real.sqrt η)*(D.g' v : ℝ)))
  have hc : ((sourceAlternativeLabels D hD a).card : ℝ≥0∞) ≤
      ENNReal.ofReal (((9:ℝ)^d*A^d)^D.S.M) := by
    simpa only [ENNReal.ofReal_natCast] using
      ENNReal.ofReal_le_ofReal (card_sourceAlternativeLabels_le D hD a)
  calc
    _ ≤ ∑ _b ∈ sourceAlternativeLabels D hD a, P*Q := by
      apply Finset.sum_le_sum
      intro b _
      rw [ofReal_integral_norm_sourceCoefficient_eq D a b r]
      exact mul_le_mul' le_rfl (alternative_fourier_mass_le hd D hL hD b)
    _ = ((sourceAlternativeLabels D hD a).card : ℝ≥0∞)*P*Q := by
      simp only [Finset.sum_const,nsmul_eq_mul,mul_assoc]
    _ ≤ _ := mul_le_mul' (mul_le_mul' hc le_rfl) le_rfl

/-- Full summed coefficient mass with a constant exponential only in M. -/
theorem tsum_sourceCoefficient_mass_le {d : ℕ} (hd : 1 ≤ d) (D : SumintDatum d)
    {A L γ η : ℝ} {Dsteps : ℕ} (hA : 1 ≤ A) (hL : 0 < L)
    (hD : D.Admissible A L γ η Dsteps) (r : Mom d) :
    (∑' a : D.S.VIdx → Fin d → ℤ,
      ∑ b ∈ sourceAlternativeLabels D hD a, ENNReal.ofReal (∫ ξ, ‖sourceCoefficient D a b r ξ‖)) ≤
      ENNReal.ofReal ((((9:ℝ)^d*A^d)*summedCellFourierFactor d (d+1)*cellFourierFactor d)^D.S.M *
        L^(-(gammaWeight d γ-Real.sqrt η)*D.M₁)) := by
  let P := fun a : D.S.VIdx → Fin d → ℤ =>
    ∏ v, ENNReal.ofReal (∫ ξ : Mom d, ‖𝓕 (localizedWeight (a v) (D.wK v r)) ξ‖)
  let U := ((9:ℝ)^d*A^d)^D.S.M
  let V := cellFourierFactor d^D.S.M *
    ∏ v, L^(-(gammaWeight d γ-Real.sqrt η)*(D.g' v : ℝ))
  let W := summedCellFourierFactor d (d+1)^D.S.M *
    ∏ v, L^(-(gammaWeight d γ-Real.sqrt η)*(D.g v : ℝ))
  have hU : 0 ≤ U := pow_nonneg (mul_nonneg (by positivity) (pow_nonneg (zero_le_one.trans hA) _)) _
  have hW : 0 ≤ W := mul_nonneg (pow_nonneg (summedCellFourierFactor_nonneg _ _) _)
    (Finset.prod_nonneg (fun _ _ => Real.rpow_nonneg hL.le _))
  calc
    _ ≤ ∑' a, ENNReal.ofReal U*P a*ENNReal.ofReal V :=
      ENNReal.tsum_le_tsum (fun a => sum_alternative_sourceCoefficient_mass_le hd D hL hD a r)
    _ = ENNReal.ofReal U*(∑' a, P a)*ENNReal.ofReal V := by
      rw [ENNReal.tsum_mul_right,ENNReal.tsum_mul_left]
    _ ≤ ENNReal.ofReal U*ENNReal.ofReal W*ENNReal.ofReal V :=
      mul_le_mul' (mul_le_mul' le_rfl (tsum_primary_fourier_mass_le hd D hL hD r)) le_rfl
    _ = _ := by
      rw [← ENNReal.ofReal_mul hU,← ENNReal.ofReal_mul (mul_nonneg hU hW)]
      congr 1
      dsimp [U,V,W]
      have he := prod_primary_alternative_decay D hL (gammaWeight d γ-Real.sqrt η)
      calc
        _ = (((9:ℝ)^d*A^d)*summedCellFourierFactor d (d+1)*cellFourierFactor d)^D.S.M *
            ((∏ v, L^(-(gammaWeight d γ-Real.sqrt η)*(D.g v : ℝ))) *
              ∏ v, L^(-(gammaWeight d γ-Real.sqrt η)*(D.g' v : ℝ))) := by
          simp only [mul_pow]
          ring
        _ = _ := by rw [he]

/-- In particular the complete localized coefficient family has finite total mass. -/
theorem tsum_sourceCoefficient_mass_lt_top {d : ℕ} (hd : 1 ≤ d) (D : SumintDatum d)
    {A L γ η : ℝ} {Dsteps : ℕ} (hA : 1 ≤ A) (hL : 0 < L)
    (hD : D.Admissible A L γ η Dsteps) (r : Mom d) :
    (∑' a : D.S.VIdx → Fin d → ℤ,
      ∑ b ∈ sourceAlternativeLabels D hD a, ENNReal.ofReal (∫ ξ, ‖sourceCoefficient D a b r ξ‖)) < ⊤ :=
  (tsum_sourceCoefficient_mass_le hd D hA hL hD r).trans_lt ENNReal.ofReal_lt_top

end WaveTurbulence.SumintPar
