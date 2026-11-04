/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Sumint.SourceTotalCoefficientMass

/-!
# Absolute lattice mass before oscillatory cancellation

The cutoff insertion has a frequency-independent support count. Fourier
inversion bounds each localized weight by its coefficient mass. Summing
these crude bounds justifies all later spatial and coefficient Fubini
steps without using totalized divergent series.
-/

public section

open MeasureTheory Finset
open scoped ENNReal

namespace WaveTurbulence.Sumint

/-- Fourier inversion bounds the actual localized weight at every lattice input. -/
theorem norm_localizedSourceWeight_le_mass {d : ℕ} (hd : 1 ≤ d) (D : SumintDatum d)
    {A L γ η : ℝ} {Dsteps : ℕ} (hL : 0 < L) (hD : D.Admissible A L γ η Dsteps)
    (a b : D.S.VIdx → Fin d → ℤ) (E : Fin 4 → Mom d) (x : D.S.VIdx → Fin d → ℤ) :
    ‖localizedSourceWeight D L a b E x‖ ≤ ∫ ξ, ‖sourceCoefficient D a b ξ‖ := by
  change ‖∏ v, localizedWeight (a v) (D.wK v) (D.kVec L x E v) *
    localizedWeight (b v) (D.wL v) (D.ℓVec L x E v)‖ ≤ _
  rw [← source_coefficient_expansion hd D hL hD a b x E]
  exact (norm_integral_le_integral_norm _).trans_eq (integral_norm_tensorCharacter_mul _ _)

/-- Each cell's complete absolute lattice mass costs only the fixed support count. -/
theorem tsum_localizedSourceWeight_enorm_le {d : ℕ} (hd : 1 ≤ d) (D : SumintDatum d)
    {A L γ η : ℝ} {Dsteps : ℕ} (hL : 0 < L) (hD : D.Admissible A L γ η Dsteps)
    (a b : D.S.VIdx → Fin d → ℤ) (E : Fin 4 → Mom d) (hE : ∀ j, ‖E j-D.centre j‖ ≤ 1) :
    (∑' x : D.S.VIdx → Fin d → ℤ, ‖localizedSourceWeight D L a b E x‖ₑ) ≤
      ENNReal.ofReal ((8*L+1)^(d*D.S.M)) * ENNReal.ofReal (∫ ξ, ‖sourceCoefficient D a b ξ‖) := by
  classical
  obtain ⟨p,hp⟩ := exists_inputCutoff_insertion D hD a b
  have hz (x : D.S.VIdx → Fin d → ℤ) (hx : x ∉ inputCutoffBox L p) :
      localizedSourceWeight D L a b E x = 0 := by
    change (∏ v, localizedWeight (a v) (D.wK v) (D.kVec L x E v) *
      localizedWeight (b v) (D.wL v) (D.ℓVec L x E v)) = 0
    rw [hp E hE x,inputCutoff_product_eq_zero hL p x hx,Complex.ofReal_zero,zero_mul]
  have hc : ((inputCutoffBox L p).card : ℝ≥0∞) ≤ ENNReal.ofReal ((8*L+1)^(d*D.S.M)) := by
    have hb := card_inputCutoffBox_le hL.le p
    rw [card_vector_index] at hb
    simpa only [ENNReal.ofReal_natCast] using ENNReal.ofReal_le_ofReal hb
  rw [tsum_eq_sum (s := inputCutoffBox L p) (fun x hx => by rw [hz x hx,enorm_zero])]
  calc
    _ ≤ ∑ _x ∈ inputCutoffBox L p, ENNReal.ofReal (∫ ξ, ‖sourceCoefficient D a b ξ‖) := by
      apply Finset.sum_le_sum
      intro x _
      rw [← ofReal_norm]
      exact ENNReal.ofReal_le_ofReal (norm_localizedSourceWeight_le_mass hd D hL hD a b E x)
    _ = ((inputCutoffBox L p).card : ℝ≥0∞)*ENNReal.ofReal (∫ ξ, ‖sourceCoefficient D a b ξ‖) := by simp
    _ ≤ _ := mul_le_mul' hc le_rfl

/-- The complete localized family has finite absolute spatial mass. -/
theorem localized_source_weight_mass_lt_top {d : ℕ} (hd : 1 ≤ d) (D : SumintDatum d)
    {A L γ η : ℝ} {Dsteps : ℕ} (hA : 1 ≤ A) (hL : 0 < L)
    (hD : D.Admissible A L γ η Dsteps) (E : Fin 4 → Mom d)
    (hE : ∀ j, ‖E j-D.centre j‖ ≤ 1) :
    (∑' a : D.S.VIdx → Fin d → ℤ, ∑ b ∈ sourceAlternativeLabels D hD a,
      ∑' x : D.S.VIdx → Fin d → ℤ, ‖localizedSourceWeight D L a b E x‖ₑ) < ⊤ := by
  let K := ENNReal.ofReal ((8*L+1)^(d*D.S.M))
  calc
    _ ≤ ∑' a : D.S.VIdx → Fin d → ℤ, ∑ b ∈ sourceAlternativeLabels D hD a,
        K*ENNReal.ofReal (∫ ξ, ‖sourceCoefficient D a b ξ‖) := by
      apply ENNReal.tsum_le_tsum
      intro a
      apply Finset.sum_le_sum
      intro b _
      exact tsum_localizedSourceWeight_enorm_le hd D hL hD a b E hE
    _ = K*(∑' a : D.S.VIdx → Fin d → ℤ, ∑ b ∈ sourceAlternativeLabels D hD a,
        ENNReal.ofReal (∫ ξ, ‖sourceCoefficient D a b ξ‖)) := by
      simp_rw [← Finset.mul_sum]
      rw [ENNReal.tsum_mul_left]
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top (tsum_sourceCoefficient_mass_lt_top hd D hA hL hD)

end WaveTurbulence.Sumint
