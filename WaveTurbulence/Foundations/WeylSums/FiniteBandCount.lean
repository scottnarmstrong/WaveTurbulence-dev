/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.WeylSums.BandFourierUpper

/-! # A finite positive-kernel energy-band counting inequality -/

public section
open MeasureTheory Set Finset
namespace WaveTurbulence.WeylSums

/-- A finite count in an energy band is bounded by the short-time Fourier
`L¹` norm of any nonnegative weight which majorizes that count. -/
theorem exists_finite_band_count_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ {ι : Type*} (I S : Finset ι) (w E : ι → ℝ) (τ : ℝ),
      0 < τ → S ⊆ I → (∀ i ∈ I, 0 ≤ w i) →
      (∀ i ∈ S, 1 ≤ w i) → (∀ i ∈ S, |E i| ≤ τ) →
      (S.card : ℝ) ≤ C*τ*(∫ t in {t : ℝ | |t| ≤ 1/τ}, ‖finiteEnergySum I w E t‖) := by
  obtain ⟨r,hr,hrsmall,hlower⟩ := exists_intervalFourierKernel_lower_bound
  refine ⟨2/r,by positivity,?_⟩
  intro ι I S w E τ hτ hSI hw hweight hband
  let h := r/τ
  have hh : 0 < h := div_pos hr hτ
  have hlow : (S.card : ℝ)*h^2 ≤ ∑ i ∈ I, w i*‖intervalFourierKernel h (E i)‖^2 := by
    calc
      _ = ∑ _i ∈ S, h^2 := by simp
      _ ≤ ∑ i ∈ S, w i*‖intervalFourierKernel h (E i)‖^2 := by
        apply sum_le_sum
        intro i hi
        have hb := (sq_le_sq₀ hh.le (norm_nonneg _)).mpr (hlower τ hτ (E i) (hband i hi))
        exact hb.trans (le_mul_of_one_le_left (sq_nonneg _) (hweight i hi))
      _ ≤ ∑ i ∈ I, w i*‖intervalFourierKernel h (E i)‖^2 :=
        sum_le_sum_of_subset_of_nonneg hSI (fun i hi hnot => mul_nonneg (hw i hi) (sq_nonneg _))
  have hspan : 2*h ≤ 1/τ := by
    dsimp [h]
    rw [← mul_div_assoc]
    exact (div_le_div_iff_of_pos_right hτ).mpr hrsmall
  have hbig : {t : ℝ | |t| ≤ 1/τ} = Icc (-(1/τ)) (1/τ) := by
    ext t
    change |t| ≤ 1/τ ↔ -(1/τ) ≤ t ∧ t ≤ 1/τ
    exact abs_le
  have hiBig : IntegrableOn (fun t => ‖finiteEnergySum I w E t‖) {t : ℝ | |t| ≤ 1/τ} := by
    rw [hbig]
    exact (continuous_finiteEnergySum I w E).norm.continuousOn.integrableOn_Icc
  have hmass : (∫ t in {t : ℝ | |t| ≤ 2*h}, ‖finiteEnergySum I w E t‖) ≤
      ∫ t in {t : ℝ | |t| ≤ 1/τ}, ‖finiteEnergySum I w E t‖ :=
    setIntegral_mono_set hiBig (Filter.Eventually.of_forall (fun t => norm_nonneg _))
      (Filter.Eventually.of_forall (fun t ht => ht.trans hspan))
  have hupper := (sum_intervalFourierKernel_sq_le I w E hw h hh.le).trans
    (mul_le_mul_of_nonneg_left hmass (by positivity : 0 ≤ 2*h))
  have hc : (S.card : ℝ) ≤
      ((2*h)*(∫ t in {t : ℝ | |t| ≤ 1/τ}, ‖finiteEnergySum I w E t‖))/h^2 :=
    (le_div_iff₀ (sq_pos_of_pos hh)).mpr (hlow.trans hupper)
  have heq : ((2*h)*(∫ t in {t : ℝ | |t| ≤ 1/τ}, ‖finiteEnergySum I w E t‖))/h^2 =
      (2/r)*τ*(∫ t in {t : ℝ | |t| ≤ 1/τ}, ‖finiteEnergySum I w E t‖) := by
    dsimp [h]
    field_simp [hr.ne',hτ.ne']
  exact hc.trans_eq heq

end WaveTurbulence.WeylSums
