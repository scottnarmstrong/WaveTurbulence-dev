/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.CountLemmas.DoubleBandUpper

/-! # Counting two simultaneous bands by a full-square Fourier integral -/

public section
open MeasureTheory Set Finset
open WaveTurbulence.WeylSums
namespace WaveTurbulence.CountLemmas

/-- A positive tensor kernel majorizes two simultaneous energy bands.
The constant is absolute and the bandwidth is the actual source tolerance. -/
theorem exists_double_band_count_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ {ι : Type*} (I S : Finset ι) (w E F : ι → ℝ) (τ : ℝ),
      0 < τ → S ⊆ I → (∀ i ∈ I, 0 ≤ w i) → (∀ i ∈ S, 1 ≤ w i) →
      (∀ i ∈ S, |E i| ≤ τ ∧ |F i| ≤ τ) →
      (S.card : ℝ) ≤ C*τ^2*(∫ ts : ℝ × ℝ in
        ({t : ℝ | |t| ≤ 1/τ} ×ˢ {t : ℝ | |t| ≤ 1/τ}), ‖doubleEnergySum I w E F ts‖) := by
  obtain ⟨r,hr,hrsmall,hlower⟩ := exists_intervalFourierKernel_lower_bound
  refine ⟨(2/r)^2,by positivity,?_⟩
  intro ι I S w E F τ hτ hSI hw hweight hband
  let h := r/τ
  have hh : 0 < h := div_pos hr hτ
  have hlow : (S.card : ℝ)*h^4 ≤
      ∑ i ∈ I, w i*‖intervalFourierKernel h (E i)‖^2*‖intervalFourierKernel h (F i)‖^2 := by
    calc
      _ = ∑ _i ∈ S, h^2*h^2 := by simp only [sum_const,nsmul_eq_mul]; ring
      _ ≤ ∑ i ∈ S, w i*‖intervalFourierKernel h (E i)‖^2*‖intervalFourierKernel h (F i)‖^2 := by
        apply sum_le_sum
        intro i hi
        have hE := (sq_le_sq₀ hh.le (norm_nonneg _)).mpr (hlower τ hτ (E i) (hband i hi).1)
        have hF := (sq_le_sq₀ hh.le (norm_nonneg _)).mpr (hlower τ hτ (F i) (hband i hi).2)
        exact mul_le_mul (hE.trans (le_mul_of_one_le_left (sq_nonneg _) (hweight i hi)))
          hF (sq_nonneg _) (mul_nonneg (hw i (hSI hi)) (sq_nonneg _))
      _ ≤ _ := sum_le_sum_of_subset_of_nonneg hSI
        (fun i hi _ => mul_nonneg (mul_nonneg (hw i hi) (sq_nonneg _)) (sq_nonneg _))
  let W := {t : ℝ | |t| ≤ 2*h}
  let B := {t : ℝ | |t| ≤ 1/τ}
  let Z := fun ts => ‖doubleEnergySum I w E F ts‖
  have hW : W = Icc (-(2*h)) (2*h) := by ext t; change |t| ≤ 2*h ↔ _; exact abs_le
  have hB : B = Icc (-(1/τ)) (1/τ) := by ext t; change |t| ≤ 1/τ ↔ _; exact abs_le
  have hc : Continuous Z := (continuous_doubleEnergySum I w E F).norm
  have hiW : IntegrableOn (fun ts : ℝ × ℝ => Z ts.swap) (W ×ˢ W)
      ((volume : Measure ℝ).prod volume) := by
    rw [hW]
    exact ContinuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
      (hc.comp continuous_swap).continuousOn
  have heq : (∫ s in W, ∫ t in W, Z (t,s)) = ∫ ts in W ×ˢ W, Z ts := by
    exact (setIntegral_prod (fun ts : ℝ × ℝ => Z ts.swap) hiW).symm.trans
      (setIntegral_prod_swap W W Z)
  have hspan : 2*h ≤ 1/τ := by
    dsimp only [h]
    rw [← mul_div_assoc]
    exact (div_le_div_iff_of_pos_right hτ).mpr hrsmall
  have hiB : IntegrableOn Z (B ×ˢ B) := by
    rw [hB]
    exact ContinuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc) hc.continuousOn
  have hmass : (∫ ts in W ×ˢ W, Z ts) ≤ ∫ ts in B ×ˢ B, Z ts :=
    setIntegral_mono_set hiB (Filter.Eventually.of_forall (fun ts => norm_nonneg _))
      (Filter.Eventually.of_forall (fun ts hts => ⟨hts.1.trans hspan,hts.2.trans hspan⟩))
  have hu := sum_double_kernel_sq_le I w E F hw h hh.le
  rw [heq] at hu
  have hupper := hu.trans (mul_le_mul_of_nonneg_left hmass (sq_nonneg (2*h)))
  have hbound := (le_div_iff₀ (pow_pos hh 4)).mpr (hlow.trans hupper)
  apply hbound.trans_eq
  change ((2*h)^2*(∫ ts in B ×ˢ B, Z ts))/h^4 =
    (2/r)^2*τ^2*(∫ ts in B ×ˢ B, Z ts)
  dsimp only [h]
  field_simp [hr.ne',hτ.ne']

end WaveTurbulence.CountLemmas
