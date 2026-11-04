/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.WeylSums.BandFourierKernel

/-! # Upper bounds for the positive energy-band kernel -/

public section
open MeasureTheory Set Finset
open scoped BigOperators ComplexConjugate
namespace WaveTurbulence.WeylSums

/-- A finite weighted Fourier sum, with no lattice-specific assumptions. -/
@[expose] noncomputable def finiteEnergySum {ι : Type*} (I : Finset ι)
    (w E : ι → ℝ) (t : ℝ) : ℂ := ∑ i ∈ I, (w i : ℂ)*e (t*E i)

theorem continuous_finiteEnergySum {ι : Type*} (I : Finset ι) (w E : ι → ℝ) :
    Continuous (finiteEnergySum I w E) := by
  apply continuous_finsetSum
  intro i hi
  exact continuous_const.mul (continuous_e.comp (by fun_prop))

/-- The square of a Fourier interval average has the exact positive
kernel representation as a double time integral. -/
theorem integral_finiteEnergySum_sub {ι : Type*} (I : Finset ι) (w E : ι → ℝ) (h : ℝ) :
    (∫ t in Icc (-h) h, ∫ s in Icc (-h) h, finiteEnergySum I w E (t-s)) =
      ∑ i ∈ I, (w i : ℂ)*(intervalFourierKernel h (E i)*conj (intervalFourierKernel h (E i))) := by
  have hinner (t : ℝ) : (∫ s in Icc (-h) h, finiteEnergySum I w E (t-s)) =
      ∑ i ∈ I, (w i : ℂ)*e (t*E i)*conj (intervalFourierKernel h (E i)) := by
    have hfi (i : ι) (_hi : i ∈ I) :
        IntegrableOn (fun s : ℝ => (w i : ℂ)*e ((t-s)*E i)) (Icc (-h) h) := by
      have hc : Continuous (fun s : ℝ => (w i : ℂ)*e ((t-s)*E i)) := continuous_const.mul (continuous_e.comp (by fun_prop))
      exact hc.continuousOn.integrableOn_Icc
    rw [show (fun s => finiteEnergySum I w E (t-s)) =
      (fun s => ∑ i ∈ I, (w i : ℂ)*e ((t-s)*E i)) from rfl,integral_finsetSum I hfi]
    apply sum_congr rfl
    intro i hi
    have heq (s : ℝ) : (w i : ℂ)*e ((t-s)*E i) = ((w i : ℂ)*e (t*E i))*conj (e (s*E i)) := by
      rw [conj_e,mul_assoc,← e_add]
      congr 2
      ring
    simp_rw [heq]
    rw [integral_const_mul,integral_conj]
    rfl
  simp_rw [hinner]
  have hfo (i : ι) (_hi : i ∈ I) :
      IntegrableOn (fun t : ℝ => (w i : ℂ)*e (t*E i)*conj (intervalFourierKernel h (E i))) (Icc (-h) h) := by
    have hc : Continuous (fun t : ℝ => (w i : ℂ)*e (t*E i)*conj (intervalFourierKernel h (E i))) := (continuous_const.mul (continuous_e.comp (by fun_prop))).mul continuous_const
    exact hc.continuousOn.integrableOn_Icc
  rw [integral_finsetSum I hfo]
  apply sum_congr rfl
  intro i hi
  rw [integral_mul_const,integral_const_mul]
  exact mul_assoc _ _ _

/-- The triangular convolution of two time intervals has height at most
`2h` and support in `[-2h,2h]`. This proof needs no explicit tent transform. -/
theorem norm_double_interval_sub_integral_le (Z : ℝ → ℂ) (hZ : Continuous Z)
    (h : ℝ) (hh : 0 ≤ h) :
    ‖∫ t in Icc (-h) h, ∫ s in Icc (-h) h, Z (t-s)‖ ≤
      (2*h)*(∫ u in {u : ℝ | |u| ≤ 2*h}, ‖Z u‖) := by
  let B := ∫ u in {u : ℝ | |u| ≤ 2*h}, ‖Z u‖
  have hW : {u : ℝ | |u| ≤ 2*h} = Icc (-2*h) (2*h) := by
    ext u
    change |u| ≤ 2*h ↔ -2*h ≤ u ∧ u ≤ 2*h
    simpa only [neg_mul] using (abs_le : |u| ≤ 2*h ↔ -(2*h) ≤ u ∧ u ≤ 2*h)
  have hiB : IntegrableOn (fun u => ‖Z u‖) {u : ℝ | |u| ≤ 2*h} := by
    rw [hW]
    exact hZ.norm.continuousOn.integrableOn_Icc
  have hinner (t : ℝ) (ht : t ∈ Icc (-h) h) : ‖∫ s in Icc (-h) h, Z (t-s)‖ ≤ B := by
    have htrans : (∫ s in Icc (-h) h, ‖Z (t-s)‖) = ∫ u in Icc (t-h) (t+h), ‖Z u‖ := by
      rw [integral_Icc_eq_integral_Ioc,← intervalIntegral.integral_of_le (by linarith : -h ≤ h),
        intervalIntegral.integral_comp_sub_left (fun u : ℝ => ‖Z u‖) t]
      rw [intervalIntegral.integral_of_le (by linarith : t-h ≤ t-(-h)),← integral_Icc_eq_integral_Ioc]
      simp only [sub_neg_eq_add]
    calc
      _ ≤ ∫ s in Icc (-h) h, ‖Z (t-s)‖ := norm_integral_le_integral_norm _
      _ = ∫ u in Icc (t-h) (t+h), ‖Z u‖ := htrans
      _ ≤ B := setIntegral_mono_set hiB (Filter.Eventually.of_forall (fun u => norm_nonneg _))
        (Filter.Eventually.of_forall (fun u hu => by
          change |u| ≤ 2*h
          apply abs_le.mpr
          constructor <;> linarith only [hu.1,hu.2,ht.1,ht.2]))
  have hb : ‖∫ t in Icc (-h) h, ∫ s in Icc (-h) h, Z (t-s)‖ ≤ ∫ _t in Icc (-h) h, B := by
    apply norm_integral_le_of_norm_le (integrableOn_const (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top))
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    exact hinner t ht
  have hconst : (∫ _t in Icc (-h) h, B) = (2*h)*B := by
    rw [integral_const,measureReal_def,Measure.restrict_apply_univ,Real.volume_Icc,
      ENNReal.toReal_ofReal (by linarith : 0 ≤ h-(-h)),smul_eq_mul]
    ring
  exact hb.trans_eq hconst

/-- Positivity turns the double integral into a bound for the weighted
sum of squared interval transforms. -/
theorem sum_intervalFourierKernel_sq_le {ι : Type*} (I : Finset ι) (w E : ι → ℝ)
    (hw : ∀ i ∈ I, 0 ≤ w i) (h : ℝ) (hh : 0 ≤ h) :
    (∑ i ∈ I, w i*‖intervalFourierKernel h (E i)‖^2) ≤
      (2*h)*(∫ u in {u : ℝ | |u| ≤ 2*h}, ‖finiteEnergySum I w E u‖) := by
  have hnonneg : 0 ≤ ∑ i ∈ I, w i*‖intervalFourierKernel h (E i)‖^2 :=
    sum_nonneg (fun i hi => mul_nonneg (hw i hi) (sq_nonneg _))
  have hcast : (∑ i ∈ I, (w i : ℂ)*(intervalFourierKernel h (E i)*conj (intervalFourierKernel h (E i)))) =
      ((∑ i ∈ I, w i*‖intervalFourierKernel h (E i)‖^2 : ℝ) : ℂ) := by
    simp only [Complex.mul_conj',Complex.ofReal_sum,Complex.ofReal_mul,Complex.ofReal_pow]
  have hh' := norm_double_interval_sub_integral_le (finiteEnergySum I w E) (continuous_finiteEnergySum I w E) h hh
  rw [integral_finiteEnergySum_sub,hcast,Complex.norm_real,Real.norm_of_nonneg hnonneg] at hh'
  exact hh'

end WaveTurbulence.WeylSums
