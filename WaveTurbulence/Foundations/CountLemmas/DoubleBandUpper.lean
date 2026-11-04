/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.CountLemmas.ComplexBandKernel
public import WaveTurbulence.Foundations.WeylSums.BandFourierUpper
public import Mathlib.MeasureTheory.Integral.Prod

/-! # A positive Fourier kernel for two simultaneous energy bands -/

public section
open MeasureTheory Set Finset
open scoped ComplexConjugate
open WaveTurbulence.WeylSums
namespace WaveTurbulence.CountLemmas

@[expose] noncomputable def doubleEnergySum {ι : Type*} (I : Finset ι)
    (w E F : ι → ℝ) (ts : ℝ × ℝ) : ℂ :=
  ∑ i ∈ I, (w i : ℂ)*e (ts.1*E i+ts.2*F i)

@[fun_prop] theorem continuous_doubleEnergySum {ι : Type*} (I : Finset ι) (w E F : ι → ℝ) :
    Continuous (doubleEnergySum I w E F) := by
  apply continuous_finsetSum
  intro i _
  exact continuous_const.mul (continuous_e.comp (by fun_prop))

/-- A complex-weight interval transform is the first squared kernel in a
positive two-band majorant. -/
theorem norm_kernel_weighted_sum_le {ι : Type*} (I : Finset ι)
    (w E F : ι → ℝ) (h : ℝ) (hh : 0 ≤ h) (s : ℝ) :
    ‖∑ i ∈ I, ((w i*‖intervalFourierKernel h (E i)‖^2 : ℝ) : ℂ)*e (s*F i)‖ ≤
      (2*h)*(∫ t in {t : ℝ | |t| ≤ 2*h}, ‖doubleEnergySum I w E F (t,s)‖) := by
  let v := fun i => (w i : ℂ)*e (s*F i)
  have heq (t : ℝ) : finiteComplexEnergySum I v E t = doubleEnergySum I w E F (t,s) := by
    apply sum_congr rfl
    intro i _
    dsimp only [v]
    rw [mul_assoc,← e_add]
    congr 2
    ring
  have hsum : (∑ i ∈ I, ((w i*‖intervalFourierKernel h (E i)‖^2 : ℝ) : ℂ)*e (s*F i)) =
      ∑ i ∈ I, v i*(intervalFourierKernel h (E i)*conj (intervalFourierKernel h (E i))) := by
    apply sum_congr rfl
    intro i _
    rw [Complex.mul_conj']
    push_cast
    dsimp only [v]
    ring
  rw [hsum,← integral_finiteComplexEnergySum_sub]
  have hb := norm_double_interval_sub_integral_le (finiteComplexEnergySum I v E)
    (continuous_finiteComplexEnergySum I v E) h hh
  simpa only [heq] using hb

/-- The tensor product of the two positive interval kernels is controlled
by the full-square Fourier integral. The statement uses iterated integrals
so it can be applied before the product-measure conversion. -/
theorem sum_double_kernel_sq_le {ι : Type*} (I : Finset ι)
    (w E F : ι → ℝ) (hw : ∀ i ∈ I, 0 ≤ w i) (h : ℝ) (hh : 0 ≤ h) :
    (∑ i ∈ I, w i*‖intervalFourierKernel h (E i)‖^2*‖intervalFourierKernel h (F i)‖^2) ≤
      (2*h)^2*(∫ s in {s : ℝ | |s| ≤ 2*h},
        ∫ t in {t : ℝ | |t| ≤ 2*h}, ‖doubleEnergySum I w E F (t,s)‖) := by
  let v := fun i => w i*‖intervalFourierKernel h (E i)‖^2
  have hb := sum_intervalFourierKernel_sq_le I v F
    (fun i hi => mul_nonneg (hw i hi) (sq_nonneg _)) h hh
  let W := {s : ℝ | |s| ≤ 2*h}
  have hW : W = Icc (-(2*h)) (2*h) := by
    ext s
    change |s| ≤ 2*h ↔ -(2*h) ≤ s ∧ s ≤ 2*h
    exact abs_le
  have hi₁ : IntegrableOn (fun s => ‖finiteEnergySum I v F s‖) W := by
    rw [hW]
    exact (continuous_finiteEnergySum I v F).norm.continuousOn.integrableOn_Icc
  have hi₂ : IntegrableOn (fun s => (2*h)*(∫ t in W, ‖doubleEnergySum I w E F (t,s)‖)) W := by
    have hc : Continuous (fun s => ∫ t in W, ‖doubleEnergySum I w E F (t,s)‖) := by
      rw [hW]
      apply continuous_parametric_integral_of_continuous
      · exact (continuous_doubleEnergySum I w E F).norm.comp (by fun_prop)
      · exact isCompact_Icc
    simpa only [hW] using (hc.const_mul (2*h)).continuousOn.integrableOn_Icc
      (a := -(2*h)) (b := 2*h) (μ := volume)
  have hm : (∫ s in W, ‖finiteEnergySum I v F s‖) ≤
      ∫ s in W, (2*h)*(∫ t in W, ‖doubleEnergySum I w E F (t,s)‖) :=
    integral_mono_ae hi₁ hi₂ (Filter.Eventually.of_forall (fun s => norm_kernel_weighted_sum_le I w E F h hh s))
  have hc := hb.trans (mul_le_mul_of_nonneg_left hm (by positivity : 0 ≤ 2*h))
  rw [integral_const_mul] at hc
  simpa only [v,pow_two,mul_assoc] using hc

end WaveTurbulence.CountLemmas
