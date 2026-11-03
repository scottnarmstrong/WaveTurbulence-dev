/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.WeylSums.BandFourierKernel

/-! # Complex coefficients in the interval Fourier kernel -/

public section
open MeasureTheory Set Finset
open scoped BigOperators ComplexConjugate
namespace WaveTurbulence.CountLemmas
open WaveTurbulence.WeylSums

/-- A finite weighted Fourier sum, with no lattice-specific assumptions. -/
@[expose] noncomputable def finiteComplexEnergySum {ι : Type*} (I : Finset ι)
    (w : ι → ℂ) (E : ι → ℝ) (t : ℝ) : ℂ := ∑ i ∈ I, w i*e (t*E i)

theorem continuous_finiteComplexEnergySum {ι : Type*} (I : Finset ι) (w : ι → ℂ) (E : ι → ℝ) :
    Continuous (finiteComplexEnergySum I w E) := by
  apply continuous_finsetSum
  intro i hi
  exact continuous_const.mul (continuous_e.comp (by fun_prop))

/-- The square of a Fourier interval average has the exact positive
kernel representation as a double time integral. -/
theorem integral_finiteComplexEnergySum_sub {ι : Type*} (I : Finset ι) (w : ι → ℂ) (E : ι → ℝ) (h : ℝ) :
    (∫ t in Icc (-h) h, ∫ s in Icc (-h) h, finiteComplexEnergySum I w E (t-s)) =
      ∑ i ∈ I, w i*(intervalFourierKernel h (E i)*conj (intervalFourierKernel h (E i))) := by
  have hinner (t : ℝ) : (∫ s in Icc (-h) h, finiteComplexEnergySum I w E (t-s)) =
      ∑ i ∈ I, w i*e (t*E i)*conj (intervalFourierKernel h (E i)) := by
    have hfi (i : ι) (_hi : i ∈ I) :
        IntegrableOn (fun s : ℝ => w i*e ((t-s)*E i)) (Icc (-h) h) := by
      have hc : Continuous (fun s : ℝ => w i*e ((t-s)*E i)) := continuous_const.mul (continuous_e.comp (by fun_prop))
      exact hc.continuousOn.integrableOn_Icc
    rw [show (fun s => finiteComplexEnergySum I w E (t-s)) =
      (fun s => ∑ i ∈ I, w i*e ((t-s)*E i)) from rfl,integral_finsetSum I hfi]
    apply sum_congr rfl
    intro i hi
    have heq (s : ℝ) : w i*e ((t-s)*E i) = (w i*e (t*E i))*conj (e (s*E i)) := by
      rw [conj_e,mul_assoc,← e_add]
      congr 2
      ring
    simp_rw [heq]
    rw [integral_const_mul,integral_conj]
    rfl
  simp_rw [hinner]
  have hfo (i : ι) (_hi : i ∈ I) :
      IntegrableOn (fun t : ℝ => w i*e (t*E i)*conj (intervalFourierKernel h (E i))) (Icc (-h) h) := by
    have hc : Continuous (fun t : ℝ => w i*e (t*E i)*conj (intervalFourierKernel h (E i))) := (continuous_const.mul (continuous_e.comp (by fun_prop))).mul continuous_const
    exact hc.continuousOn.integrableOn_Icc
  rw [integral_finsetSum I hfo]
  apply sum_congr rfl
  intro i hi
  rw [integral_mul_const,integral_const_mul]
  exact mul_assoc _ _ _


end WaveTurbulence.CountLemmas
