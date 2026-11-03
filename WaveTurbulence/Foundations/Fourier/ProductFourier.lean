/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Fourier.TimeInterpolation
public import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Tactic

/-!
# Fourier factorization for independent vector blocks

TARGET L1007–L1012: products in independent momentum variables have
factorized Fourier transforms and Fourier-L¹ norms.
-/

public section

open MeasureTheory
open scoped ENNReal

namespace WaveTurbulence.Fourier

/-- Fourier transform in `n` blocks of `d` scalar coordinates. -/
@[expose] noncomputable def blockFourier {n d : ℕ}
    (F : (Fin n → Fin d → ℝ) → ℂ) (ξ : Fin n → Fin d → ℝ) : ℂ :=
  ∫ x, Real.fourierChar (-(∑ i, timePairing d (x i) (ξ i))) • F x

/-- Fourier-L¹ norm with the same integrability guard as the scalar time
norm. The guard prevents a failed Bochner integral from giving a junk zero. -/
@[expose] noncomputable def blockFourierL1 {n d : ℕ}
    (F : (Fin n → Fin d → ℝ) → ℂ) : ℝ≥0∞ := by
  classical
  exact if Integrable F then ∫⁻ ξ, ‖blockFourier F ξ‖ₑ else ⊤

private theorem fourierChar_sum {ι : Type*} (s : Finset ι) (a : ι → ℝ) :
    (Real.fourierChar (∑ i ∈ s, a i) : ℂ) = ∏ i ∈ s, (Real.fourierChar (a i) : ℂ) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => simp only [Finset.sum_insert hi, Finset.prod_insert hi,
      AddChar.map_add_eq_mul, Circle.coe_mul, ih]

/-- Fubini factorization of the Fourier transform. -/
theorem blockFourier_prod {n d : ℕ} (f : Fin n → (Fin d → ℝ) → ℂ)
    (ξ : Fin n → Fin d → ℝ) :
    blockFourier (fun x => ∏ i, f i (x i)) ξ = ∏ i, timeFourier (f i) (ξ i) := by
  unfold blockFourier
  simp_rw [Circle.smul_def, ← Finset.sum_neg_distrib, fourierChar_sum,
    smul_eq_mul, ← Finset.prod_mul_distrib]
  change (∫ x : Fin n → Fin d → ℝ, ∏ i,
    (Real.fourierChar (-timePairing d (x i) (ξ i)) : ℂ) * f i (x i)) = _
  exact integral_fin_nat_prod_volume_eq_prod
    (fun i (t : Fin d → ℝ) => (Real.fourierChar (-timePairing d t (ξ i)) : ℂ) * f i t)

private theorem lintegral_fin_prod {E : Type*} [MeasureSpace E] [SigmaFinite (volume : Measure E)] :
    ∀ (n : ℕ) (f : Fin n → E → ℝ≥0∞), (∀ i, Measurable (f i)) →
      (∫⁻ x : Fin n → E, ∏ i, f i (x i) ∂Measure.pi (fun _ => (volume : Measure E))) = ∏ i, ∫⁻ x, f i x := by
  intro n
  induction n with
  | zero => intro f _; simp
  | succ n ih =>
    intro f hf
    rw [← ((measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) =>
      (volume : Measure E)) 0).symm).lintegral_comp_emb
        (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => E) 0).symm.measurableEmbedding]
    simp only [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
      Fin.prod_univ_succ, Fin.insertNth_zero, Equiv.coe_fn_mk, Fin.cons_succ,
      Fin.zero_succAbove, cast_eq, Fin.cons_zero]
    rw [lintegral_prod_mul (f := f 0)
      (g := fun x : Fin n → E => ∏ i, f i.succ (x i))
      (hf 0).aemeasurable
      ((Finset.measurable_prod Finset.univ (fun i _ =>
        (hf i.succ).comp (measurable_pi_apply i))).aemeasurable), ih _ (fun i => hf i.succ)]

/-- Exact Fourier-L¹ factorization for integrable block factors. -/
theorem blockFourierL1_prod {n d : ℕ} (f : Fin n → (Fin d → ℝ) → ℂ)
    (hf : ∀ i, Integrable (f i)) :
    blockFourierL1 (fun x => ∏ i, f i (x i)) = ∏ i, timeFourierNorm 0 (f i) := by
  classical
  have hi : Integrable (fun x : Fin n → Fin d → ℝ => ∏ i, f i (x i)) :=
    Integrable.fintype_prod hf
  rw [blockFourierL1, ite_eq_left hi]
  simp_rw [blockFourier_prod, ← ofReal_norm, norm_prod, ENNReal.ofReal_prod_of_nonneg
    (fun _ _ => norm_nonneg _)]
  simp_rw [ofReal_norm]
  rw [volume_pi, lintegral_fin_prod n _ (fun i => (timeFourier_continuous (hf i)).measurable.enorm)]
  apply Finset.prod_congr rfl
  intro i _
  rw [timeFourierNorm_eq_lintegral (hf i)]
  simp [timeWeight]

end WaveTurbulence.Fourier
