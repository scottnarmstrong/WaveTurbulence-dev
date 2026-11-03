/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.WeylSums.SobolevMultiplication
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
public import Mathlib.MeasureTheory.Group.Integral

/-!
# Cutoff dilation and translation in the finite-order Fourier bound

For width at least one, derivative factors from dilation are at most one.
The only growth of the Sobolev `L¹` quantity is the volume factor `width^(Fintype.card ι)`.
-/

public section
open MeasureTheory Finset
namespace WaveTurbulence.WeylSums

/-- The scaled and translated joint cutoff. -/
@[expose] noncomputable def scaledTranslatedCutoff {ι : Type*} [Fintype ι]
    (κ : EuclideanSpace ℝ ι → ℂ) (width : ℝ)
    (a x : EuclideanSpace ℝ ι) : ℂ := κ (width⁻¹ • (x-a))

theorem scaledTranslatedCutoff_contDiff {ι : Type*} [Fintype ι] {N : ℕ}
    {κ : EuclideanSpace ℝ ι → ℂ} (hs : ContDiff ℝ N κ)
    (width : ℝ) (a : EuclideanSpace ℝ ι) :
    ContDiff ℝ N (scaledTranslatedCutoff κ width a) := by
  unfold scaledTranslatedCutoff
  fun_prop

theorem scaledTranslatedCutoff_hasCompactSupport {ι : Type*} [Fintype ι]
    {κ : EuclideanSpace ℝ ι → ℂ} (hc : HasCompactSupport κ)
    {width : ℝ} (hw : width ≠ 0) (a : EuclideanSpace ℝ ι) :
    HasCompactSupport (scaledTranslatedCutoff κ width a) := by
  let H : EuclideanSpace ℝ ι ≃ₜ EuclideanSpace ℝ ι :=
    (Homeomorph.addRight (-a)).trans (Homeomorph.smul (Units.mk0 width⁻¹ (inv_ne_zero hw)))
  convert hc.comp_homeomorph H using 1
  funext x
  change κ (width⁻¹ • (x-a)) = κ ((Units.mk0 width⁻¹ (inv_ne_zero hw)) • (x+(-a)))
  simp only [Units.smul_def, Units.val_mk0, sub_eq_add_neg]

/-- Dilation does not enlarge pointwise derivative bounds when `width≥1`. -/
theorem norm_scaledTranslatedCutoff_derivative_le {ι : Type*} [Fintype ι] {N j : ℕ}
    {κ : EuclideanSpace ℝ ι → ℂ} (hs : ContDiff ℝ N κ)
    {width : ℝ} (hw : 1 ≤ width) (a x : EuclideanSpace ℝ ι) (hj : j ≤ N) :
    ‖iteratedFDeriv ℝ j (scaledTranslatedCutoff κ width a) x‖ ≤
      ‖iteratedFDeriv ℝ j κ (width⁻¹ • (x-a))‖ := by
  have hwp : 0 < width := by linarith only [hw]
  have hwi : 0 ≤ width⁻¹ := inv_nonneg.mpr hwp.le
  have hwi1 : width⁻¹ ≤ 1 := by
    simpa only [one_div, inv_one] using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hw
  have hderiv : iteratedFDeriv ℝ j (scaledTranslatedCutoff κ width a) x =
      width⁻¹^j • iteratedFDeriv ℝ j κ (width⁻¹ • (x-a)) := by
    unfold scaledTranslatedCutoff
    rw [iteratedFDeriv_comp_sub (𝕜 := ℝ) (f := fun z => κ (width⁻¹ • z)) j a x]
    exact congrFun (iteratedFDeriv_comp_const_smul width⁻¹ (hs.of_le (by exact_mod_cast hj))) (x-a)
  rw [hderiv, norm_smul, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hwi j)]
  exact mul_le_of_le_one_left (norm_nonneg _) (pow_le_one₀ hwi hwi1)

/-- Exact volume growth, with no derivative loss, at widths at least one. -/
theorem derivativeL1Sum_scaledTranslated_le {ι : Type*} [Fintype ι] {N : ℕ}
    {κ : EuclideanSpace ℝ ι → ℂ} (hc : HasCompactSupport κ) (hs : ContDiff ℝ N κ)
    {width : ℝ} (hw : 1 ≤ width) (a : EuclideanSpace ℝ ι) :
    Fourier.derivativeL1Sum N (scaledTranslatedCutoff κ width a) ≤
      width^(Fintype.card ι) * Fourier.derivativeL1Sum N κ := by
  have hwp : 0 < width := by linarith only [hw]
  unfold Fourier.derivativeL1Sum
  rw [mul_sum]
  apply sum_le_sum
  intro j hjmem
  have hj : j ≤ N := Nat.le_of_lt_succ (mem_range.mp hjmem)
  have hi : Integrable (iteratedFDeriv ℝ j κ) :=
    (hs.continuous_iteratedFDeriv (by exact_mod_cast hj)).integrable_of_hasCompactSupport (hc.iteratedFDeriv j)
  have hcomp : Integrable (fun x => ‖iteratedFDeriv ℝ j κ (width⁻¹ • (x-a))‖) :=
    (hi.norm.comp_smul (inv_ne_zero hwp.ne')).comp_sub_right a
  calc
    _ ≤ ∫ x, ‖iteratedFDeriv ℝ j κ (width⁻¹ • (x-a))‖ :=
      integral_mono_of_nonneg (Filter.Eventually.of_forall (fun x => norm_nonneg _)) hcomp
        (Filter.Eventually.of_forall (fun x => norm_scaledTranslatedCutoff_derivative_le hs hw a x hj))
    _ = width^(Fintype.card ι) * ∫ x, ‖iteratedFDeriv ℝ j κ x‖ := by
      rw [integral_sub_right_eq_self (fun x : EuclideanSpace ℝ ι => ‖iteratedFDeriv ℝ j κ (width⁻¹ • x)‖) a,
        Measure.integral_comp_inv_smul_of_nonneg volume (fun x => ‖iteratedFDeriv ℝ j κ x‖) hwp.le]
      simp only [finrank_euclideanSpace, smul_eq_mul]

end WaveTurbulence.WeylSums
