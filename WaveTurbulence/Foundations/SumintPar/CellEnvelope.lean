/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.SumintPar.SummedFourierBounds
import Mathlib.Tactic

/-!
# The cell Fourier envelope of a weight family depending on a parameter

For a family `r ↦ F r` of weights with a common `S^{N,K}` bound, the supremum over `r` of the
Fourier coefficient of each localized cell is dominated by an `r`-free envelope, whose total mass
over all cells obeys the same constant `summedCellFourierFactor` as for a single weight. This is the
input needed to let the `𝒦` weights of `sumint` depend on `r = e - f` (clause (b)).
-/

@[expose] public section
set_option autoImplicit false

open MeasureTheory Finset
open scoped ENNReal FourierTransform

namespace WaveTurbulence.SumintPar

/-- The `r`-free majorant of the `n`-th derivative of every localized cell weight. -/
@[expose] noncomputable def derivMajorant (d K n : ℕ) (B : ℝ) (a : Fin d → ℤ) (x : Mom d) : ℝ :=
  (localizationBox a).indicator (fun x => localizedDerivativeFactor d n * (B / jbr x ^ K)) x

theorem derivMajorant_nonneg (d K n : ℕ) {B : ℝ} (hB : 0 ≤ B) (a : Fin d → ℤ) (x : Mom d) :
    0 ≤ derivMajorant d K n B a x := by
  unfold derivMajorant
  apply Set.indicator_nonneg
  intro y _
  exact mul_nonneg (localizedDerivativeFactor_nonneg d n)
    (div_nonneg hB (pow_nonneg (by linarith [one_le_jbr y]) _))

theorem measurable_derivMajorant (d K n : ℕ) (B : ℝ) (a : Fin d → ℤ) :
    Measurable (derivMajorant d K n B a) := by
  unfold derivMajorant
  apply Measurable.indicator _ (localizationBox_isClosed a).measurableSet
  have : Continuous (fun x : Mom d => jbr x) := by unfold jbr; fun_prop
  fun_prop

theorem norm_iteratedFDeriv_localizedWeight_le_majorant {d N K n : ℕ} (hN : N ≠ 0) (hn : n ≤ N)
    {F : Mom d → ℂ} {B : ℝ} (hB : 0 ≤ B) (hF : SNorm N K F ≤ ENNReal.ofReal B)
    (a : Fin d → ℤ) (x : Mom d) :
    ‖iteratedFDeriv ℝ n (localizedWeight a F) x‖ ≤ derivMajorant d K n B a x := by
  unfold derivMajorant
  by_cases hx : x ∈ localizationBox a
  · rw [Set.indicator_of_mem hx]
    exact norm_iteratedFDeriv_localizedWeight_le hN hn hB hF a x
  · rw [Set.indicator_of_notMem hx]
    have hd : iteratedFDeriv ℝ n (localizedWeight a F) x = 0 := by
      by_contra hne
      exact hx ((tsupport_localizedWeight_subset a F) ((support_iteratedFDeriv_subset n) hne))
    rw [hd, norm_zero]

/-- Summing the majorants over all cells costs only the finite overlap. -/
theorem tsum_ofReal_derivMajorant_le (d K n : ℕ) {B : ℝ} (hB : 0 ≤ B) (x : Mom d) :
    (∑' a : Fin d → ℤ, ENNReal.ofReal (derivMajorant d K n B a x)) ≤
      ENNReal.ofReal (((4 : ℝ) ^ d * localizedDerivativeFactor d n * B) * inverseSpatialWeight K x) := by
  have hh := tsum_enorm_le_localization_overlap (fun a : Fin d → ℤ => derivMajorant d K n B a x) x
    (C := localizedDerivativeFactor d n * (B / jbr x ^ K))
    (fun a ha => by unfold derivMajorant; rw [Set.indicator_of_notMem ha])
    (fun a => by
      rw [Real.norm_of_nonneg (derivMajorant_nonneg d K n hB a x)]
      unfold derivMajorant
      by_cases hx : x ∈ localizationBox a
      · rw [Set.indicator_of_mem hx]
      · rw [Set.indicator_of_notMem hx]
        exact mul_nonneg (localizedDerivativeFactor_nonneg d n)
          (div_nonneg hB (pow_nonneg (by linarith [one_le_jbr x]) _)))
  have he : ∀ a : Fin d → ℤ, ‖derivMajorant d K n B a x‖ₑ = ENNReal.ofReal (derivMajorant d K n B a x) :=
    fun a => by rw [← ofReal_norm, Real.norm_of_nonneg (derivMajorant_nonneg d K n hB a x)]
  simp_rw [he] at hh
  apply hh.trans_eq
  rw [← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 4 ^ d)]
  congr 1
  unfold inverseSpatialWeight
  ring

theorem tsum_lintegral_derivMajorant_le (d K n : ℕ) (hK : d < K) {B : ℝ} (hB : 0 ≤ B) :
    (∑' a : Fin d → ℤ, ∫⁻ x, ENNReal.ofReal (derivMajorant d K n B a x)) ≤
      ENNReal.ofReal (((4 : ℝ) ^ d * localizedDerivativeFactor d n * B) * ∫ x : Mom d, inverseSpatialWeight K x) := by
  rw [← lintegral_tsum (fun a => (measurable_derivMajorant d K n B a).ennreal_ofReal.aemeasurable)]
  calc
    _ ≤ ∫⁻ x : Mom d, ENNReal.ofReal (((4 : ℝ) ^ d * localizedDerivativeFactor d n * B) *
        inverseSpatialWeight K x) := lintegral_mono (tsum_ofReal_derivMajorant_le d K n hB)
    _ = ENNReal.ofReal (∫ x : Mom d, ((4 : ℝ) ^ d * localizedDerivativeFactor d n * B) *
        inverseSpatialWeight K x) := by
      apply (ofReal_integral_eq_lintegral_ofReal
        ((integrable_inverseSpatialWeight hK).const_mul _)
        (ae_of_all _ (fun x => mul_nonneg (mul_nonneg (mul_nonneg (by positivity)
          (localizedDerivativeFactor_nonneg d n)) hB) (inverseSpatialWeight_nonneg K x)))).symm
    _ = _ := by rw [integral_const_mul]

theorem lintegral_fourierEnvelope (d : ℕ) :
    (∫⁻ ξ : Mom d, ENNReal.ofReal ((2 : ℝ) ^ (d + 1 - 1) * (1 + 2 ^ (d + 1)) *
        (1 + ‖ξ‖) ^ (-((d + 1 : ℕ) : ℝ)))) =
      ENNReal.ofReal (Fourier.fourierL1Constant (Mom d) (d + 1)) := by
  have henv : Integrable (fun ξ : Mom d => (1 + ‖ξ‖) ^ (-((d + 1 : ℕ) : ℝ))) :=
    integrable_one_add_norm (by simp [Mom])
  have hnn : ∀ ξ : Mom d, 0 ≤ (2 : ℝ) ^ (d + 1 - 1) * (1 + 2 ^ (d + 1)) *
      (1 + ‖ξ‖) ^ (-((d + 1 : ℕ) : ℝ)) := fun ξ => by positivity
  rw [← ofReal_integral_eq_lintegral_ofReal ((henv.const_mul _)) (ae_of_all _ hnn)]
  congr 1
  rw [integral_const_mul]
  unfold Fourier.fourierL1Constant
  ring

/-- The summed cell constant only improves with the decay order. -/
theorem summedCellFourierFactor_mono {d K : ℕ} (hK : d + 1 ≤ K) :
    summedCellFourierFactor d K ≤ summedCellFourierFactor d (d + 1) := by
  unfold summedCellFourierFactor
  apply mul_le_mul_of_nonneg_left _ (Fourier.fourierL1Constant_nonneg _)
  apply Finset.sum_le_sum
  intro j _
  apply mul_le_mul_of_nonneg_left _ (mul_nonneg (by positivity) (localizedDerivativeFactor_nonneg d j))
  apply integral_mono (integrable_inverseSpatialWeight (by omega)) (integrable_inverseSpatialWeight (by omega))
  intro x
  unfold inverseSpatialWeight
  exact one_div_le_one_div_of_le (pow_pos (by linarith [one_le_jbr x]) _)
    (pow_le_pow_right₀ (one_le_jbr x) hK)

/-- The single-weight summed Fourier mass with the decay-free base constant. -/
theorem tsum_localizedWeight_fourier_mass_le_base {d N K : ℕ} (hN : N ≠ 0) (hdN : d + 1 ≤ N)
    (hK : d < K) {F : Mom d → ℂ} {B : ℝ} (hB : 0 ≤ B)
    (hF : SNorm N K F ≤ ENNReal.ofReal B) :
    (∑' a : Fin d → ℤ, ENNReal.ofReal (∫ ξ, ‖𝓕 (localizedWeight a F) ξ‖)) ≤
      ENNReal.ofReal (summedCellFourierFactor d (d + 1) * B) :=
  (tsum_localizedWeight_fourier_mass_le hN hdN hK hB hF).trans
    (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (summedCellFourierFactor_mono hK) hB))

theorem integrable_derivMajorant (d K n : ℕ) {B : ℝ} (hB : 0 ≤ B) (a : Fin d → ℤ) :
    Integrable (derivMajorant d K n B a) := by
  have hint : IntegrableOn (fun _ : Mom d => localizedDerivativeFactor d n * B) (localizationBox a) := by
    apply integrableOn_const
    · rw [volume_localizationBox]
      exact ENNReal.one_ne_top
    · exact enorm_ne_top
  have hind := hint.integrable_indicator (localizationBox_isClosed a).measurableSet
  refine hind.mono' (measurable_derivMajorant d K n B a).aestronglyMeasurable (ae_of_all _ fun x => ?_)
  rw [Real.norm_of_nonneg (derivMajorant_nonneg d K n hB a x)]
  unfold derivMajorant
  apply Set.indicator_le_indicator
  apply mul_le_mul_of_nonneg_left _ (localizedDerivativeFactor_nonneg d n)
  exact div_le_self hB (one_le_pow₀ (one_le_jbr x))

/-- The polynomial Fourier-decay factor of a `(d+1)`-fold integrable derivative bound. -/
@[expose] noncomputable def fourierDecayFactor (d : ℕ) (ξ : Mom d) : ℝ :=
  (2 : ℝ) ^ (d + 1 - 1) * (1 + 2 ^ (d + 1)) * (1 + ‖ξ‖) ^ (-((d + 1 : ℕ) : ℝ))

theorem fourierDecayFactor_nonneg (d : ℕ) (ξ : Mom d) : 0 ≤ fourierDecayFactor d ξ := by
  unfold fourierDecayFactor; positivity

theorem continuous_fourierDecayFactor (d : ℕ) : Continuous (fourierDecayFactor (d := d) ·) := by
  unfold fourierDecayFactor
  exact continuous_const.mul ((continuous_const.add continuous_norm).rpow_const
    (fun ξ => Or.inl (ne_of_gt (by show (0:ℝ) < 1 + ‖ξ‖; have := norm_nonneg ξ; linarith))))

theorem integrable_fourierDecayFactor (d : ℕ) : Integrable (fourierDecayFactor (d := d) ·) := by
  have henv : Integrable (fun ξ : Mom d => (1 + ‖ξ‖) ^ (-((d + 1 : ℕ) : ℝ))) :=
    integrable_one_add_norm (by simp [Mom])
  exact henv.const_mul _

theorem integral_fourierDecayFactor (d : ℕ) :
    ∫ ξ : Mom d, fourierDecayFactor d ξ = Fourier.fourierL1Constant (Mom d) (d + 1) := by
  unfold fourierDecayFactor Fourier.fourierL1Constant
  rw [integral_const_mul]

/-- The `r`-free Fourier envelope of one localization cell (a real function of the frequency). -/
@[expose] noncomputable def cellEnv (d K : ℕ) (B : ℝ) (a : Fin d → ℤ) (ξ : Mom d) : ℝ :=
  fourierDecayFactor d ξ * ∑ j ∈ range (d + 2), ∫ x, derivMajorant d K j B a x

theorem cellEnv_nonneg (d K : ℕ) {B : ℝ} (hB : 0 ≤ B) (a : Fin d → ℤ) (ξ : Mom d) :
    0 ≤ cellEnv d K B a ξ :=
  mul_nonneg (fourierDecayFactor_nonneg d ξ)
    (Finset.sum_nonneg fun j _ => integral_nonneg (derivMajorant_nonneg d K j hB a))

theorem continuous_cellEnv (d K : ℕ) (B : ℝ) (a : Fin d → ℤ) : Continuous (cellEnv d K B a) :=
  (continuous_fourierDecayFactor d).mul continuous_const

theorem integrable_cellEnv (d K : ℕ) (B : ℝ) (a : Fin d → ℤ) : Integrable (cellEnv d K B a) :=
  (integrable_fourierDecayFactor d).mul_const _

/-- The mass of the cell envelope. -/
@[expose] noncomputable def cellOmega (d K : ℕ) (B : ℝ) (a : Fin d → ℤ) : ℝ :=
  Fourier.fourierL1Constant (Mom d) (d + 1) * ∑ j ∈ range (d + 2), ∫ x, derivMajorant d K j B a x

theorem integral_cellEnv (d K : ℕ) (B : ℝ) (a : Fin d → ℤ) :
    ∫ ξ, cellEnv d K B a ξ = cellOmega d K B a := by
  unfold cellEnv cellOmega
  rw [integral_mul_const, integral_fourierDecayFactor]

/-- **Pointwise `r`-uniform Fourier bound** of every localized cell weight of the family. -/
theorem norm_fourier_localizedWeight_le_cellEnv {d N K : ℕ} (hN : N ≠ 0) (hdN : d + 1 ≤ N)
    {F : Mom d → ℂ} {B : ℝ} (hB : 0 ≤ B) (hF : SNorm N K F ≤ ENNReal.ofReal B)
    (a : Fin d → ℤ) (ξ : Mom d) :
    ‖𝓕 (localizedWeight a F) ξ‖ ≤ cellEnv d K B a ξ := by
  have hf := contDiff_of_SNorm_le hN hF
  have hc : ContDiff ℝ (d + 1) (localizedWeight a F) :=
    (localizedWeight_contDiff a hf).of_le (by exact_mod_cast hdN)
  have hi (j : ℕ) (hj : j ≤ d + 1) := integrable_iteratedFDeriv_localizedWeight (hj.trans hdN) hf a
  have hp := Fourier.fourier_polynomial_weight_le hc hi ξ
  have hp0 : 0 < (1 + ‖ξ‖) ^ (d + 1) := pow_pos (by positivity) _
  have hnorm : ‖𝓕 (localizedWeight a F) ξ‖ ≤ fourierDecayFactor d ξ *
        Fourier.derivativeL1Sum (d + 1) (localizedWeight a F) := by
    unfold fourierDecayFactor
    rw [Real.rpow_neg (by positivity), Real.rpow_natCast]
    have : ‖𝓕 (localizedWeight a F) ξ‖ ≤ ((2 : ℝ) ^ (d + 1 - 1) * (1 + 2 ^ (d + 1)) *
        Fourier.derivativeL1Sum (d + 1) (localizedWeight a F)) / (1 + ‖ξ‖) ^ (d + 1) :=
      (le_div_iff₀ hp0).2 (by simpa only [mul_comm] using hp)
    calc _ ≤ _ := this
      _ = _ := by field_simp
  refine hnorm.trans (mul_le_mul_of_nonneg_left ?_ (fourierDecayFactor_nonneg d ξ))
  unfold Fourier.derivativeL1Sum
  apply Finset.sum_le_sum
  intro j hj
  have hjd : j ≤ d + 1 := by have := Finset.mem_range.mp hj; omega
  apply integral_mono (hi j hjd).norm (integrable_derivMajorant d K j hB a)
  intro x
  exact norm_iteratedFDeriv_localizedWeight_le_majorant hN (hjd.trans hdN) hB hF a x

/-- The total mass of the `r`-free cell envelopes. -/
theorem tsum_ofReal_cellOmega_le {d K : ℕ} (hK : d < K) {B : ℝ} (hB : 0 ≤ B) :
    (∑' a : Fin d → ℤ, ENNReal.ofReal (cellOmega d K B a)) ≤
      ENNReal.ofReal (summedCellFourierFactor d K * B) := by
  have ht : 0 ≤ ∫ x : Mom d, inverseSpatialWeight K x :=
    integral_nonneg (inverseSpatialWeight_nonneg K)
  have hom (a : Fin d → ℤ) : ENNReal.ofReal (cellOmega d K B a) =
      ENNReal.ofReal (Fourier.fourierL1Constant (Mom d) (d + 1)) *
        ∑ j ∈ range (d + 2), ∫⁻ x, ENNReal.ofReal (derivMajorant d K j B a x) := by
    unfold cellOmega
    rw [ENNReal.ofReal_mul (Fourier.fourierL1Constant_nonneg _),
      ENNReal.ofReal_sum_of_nonneg (fun j _ => integral_nonneg (derivMajorant_nonneg d K j hB a))]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    exact ofReal_integral_eq_lintegral_ofReal (integrable_derivMajorant d K j hB a)
      (ae_of_all _ (derivMajorant_nonneg d K j hB a))
  simp_rw [hom]
  calc
    _ = ENNReal.ofReal (Fourier.fourierL1Constant (Mom d) (d + 1)) *
        ∑ j ∈ range (d + 2), ∑' a : Fin d → ℤ, ∫⁻ x, ENNReal.ofReal (derivMajorant d K j B a x) := by
      rw [ENNReal.tsum_mul_left, tsum_finsetSum_ennreal]
    _ ≤ ENNReal.ofReal (Fourier.fourierL1Constant (Mom d) (d + 1)) *
        ∑ j ∈ range (d + 2), ENNReal.ofReal (((4 : ℝ) ^ d * localizedDerivativeFactor d j * B) *
          ∫ x : Mom d, inverseSpatialWeight K x) := by
      apply mul_le_mul_right
      apply Finset.sum_le_sum
      intro j hj
      exact tsum_lintegral_derivMajorant_le d K j hK hB
    _ = _ := by
      unfold summedCellFourierFactor
      rw [mul_assoc (Fourier.fourierL1Constant (Mom d) (d + 1))]
      rw [ENNReal.ofReal_mul (Fourier.fourierL1Constant_nonneg _)]
      congr 1
      rw [Finset.sum_mul, ENNReal.ofReal_sum_of_nonneg]
      · apply Finset.sum_congr rfl
        intro j _
        congr 1
        ring
      · intro j _
        exact mul_nonneg (mul_nonneg (mul_nonneg (by positivity)
          (localizedDerivativeFactor_nonneg d j)) ht) hB

theorem tsum_ofReal_cellOmega_le_base {d K : ℕ} (hK : d < K) {B : ℝ} (hB : 0 ≤ B) :
    (∑' a : Fin d → ℤ, ENNReal.ofReal (cellOmega d K B a)) ≤
      ENNReal.ofReal (summedCellFourierFactor d (d + 1) * B) :=
  (tsum_ofReal_cellOmega_le hK hB).trans
    (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (summedCellFourierFactor_mono hK) hB))

end WaveTurbulence.SumintPar
