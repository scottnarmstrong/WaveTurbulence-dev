/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Cut2A.SpatialMeasureDefs
public import WaveTurbulence.Foundations.Cut2A.Chirp
public import WaveTurbulence.Frozen.Defs.Mom
public import Mathlib.Analysis.Fourier.FourierTransformDeriv

/-! # STAGE1W-O4: smoothness of a Fourier-presented weight (row O4c)

For a spatial measure `M` on `Mom d` whose `J`-th moment `∫ (1 + ‖ξ‖)^J ‖amp‖` is at most `c`, the value
`M.value` is `C^J` and its `n`-th Fréchet derivative is bounded by `(2π)^n c` for `n ≤ J`
(`contDiff_value`, `norm_iteratedFDeriv_value_le`).

Proof: the value is a Mathlib vector Fourier integral on `Mom d × ℂ` against the finite measure
`ν = (ξ, amp/‖amp‖)_* (‖amp‖ μ)` (`value_eq_fourierIntegral`), whose moments are those of `M`. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open MeasureTheory Real
open scoped ENNReal NNReal

namespace WaveTurbulence.Flower.Stage1WNoVine

variable {d : ℕ} {α : Type*} [MeasurableSpace α]

/-- The unit direction of a complex number (`0` at `0`). -/
def unitDir (z : ℂ) : ℂ := if z = 0 then 0 else z / (‖z‖ : ℂ)

theorem norm_unitDir_le (z : ℂ) : ‖unitDir z‖ ≤ 1 := by
  unfold unitDir
  split_ifs with h
  · simp
  · rw [norm_div, Complex.norm_real, norm_norm, div_self (norm_ne_zero_iff.mpr h)]

theorem norm_smul_unitDir (z : ℂ) : (‖z‖₊ : ℝ) • unitDir z = z := by
  unfold unitDir
  split_ifs with h
  · simp [h]
  · rw [Complex.real_smul, coe_nnnorm]
    field_simp [norm_ne_zero_iff.mpr h]

theorem measurable_unitDir : Measurable unitDir := by
  unfold unitDir
  refine Measurable.ite (measurableSet_singleton 0) measurable_const ?_
  exact measurable_id.div (Complex.measurable_ofReal.comp measurable_norm)

/-- The linear pairing on `Mom d × ℂ` reading the frequency coordinate. -/
def jetPairing (d : ℕ) : (Mom d × ℂ) →L[ℝ] Mom d →L[ℝ] ℝ :=
  -((innerSL ℝ (E := Mom d)).comp (ContinuousLinearMap.fst ℝ (Mom d) ℂ))

theorem norm_jetPairing_le (d : ℕ) : ‖jetPairing d‖ ≤ 1 := by
  unfold jetPairing
  rw [ContinuousLinearMap.opNorm_neg]
  refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
  have h1 : ‖innerSL ℝ (E := Mom d)‖ ≤ 1 := norm_innerSL_le ℝ
  have h2 : ‖ContinuousLinearMap.fst ℝ (Mom d) ℂ‖ ≤ 1 := ContinuousLinearMap.norm_fst_le ℝ (Mom d) ℂ
  calc ‖innerSL ℝ (E := Mom d)‖ * ‖ContinuousLinearMap.fst ℝ (Mom d) ℂ‖ ≤ 1 * 1 :=
        mul_le_mul h1 h2 (norm_nonneg _) zero_le_one
    _ = 1 := one_mul 1

theorem jetPairing_apply (v : Mom d × ℂ) (x : Mom d) : jetPairing d v x = -inner ℝ v.1 x := rfl

section Measure

variable (M : Cut2A.SpatialMeasure (Mom d) α)

/-- A strongly measurable version of the amplitude. -/
def ampMk : α → ℂ := M.amplitude_integrable.aestronglyMeasurable.mk M.amplitude

theorem stronglyMeasurable_ampMk : StronglyMeasurable (ampMk M) :=
  M.amplitude_integrable.aestronglyMeasurable.stronglyMeasurable_mk

theorem ampMk_ae : M.amplitude =ᵐ[M.μ] ampMk M :=
  M.amplitude_integrable.aestronglyMeasurable.ae_eq_mk

/-- The frequency/direction map. -/
def jetMap : α → Mom d × ℂ := fun a => (M.frequency a, unitDir (ampMk M a))

theorem measurable_jetMap : Measurable (jetMap M) :=
  M.frequency_measurable.prodMk (measurable_unitDir.comp (stronglyMeasurable_ampMk M).measurable)

/-- The amplitude density. -/
def jetDensity : α → ℝ≥0 := fun a => ‖ampMk M a‖₊

theorem measurable_jetDensity : Measurable (jetDensity M) :=
  (stronglyMeasurable_ampMk M).measurable.nnnorm

/-- The finite measure on `Mom d × ℂ` presenting `M.value`. -/
def jetMeasure : Measure (Mom d × ℂ) :=
  Measure.map (jetMap M) (M.μ.withDensity fun a => (jetDensity M a : ℝ≥0∞))

theorem value_eq_fourierIntegral (x : Mom d) :
    M.value x = VectorFourier.fourierIntegral Real.fourierChar (jetMeasure M)
      (jetPairing d).toLinearMap₁₂ (fun v => v.2) x := by
  unfold VectorFourier.fourierIntegral jetMeasure
  have e1 : (fun v : Mom d × ℂ => Real.fourierChar (-((jetPairing d).toLinearMap₁₂ v x)) • v.2) =
      fun v => (Real.fourierChar (inner ℝ v.1 x) : ℂ) * v.2 := by
    funext v
    have h : (jetPairing d).toLinearMap₁₂ v x = -inner ℝ v.1 x := rfl
    rw [Circle.smul_def, smul_eq_mul, h, neg_neg]
  rw [e1]
  have hcont : Continuous (fun v : Mom d × ℂ => (Real.fourierChar (inner ℝ v.1 x) : ℂ) * v.2) :=
    (Cut2A.character_smooth.continuous.comp (continuous_fst.inner continuous_const)).mul continuous_snd
  rw [integral_map (measurable_jetMap M).aemeasurable hcont.aestronglyMeasurable,
    integral_withDensity_eq_integral_smul (measurable_jetDensity M)]
  unfold Cut2A.SpatialMeasure.value
  refine integral_congr_ae ((ampMk_ae M).mono fun a ha => ?_)
  show M.amplitude a * (Real.fourierChar (inner ℝ (M.frequency a) x) : ℂ) =
    ((‖ampMk M a‖₊ : ℝ≥0) : ℝ) • ((Real.fourierChar (inner ℝ (M.frequency a) x) : ℂ) * unitDir (ampMk M a))
  rw [ha]
  conv_lhs => rw [← norm_smul_unitDir (ampMk M a)]
  rw [Complex.real_smul, Complex.real_smul]
  ring

end Measure

section Moments

variable (M : Cut2A.SpatialMeasure (Mom d) α) {J : ℕ} {c : ℝ}

theorem norm_jetMap_le (a : α) : ‖jetMap M a‖ ≤ 1 + ‖M.frequency a‖ := by
  unfold jetMap
  rw [Prod.norm_def]
  have h0 := norm_nonneg (M.frequency a)
  exact max_le (by linarith) ((norm_unitDir_le _).trans (by linarith))

theorem lintegral_moment_eq :
    ∫⁻ a, ‖(1 + ‖M.frequency a‖) ^ J * ‖ampMk M a‖‖ₑ ∂M.μ =
      ∫⁻ a, ENNReal.ofReal ((1 + ‖M.frequency a‖) ^ J) * ‖M.amplitude a‖ₑ ∂M.μ := by
  refine lintegral_congr_ae ((ampMk_ae M).mono fun a ha => ?_)
  have h0 : 0 ≤ (1 + ‖M.frequency a‖) ^ J := by positivity
  dsimp only
  rw [Real.enorm_eq_ofReal (mul_nonneg h0 (norm_nonneg _)), ENNReal.ofReal_mul h0, ofReal_norm_eq_enorm, ha]

theorem integrable_moment
    (hM : ∫⁻ a, ENNReal.ofReal ((1 + ‖M.frequency a‖) ^ J) * ‖M.amplitude a‖ₑ ∂M.μ ≤ ENNReal.ofReal c) :
    Integrable (fun a => (1 + ‖M.frequency a‖) ^ J * ‖ampMk M a‖) M.μ := by
  refine ⟨?_, ?_⟩
  · exact ((((continuous_const.add continuous_norm).pow J).measurable.comp M.frequency_measurable).mul
      (stronglyMeasurable_ampMk M).measurable.norm).aestronglyMeasurable
  · unfold HasFiniteIntegral
    rw [lintegral_moment_eq]
    exact lt_of_le_of_lt hM ENNReal.ofReal_lt_top

theorem jetDensity_smul_le {n : ℕ} (hn : n ≤ J) (a : α) :
    ‖(jetDensity M a : ℝ) * (‖jetMap M a‖ ^ n * ‖(jetMap M a).2‖)‖ ≤
      (1 + ‖M.frequency a‖) ^ J * ‖ampMk M a‖ := by
  have h1 : ‖jetMap M a‖ ^ n ≤ (1 + ‖M.frequency a‖) ^ J :=
    (pow_le_pow_left₀ (norm_nonneg _) (norm_jetMap_le M a) n).trans
      (pow_le_pow_right₀ (by linarith [norm_nonneg (M.frequency a)]) hn)
  have h2 : ‖(jetMap M a).2‖ ≤ 1 := norm_unitDir_le _
  have h3 : (jetDensity M a : ℝ) = ‖ampMk M a‖ := rfl
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), h3]
  calc ‖ampMk M a‖ * (‖jetMap M a‖ ^ n * ‖(jetMap M a).2‖)
      ≤ ‖ampMk M a‖ * ((1 + ‖M.frequency a‖) ^ J * 1) := by
        gcongr
    _ = _ := by ring

theorem measurable_jetIntegrand (n : ℕ) :
    Measurable (fun a => (jetDensity M a : ℝ) * (‖jetMap M a‖ ^ n * ‖(jetMap M a).2‖)) :=
  (measurable_jetDensity M).coe_nnreal_real.mul
    ((((continuous_norm.pow n).mul (continuous_norm.comp continuous_snd)).measurable).comp (measurable_jetMap M))

theorem integrable_jetMoment
    (hM : ∫⁻ a, ENNReal.ofReal ((1 + ‖M.frequency a‖) ^ J) * ‖M.amplitude a‖ₑ ∂M.μ ≤ ENNReal.ofReal c)
    (n : ℕ) (hn : n ≤ J) :
    Integrable (fun v : Mom d × ℂ => ‖v‖ ^ n * ‖v.2‖) (jetMeasure M) := by
  have hc : Continuous (fun v : Mom d × ℂ => ‖v‖ ^ n * ‖v.2‖) :=
    (continuous_norm.pow n).mul (continuous_norm.comp continuous_snd)
  unfold jetMeasure
  rw [integrable_map_measure hc.aestronglyMeasurable (measurable_jetMap M).aemeasurable,
    integrable_withDensity_iff_integrable_smul (measurable_jetDensity M)]
  refine (integrable_moment M hM).mono' ?_ (Filter.Eventually.of_forall fun a => ?_)
  · exact (measurable_jetIntegrand M n).aestronglyMeasurable
  · exact jetDensity_smul_le M hn a

theorem integral_jetMoment_le (hc : 0 ≤ c)
    (hM : ∫⁻ a, ENNReal.ofReal ((1 + ‖M.frequency a‖) ^ J) * ‖M.amplitude a‖ₑ ∂M.μ ≤ ENNReal.ofReal c)
    (n : ℕ) (hn : n ≤ J) :
    ∫ v, ‖v‖ ^ n * ‖v.2‖ ∂(jetMeasure M) ≤ c := by
  have hcont : Continuous (fun v : Mom d × ℂ => ‖v‖ ^ n * ‖v.2‖) :=
    (continuous_norm.pow n).mul (continuous_norm.comp continuous_snd)
  unfold jetMeasure
  rw [integral_map (measurable_jetMap M).aemeasurable hcont.aestronglyMeasurable,
    integral_withDensity_eq_integral_smul (measurable_jetDensity M)]
  have h1 : ∫ a, jetDensity M a • (‖jetMap M a‖ ^ n * ‖(jetMap M a).2‖) ∂M.μ ≤
      ∫ a, (1 + ‖M.frequency a‖) ^ J * ‖ampMk M a‖ ∂M.μ := by
    refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun a => ?_) (integrable_moment M hM)
      (Filter.Eventually.of_forall fun a => ?_)
    · exact smul_nonneg (jetDensity M a).2 (by positivity)
    · have := jetDensity_smul_le M hn a
      dsimp only
      rw [NNReal.smul_def, smul_eq_mul]
      exact (le_abs_self _).trans (by simpa [Real.norm_eq_abs] using this)
  refine h1.trans ?_
  rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun a => by positivity)
    (integrable_moment M hM).aestronglyMeasurable]
  refine ENNReal.toReal_le_of_le_ofReal hc ?_
  refine le_trans (le_of_eq ?_) hM
  rw [← lintegral_moment_eq]
  refine lintegral_congr fun a => ?_
  rw [Real.enorm_eq_ofReal (by positivity)]

/-- **A Fourier-presented weight is `C^J`.** -/
theorem contDiff_value
    (hM : ∫⁻ a, ENNReal.ofReal ((1 + ‖M.frequency a‖) ^ J) * ‖M.amplitude a‖ₑ ∂M.μ ≤ ENNReal.ofReal c) :
    ContDiff ℝ J M.value := by
  have e : M.value = VectorFourier.fourierIntegral Real.fourierChar (jetMeasure M)
      (jetPairing d).toLinearMap₁₂ (fun v => v.2) := funext (value_eq_fourierIntegral M)
  rw [e]
  have h := VectorFourier.contDiff_fourierIntegral (jetPairing d) (μ := jetMeasure M) (f := fun v => v.2)
    (N := (J : ℕ∞)) (fun n hn => integrable_jetMoment M hM n (by exact_mod_cast hn))
  exact_mod_cast h

/-- **Jet bound of a Fourier-presented weight**: `‖D^n M.value‖ ≤ (2π)^n c` for `n ≤ J`. -/
theorem norm_iteratedFDeriv_value_le (hc : 0 ≤ c)
    (hM : ∫⁻ a, ENNReal.ofReal ((1 + ‖M.frequency a‖) ^ J) * ‖M.amplitude a‖ₑ ∂M.μ ≤ ENNReal.ofReal c)
    (n : ℕ) (hn : n ≤ J) (x : Mom d) :
    ‖iteratedFDeriv ℝ n M.value x‖ ≤ (2 * π) ^ n * c := by
  have e : M.value = VectorFourier.fourierIntegral Real.fourierChar (jetMeasure M)
      (jetPairing d).toLinearMap₁₂ (fun v => v.2) := funext (value_eq_fourierIntegral M)
  rw [e, VectorFourier.iteratedFDeriv_fourierIntegral (jetPairing d) (μ := jetMeasure M) (N := (J : ℕ∞))
    (fun m hm => integrable_jetMoment M hM m (by exact_mod_cast hm)) continuous_snd.aestronglyMeasurable
    (by exact_mod_cast hn)]
  unfold VectorFourier.fourierIntegral
  have hg : Integrable (fun v : Mom d × ℂ => (2 * π) ^ n * (‖v‖ ^ n * ‖v.2‖)) (jetMeasure M) :=
    (integrable_jetMoment M hM n hn).const_mul _
  refine (norm_integral_le_of_norm_le hg (Filter.Eventually.of_forall fun v => ?_)).trans ?_
  · rw [Circle.norm_smul]
    refine (VectorFourier.norm_fourierPowSMulRight_le (jetPairing d) (fun v : Mom d × ℂ => v.2) v n).trans ?_
    have hL : 2 * π * ‖jetPairing d‖ ≤ 2 * π :=
      mul_le_of_le_one_right (by positivity) (norm_jetPairing_le d)
    have := pow_le_pow_left₀ (by positivity) hL n
    calc (2 * π * ‖jetPairing d‖) ^ n * ‖v‖ ^ n * ‖v.2‖ = (2 * π * ‖jetPairing d‖) ^ n * (‖v‖ ^ n * ‖v.2‖) := by
          ring
      _ ≤ (2 * π) ^ n * (‖v‖ ^ n * ‖v.2‖) := mul_le_mul_of_nonneg_right this (by positivity)
  · rw [integral_const_mul]
    exact mul_le_mul_of_nonneg_left (integral_jetMoment_le M hc hM n hn) (by positivity)

end Moments

end WaveTurbulence.Flower.Stage1WNoVine
