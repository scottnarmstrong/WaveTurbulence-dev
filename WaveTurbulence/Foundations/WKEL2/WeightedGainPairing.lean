/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.WKEL2.GainPairing
public import WaveTurbulence.Foundations.WKEL2.GainSwap
public import WaveTurbulence.Foundations.WKEL2.WeightedGainKernel

/-!
# The weighted gain pairing

Research-note Proposition 7: transfer the output weight to either outside
input and use the unweighted gain Schur pairing on both terms.
-/

public section

noncomputable section

open MeasureTheory
open scoped InnerProductSpace ENNReal

namespace WaveTurbulence.WKEL2

variable {d : ℕ}

/-- The gain pairing with the exact frozen output weight is uniformly bounded. -/
theorem exists_weighted_gain_pairing_bound (hd : 3 ≤ d) (s : ℝ)
    (hs : (d : ℝ) / 2 - 1 < s) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ e : Mom d, ‖e‖ = 1 → ∀ f₁ f₂ f₃ F : Mom d → ℝ,
      Measurable f₁ → Measurable f₂ → Measurable f₃ → Measurable F →
      MemLp (weightedFunction s f₁) 2 → MemLp (weightedFunction s f₂) 2 →
      MemLp (weightedFunction s f₃) 2 → MemLp F 2 →
      (∫⁻ q : Mom d × (Mom d × Mom d), ENNReal.ofReal ((1 + ‖q.1‖ ^ 2) ^ (s / 2)) *
        (ENNReal.ofReal |f₁ (q.1 + q.2.1)| * ENNReal.ofReal |f₂ (q.1 + q.2.1 + q.2.2)| *
          ENNReal.ofReal |f₃ (q.1 + q.2.2)| * ENNReal.ofReal |F q.1|)
          ∂volume.prod (resonantMeasure e)) ≤
        ENNReal.ofReal C * ENNReal.ofReal (weightedL2Norm s f₁ * weightedL2Norm s f₂ *
          weightedL2Norm s f₃) * ENNReal.ofReal (weightedL2Norm 0 F) := by
  obtain ⟨C, hC, hb⟩ := exists_gain_pairing_bound hd s hs
  have hs0 : 0 ≤ s := by
    have hdR : (3 : ℝ) ≤ d := by exact_mod_cast hd
    linarith only [hs, hdR]
  have hpow : 0 ≤ (2 : ℝ) ^ (s / 2) := Real.rpow_nonneg (by norm_num) _
  refine ⟨2 * (2 : ℝ) ^ (s / 2) * C, by positivity,
    fun e he f₁ f₂ f₃ F h₁ h₂ h₃ hF hL₁ hL₂ hL₃ hLF => ?_⟩
  let := resonantMeasure_finiteOnCompacts e (by omega : 2 ≤ d)
  let μ := (volume : Measure (Mom d)).prod (resonantMeasure e)
  let K (u v w : Mom d → ℝ) (q : Mom d × (Mom d × Mom d)) : ℝ≥0∞ :=
    ENNReal.ofReal |u (q.1 + q.2.1)| * ENNReal.ofReal |v (q.1 + q.2.1 + q.2.2)| *
      ENNReal.ofReal |w (q.1 + q.2.2)| * ENNReal.ofReal |F q.1|
  have hK {u v w : Mom d → ℝ} (hu : Measurable u) (hv : Measurable v) (hw : Measurable w) :
      Measurable (K u v w) :=
    (((hu.abs.ennreal_ofReal.comp (by fun_prop)).mul
      (hv.abs.ennreal_ofReal.comp (by fun_prop))).mul
        (hw.abs.ennreal_ofReal.comp (by fun_prop))).mul (hF.abs.ennreal_ofReal.comp measurable_fst)
  have hw₁ := measurable_weightedFunction s h₁
  have hw₃ := measurable_weightedFunction s h₃
  have hN₁ := weightedL2Norm_nonneg s f₁
  have hN₂ := weightedL2Norm_nonneg s f₂
  have hN₃ := weightedL2Norm_nonneg s f₃
  let M : ℝ≥0∞ := ENNReal.ofReal C * ENNReal.ofReal (weightedL2Norm s f₁) *
    ENNReal.ofReal (weightedL2Norm s f₂) * ENNReal.ofReal (weightedL2Norm s f₃) *
      ENNReal.ofReal (weightedL2Norm 0 F)
  have hA : (∫⁻ q, K (weightedFunction s f₁) f₂ f₃ q ∂μ) ≤ M := by
    have h := hb e he (weightedFunction s f₁) f₂ f₃ F hw₁ h₂ h₃ hF hL₁ hL₂ hL₃ hLF
    rw [weightedL2Norm_zero_weightedFunction, ENNReal.ofReal_mul hN₂, ENNReal.ofReal_mul hN₁] at h
    exact h.trans_eq (by dsimp only [M]; ac_rfl)
  have hBswap : (∫⁻ q, K f₁ f₂ (weightedFunction s f₃) q ∂μ) =
      ∫⁻ q, K (weightedFunction s f₃) f₂ f₁ q ∂μ := by
    calc
      _ = ∫⁻ q : Mom d × (Mom d × Mom d),
          K (weightedFunction s f₃) f₂ f₁ (q.1, (q.2.2, q.2.1)) ∂μ := by
        apply lintegral_congr
        rintro ⟨k, a, b⟩
        dsimp only [K]
        rw [show k + b + a = k + a + b by abel]
        ac_rfl
      _ = _ := lintegral_gain_swap he (by omega) (hK hw₃ h₂ h₁)
  have hB : (∫⁻ q, K f₁ f₂ (weightedFunction s f₃) q ∂μ) ≤ M := by
    rw [hBswap]
    have h := hb e he (weightedFunction s f₃) f₂ f₁ F hw₃ h₂ h₁ hF hL₃ hL₂ hL₁ hLF
    rw [weightedL2Norm_zero_weightedFunction, ENNReal.ofReal_mul hN₂, ENNReal.ofReal_mul hN₃] at h
    exact h.trans_eq (by dsimp only [M]; ac_rfl)
  have hset : MeasurableSet {q : Mom d × (Mom d × Mom d) | ⟪q.2.1, q.2.2⟫_ℝ = 0} :=
    (isClosed_eq (by fun_prop) continuous_const).measurableSet
  have hres : ∀ᵐ q ∂μ, ⟪q.2.1, q.2.2⟫_ℝ = 0 :=
    (Measure.ae_prod_iff_ae_ae hset).mpr (Filter.Eventually.of_forall fun _ => ae_inner_eq_zero he)
  have hpoint : ∀ᵐ q ∂μ,
      ENNReal.ofReal ((1 + ‖q.1‖ ^ 2) ^ (s / 2)) * K f₁ f₂ f₃ q ≤
        ENNReal.ofReal ((2 : ℝ) ^ (s / 2)) *
          (K (weightedFunction s f₁) f₂ f₃ q + K f₁ f₂ (weightedFunction s f₃) q) := by
    filter_upwards [hres] with q hq
    have h := mul_le_mul' (weighted_gain_kernel_le s hs0 f₁ f₂ f₃ q.1 q.2.1 q.2.2 hq)
      (le_refl (ENNReal.ofReal |F q.1|))
    simpa only [K, mul_assoc, add_mul] using h
  calc
    _ ≤ ∫⁻ q, ENNReal.ofReal ((2 : ℝ) ^ (s / 2)) *
        (K (weightedFunction s f₁) f₂ f₃ q + K f₁ f₂ (weightedFunction s f₃) q) ∂μ :=
      lintegral_mono_ae hpoint
    _ = ENNReal.ofReal ((2 : ℝ) ^ (s / 2)) *
        ((∫⁻ q, K (weightedFunction s f₁) f₂ f₃ q ∂μ) +
          ∫⁻ q, K f₁ f₂ (weightedFunction s f₃) q ∂μ) := by
      have hm : Measurable (fun q => K (weightedFunction s f₁) f₂ f₃ q +
          K f₁ f₂ (weightedFunction s f₃) q) := (hK hw₁ h₂ h₃).add (hK h₁ h₂ hw₃)
      rw [lintegral_const_mul _ hm, lintegral_add_left (hK hw₁ h₂ h₃) (K f₁ f₂ (weightedFunction s f₃))]
    _ ≤ ENNReal.ofReal ((2 : ℝ) ^ (s / 2)) * (M + M) :=
      mul_le_mul' le_rfl (add_le_add hA hB)
    _ = _ := by
      rw [ENNReal.ofReal_mul (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hpow),
        ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),
        ENNReal.ofReal_mul (mul_nonneg hN₁ hN₂), ENNReal.ofReal_mul hN₁]
      norm_num only [ENNReal.ofReal_ofNat]
      dsimp only [M]
      ring

end WaveTurbulence.WKEL2
