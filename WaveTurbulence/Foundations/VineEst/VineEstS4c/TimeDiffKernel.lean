/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS4c.TimeDiffGauss
public import WaveTurbulence.Foundations.SumintSigned.NormIntegralMinkowski
public import WaveTurbulence.Foundations.SumintSigned.NormModulation
public import WaveTurbulence.Foundations.SumintSigned.NormScalar
public import WaveTurbulence.Foundations.Fourier.SchwartzNorm
import Mathlib.Tactic

/-!
# V5 Step 4c, clause (c): the stage-one kernel

For `s > 0`, `μ, ℓ ∈ ℝ` and a smooth compactly supported cutoff `κ` on `ℝ³`, the kernel
`T(τ) = κ(τ) e^{-s(τ₀-τ₁)²} (𝐞(μτ₀) - 𝐞(μτ₁)) 𝐞(ℓτ₂)` is a Gaussian superposition (over the
frequency `x`, with density `gam(x-μ/√s) - gam x`) of modulated cutoffs.
-/

@[expose] public section
set_option autoImplicit false

open MeasureTheory Real Complex
open scoped ENNReal ContDiff

namespace WaveTurbulence.VineEstS4c.TimeDiff

/-- The shifted-Gaussian difference density. -/
@[expose] noncomputable def Dg (a x : ℝ) : ℝ := gam (x - a) - gam x

theorem integrable_gam_shift_mul_ee (a y : ℝ) :
    Integrable (fun x : ℝ => (gam (x - a) : ℂ) * ee (x * y)) := by
  refine (integrable_gam.comp_sub_right a).norm.mono' ?_ ?_
  · exact (Complex.continuous_ofReal.comp (continuous_gam.comp (continuous_sub_right a))).mul
      (continuous_ee.comp (continuous_id.mul continuous_const)) |>.aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun x => by
      rw [norm_mul, norm_ee, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (gam_nonneg _)]

theorem integrable_gam_mul_ee (y : ℝ) :
    Integrable (fun x : ℝ => (gam x : ℂ) * ee (x * y)) := by
  simpa using integrable_gam_shift_mul_ee 0 y

theorem gam_shift_inversion (a y : ℝ) :
    ∫ x, (gam (x - a) : ℂ) * ee (x * y) = ee (a * y) * Complex.exp (-(y : ℂ) ^ 2) := by
  have h := integral_add_right_eq_self (μ := (volume : Measure ℝ)) (fun x : ℝ => (gam (x - a) : ℂ) * ee (x * y)) a
  rw [← h]
  have e : ∀ x : ℝ, (gam (x + a - a) : ℂ) * ee ((x + a) * y) =
      ee (a * y) * ((gam x : ℂ) * ee (x * y)) := by
    intro x
    rw [add_sub_cancel_right, add_mul, mul_comm (a : ℝ) y, ee_add]
    ring
  simp_rw [e]
  rw [integral_const_mul, gam_inversion]

theorem Dg_inversion (a y : ℝ) :
    ∫ x, (Dg a x : ℂ) * ee (x * y) = (ee (a * y) - 1) * Complex.exp (-(y : ℂ) ^ 2) := by
  have e : ∀ x : ℝ, (Dg a x : ℂ) * ee (x * y) =
      (gam (x - a) : ℂ) * ee (x * y) - (gam x : ℂ) * ee (x * y) := by
    intro x; unfold Dg; push_cast; ring
  simp_rw [e]
  rw [integral_sub (integrable_gam_shift_mul_ee a y) (integrable_gam_mul_ee y), gam_shift_inversion,
    gam_inversion]
  ring


/-- The frequency vector of the `x`-th Gaussian mode. -/
@[expose] noncomputable def w3 (s x μ l : ℝ) : Fin 3 → ℝ := ![x * √s, μ - x * √s, l]

/-- The stage-one kernel. -/
@[expose] noncomputable def Tk (κ : (Fin 3 → ℝ) → ℂ) (s μ l : ℝ) (τ : Fin 3 → ℝ) : ℂ :=
  κ τ * ((Real.exp (-(s * (τ 0 - τ 1) ^ 2)) : ℝ) : ℂ) * (ee (μ * τ 0) - ee (μ * τ 1)) * ee (l * τ 2)

theorem w3_zero (s x μ l : ℝ) : w3 s x μ l 0 = x * √s := by simp [w3]
theorem w3_one (s x μ l : ℝ) : w3 s x μ l 1 = μ - x * √s := by simp [w3]
theorem w3_two (s x μ l : ℝ) : w3 s x μ l 2 = l := by simp [w3]

theorem timePairing3 (τ w : Fin 3 → ℝ) :
    WaveTurbulence.Fourier.timePairing 3 τ w = τ 0 * w 0 + τ 1 * w 1 + τ 2 * w 2 := by
  simp [WaveTurbulence.Fourier.timePairing, dotProduct, Fin.sum_univ_three]

theorem fourierChar_w3 (s x μ l : ℝ) (τ : Fin 3 → ℝ) :
    ((Real.fourierChar (WaveTurbulence.Fourier.timePairing 3 τ (w3 s x μ l)) : Circle) : ℂ) =
      ee (x * (√s * (τ 0 - τ 1))) * ee (μ * τ 1 + l * τ 2) := by
  rw [← ee_eq_fourierChar, ← ee_add, timePairing3]
  congr 1
  rw [w3_zero, w3_one, w3_two]
  ring

theorem Tk_eq_integral (κ : (Fin 3 → ℝ) → ℂ) {s : ℝ} (hs : 0 < s) (μ l : ℝ) (τ : Fin 3 → ℝ) :
    Tk κ s μ l τ = ∫ x, (Dg (μ / √s) x : ℂ) •
      ((Real.fourierChar (WaveTurbulence.Fourier.timePairing 3 τ (w3 s x μ l)) : Circle) • κ τ) := by
  have hsq : 0 < √s := Real.sqrt_pos.mpr hs
  have e : ∀ x : ℝ, (Dg (μ / √s) x : ℂ) •
      ((Real.fourierChar (WaveTurbulence.Fourier.timePairing 3 τ (w3 s x μ l)) : Circle) • κ τ) =
      (κ τ * ee (μ * τ 1 + l * τ 2)) * ((Dg (μ / √s) x : ℂ) * ee (x * (√s * (τ 0 - τ 1)))) := by
    intro x
    rw [Circle.smul_def, fourierChar_w3, smul_eq_mul, smul_eq_mul]
    ring
  simp_rw [e]
  rw [integral_const_mul, Dg_inversion]
  have h1 : μ / √s * (√s * (τ 0 - τ 1)) = μ * (τ 0 - τ 1) := by field_simp
  have h2 : (((√s * (τ 0 - τ 1) : ℝ) : ℂ)) ^ 2 = ((s * (τ 0 - τ 1) ^ 2 : ℝ) : ℂ) := by
    push_cast
    have : ((√s : ℝ) : ℂ) ^ 2 = (s : ℂ) := by
      rw [← Complex.ofReal_pow, Real.sq_sqrt hs.le]
    rw [mul_pow, this]
  rw [h1, h2]
  have h3 : Complex.exp (-((s * (τ 0 - τ 1) ^ 2 : ℝ) : ℂ)) =
      ((Real.exp (-(s * (τ 0 - τ 1) ^ 2)) : ℝ) : ℂ) := by
    rw [Complex.ofReal_exp]; push_cast; rfl
  rw [h3]
  unfold Tk
  have h4 : ee (μ * τ 0) = ee (μ * (τ 0 - τ 1)) * ee (μ * τ 1) := by
    rw [← ee_add]; congr 1; ring
  have h5 : ee (μ * τ 1 + l * τ 2) = ee (μ * τ 1) * ee (l * τ 2) := ee_add _ _
  rw [h4, h5]
  ring


theorem sqrt_one_add_sub_sq_le (a b : ℝ) :
    √(1 + (a - b) ^ 2) ≤ √2 * √(1 + a ^ 2) * √(1 + b ^ 2) := by
  rw [← Real.sqrt_mul (by norm_num), ← Real.sqrt_mul (by positivity)]
  apply Real.sqrt_le_sqrt
  have := one_add_sq_add_le a (-b)
  simpa [sub_eq_add_neg] using this

/-- The bracket of the Gaussian-mode frequency vector. -/
theorem timeBracket_w3_le (s x μ l : ℝ) (hs : 0 ≤ s) :
    WaveTurbulence.Fourier.timeBracket (w3 s x μ l) ≤
      √2 * √(1 + x ^ 2 * s) * max √(1 + μ ^ 2) √(1 + l ^ 2) := by
  have hB : 1 ≤ max √(1 + μ ^ 2) √(1 + l ^ 2) := by
    refine le_max_of_le_left ?_
    simpa using Real.sqrt_le_sqrt (show (1 : ℝ) ≤ 1 + μ ^ 2 by nlinarith [sq_nonneg μ])
  have hX : 1 ≤ √(1 + x ^ 2 * s) := by
    simpa using Real.sqrt_le_sqrt
      (show (1 : ℝ) ≤ 1 + x ^ 2 * s by nlinarith [mul_nonneg (sq_nonneg x) hs])
  have h2 : (1 : ℝ) ≤ √2 := by
    simp
  have hBnn : 0 ≤ max √(1 + μ ^ 2) √(1 + l ^ 2) := by linarith
  apply WaveTurbulence.Fourier.timeBracket_le
  · have := mul_le_mul h2 hX zero_le_one (by linarith)
    nlinarith
  · intro j
    have hxs : (x * √s) ^ 2 = x ^ 2 * s := by rw [mul_pow, Real.sq_sqrt hs]
    have hmuB : √(1 + μ ^ 2) ≤ max √(1 + μ ^ 2) √(1 + l ^ 2) := le_max_left _ _
    have hlB : √(1 + l ^ 2) ≤ max √(1 + μ ^ 2) √(1 + l ^ 2) := le_max_right _ _
    have hbig : max √(1 + μ ^ 2) √(1 + l ^ 2) ≤
        √2 * √(1 + x ^ 2 * s) * max √(1 + μ ^ 2) √(1 + l ^ 2) := by
      have := mul_le_mul h2 hX zero_le_one (by linarith)
      nlinarith
    fin_cases j
    · simp only [Fin.zero_eta, w3, Matrix.cons_val_zero]
      rw [hxs]
      calc √(1 + x ^ 2 * s) ≤ √2 * √(1 + x ^ 2 * s) * max √(1 + μ ^ 2) √(1 + l ^ 2) := by
            have := mul_le_mul h2 hX zero_le_one (by linarith)
            nlinarith [mul_le_mul this hB zero_le_one (by positivity)]
        _ = _ := rfl
    · simp only [Fin.mk_one, w3, Matrix.cons_val_one, Matrix.cons_val_zero]
      have h := sqrt_one_add_sub_sq_le μ (x * √s)
      rw [hxs] at h
      calc _ ≤ √2 * √(1 + μ ^ 2) * √(1 + x ^ 2 * s) := h
        _ ≤ √2 * max √(1 + μ ^ 2) √(1 + l ^ 2) * √(1 + x ^ 2 * s) := by gcongr
        _ = _ := by ring
    · simp only [Fin.reduceFinMk, w3]
      show √(1 + l ^ 2) ≤ _
      exact hlB.trans hbig


theorem integrable_Dg (a : ℝ) : Integrable (fun x => Dg a x) :=
  (integrable_gam.comp_sub_right a).sub integrable_gam

/-- Stage one, before the weight bookkeeping: Minkowski over the Gaussian frequency. -/
theorem mixedNorm_Tk_le_lintegral (θ : ℝ) {κ : (Fin 3 → ℝ) → ℂ} (hκc : HasCompactSupport κ)
    (hκs : ContDiff ℝ ∞ κ) {s : ℝ} (hs : 0 < s) (μ l : ℝ) :
    WaveTurbulence.Fourier.mixedFourierNorm00 θ (fun τ (_ : Unit) => Tk κ s μ l τ) ≤
      ∫⁻ x, ‖(Dg (μ / √s) x : ℂ)‖ₑ * (ENNReal.ofReal (2 ^ |θ|) *
        WaveTurbulence.Fourier.timeWeight |θ| (w3 s x μ l) *
          WaveTurbulence.Fourier.timeFourierNorm θ κ) := by
  set a := μ / √s with ha
  let F : ℝ → (Fin 3 → ℝ) → Unit → ℂ := fun x τ _ =>
    (Dg a x : ℂ) • ((Real.fourierChar (WaveTurbulence.Fourier.timePairing 3 τ (w3 s x μ l)) :
      Circle) • κ τ)
  have hfun : (fun τ (_ : Unit) => Tk κ s μ l τ) = fun τ v => ∫ x, F x τ v := by
    funext τ v; exact Tk_eq_integral κ hs μ l τ
  rw [hfun]
  have hκi : Integrable κ := hκs.continuous.integrable_of_hasCompactSupport hκc
  have hcont : Continuous (fun p : ℝ × (Fin 3 → ℝ) =>
      F p.1 p.2 ()) := by
    have h1 : Continuous (fun p : ℝ × (Fin 3 → ℝ) => ((Dg a p.1 : ℝ) : ℂ)) := by
      unfold Dg
      exact Complex.continuous_ofReal.comp
        ((continuous_gam.comp (continuous_fst.sub continuous_const)).sub (continuous_gam.comp continuous_fst))
    have h2 : Continuous (fun p : ℝ × (Fin 3 → ℝ) =>
        ((Real.fourierChar (WaveTurbulence.Fourier.timePairing 3 p.2 (w3 s p.1 μ l)) : Circle) : ℂ)) := by
      have : Continuous (fun p : ℝ × (Fin 3 → ℝ) =>
          WaveTurbulence.Fourier.timePairing 3 p.2 (w3 s p.1 μ l)) := by
        simp_rw [timePairing3, w3_zero, w3_one, w3_two]
        fun_prop
      exact continuous_subtype_val.comp (Real.continuous_fourierChar.comp this)
    have h3 : Continuous (fun p : ℝ × (Fin 3 → ℝ) => κ p.2) := hκs.continuous.comp continuous_snd
    simp only [F, Circle.smul_def, smul_eq_mul]
    exact h1.mul (h2.mul h3)
  refine (SumintSigned.mixedFourierNorm00_integral_le (μ := (volume : Measure ℝ)) θ F
    (fun _ => hcont.measurable) ?_ ?_).trans (lintegral_mono fun x => ?_)
  · intro _
    refine ((integrable_Dg a).norm.mul_prod hκi.norm).mono' hcont.aestronglyMeasurable ?_
    exact Filter.Eventually.of_forall fun p => by
      simp only [F, norm_smul, Circle.norm_smul, Real.norm_eq_abs, Complex.norm_real]
      exact le_rfl
  · intro x _
    refine (hκi.norm.const_mul |Dg a x|).mono' ?_ ?_
    · exact (hcont.comp (Continuous.prodMk_right x)).aestronglyMeasurable
    · exact Filter.Eventually.of_forall fun τ => by
        simp only [F, norm_smul, Circle.norm_smul, Real.norm_eq_abs, Complex.norm_real]
        exact le_rfl
  · have hsm : (fun τ (_ : Unit) => F x τ ()) = fun τ v => (Dg a x : ℂ) •
        ((Real.fourierChar (WaveTurbulence.Fourier.timePairing 3 τ (w3 s x μ l)) : Circle) •
          (fun τ (_ : Unit) => κ τ) τ v) := rfl
    show WaveTurbulence.Fourier.mixedFourierNorm00 θ (fun τ (v : Unit) => F x τ v) ≤ _
    rw [show (fun τ (v : Unit) => F x τ v) = fun τ v => (Dg a x : ℂ) •
        ((Real.fourierChar (WaveTurbulence.Fourier.timePairing 3 τ (w3 s x μ l)) : Circle) •
          κ τ) from rfl, SumintSigned.mixedFourierNorm00_smul]
    gcongr
    refine (SumintSigned.mixedFourierNorm00_modulate_le_abs θ (fun τ (_ : Unit) => κ τ) (w3 s x μ l)).trans ?_
    rw [WaveTurbulence.Fourier.mixedFourierNorm00_unit]


/-- The scale-dependent factor of the stage-one norm. -/
@[expose] noncomputable def kerFac (θ μ s : ℝ) : ℝ :=
  ((1 + s) * (1 + μ ^ 2 / s)) ^ (θ / 2) * min 1 (|μ| / √s)

/-- The frequency-bracket factor. -/
@[expose] noncomputable def Bw (μ l : ℝ) : ℝ := max √(1 + μ ^ 2) √(1 + l ^ 2)

theorem one_le_Bw (μ l : ℝ) : 1 ≤ Bw μ l := by
  refine le_max_of_le_left ?_
  simpa using Real.sqrt_le_sqrt (show (1 : ℝ) ≤ 1 + μ ^ 2 by nlinarith [sq_nonneg μ])

theorem weight_pointwise {θ : ℝ} (hθ : 0 ≤ θ) {s : ℝ} (hs : 0 < s) (x μ l : ℝ) :
    2 ^ θ * WaveTurbulence.Fourier.timeBracket (w3 s x μ l) ^ θ ≤
      (2 ^ θ * 2 ^ (θ / 2) * (1 + s) ^ (θ / 2) * Bw μ l ^ θ) * (1 + x ^ 2) ^ (θ / 2) := by
  have h1 := timeBracket_w3_le s x μ l hs.le
  have hB := one_le_Bw μ l
  have hb0 : 0 ≤ WaveTurbulence.Fourier.timeBracket (w3 s x μ l) :=
    (WaveTurbulence.Fourier.timeBracket_pos _).le
  have h2 : WaveTurbulence.Fourier.timeBracket (w3 s x μ l) ^ θ ≤
      (√2 * √(1 + x ^ 2 * s) * Bw μ l) ^ θ := Real.rpow_le_rpow hb0 h1 hθ
  have hX : 0 ≤ √(1 + x ^ 2 * s) := Real.sqrt_nonneg _
  have e1 : (√2 * √(1 + x ^ 2 * s) * Bw μ l) ^ θ =
      2 ^ (θ / 2) * (1 + x ^ 2 * s) ^ (θ / 2) * Bw μ l ^ θ := by
    rw [Real.mul_rpow (by positivity) (by linarith), Real.mul_rpow (by positivity) (by positivity),
      Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_mul (by norm_num),
      ← Real.rpow_mul (by positivity)]
    congr 3 <;> ring
  have h3 : (1 + x ^ 2 * s) ^ (θ / 2) ≤ ((1 + s) * (1 + x ^ 2)) ^ (θ / 2) :=
    Real.rpow_le_rpow (by positivity) (by nlinarith [sq_nonneg x, mul_nonneg (sq_nonneg x) hs.le])
      (by linarith)
  rw [Real.mul_rpow (by positivity) (by positivity)] at h3
  calc 2 ^ θ * WaveTurbulence.Fourier.timeBracket (w3 s x μ l) ^ θ
      ≤ 2 ^ θ * (2 ^ (θ / 2) * (1 + x ^ 2 * s) ^ (θ / 2) * Bw μ l ^ θ) := by
        gcongr; exact h2.trans_eq e1
    _ ≤ 2 ^ θ * (2 ^ (θ / 2) * ((1 + s) ^ (θ / 2) * (1 + x ^ 2) ^ (θ / 2)) * Bw μ l ^ θ) := by
        gcongr
    _ = _ := by ring


/-- **Stage one**: the `𝔛^θ` norm of the kernel `Tk` (`0 ≤ θ ≤ 1`). -/
theorem mixedNorm_Tk_le {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) {κ : (Fin 3 → ℝ) → ℂ}
    (hκc : HasCompactSupport κ) (hκs : ContDiff ℝ ∞ κ) {s : ℝ} (hs : 0 < s) (μ l : ℝ) :
    WaveTurbulence.Fourier.mixedFourierNorm00 θ (fun τ (_ : Unit) => Tk κ s μ l τ) ≤
      ENNReal.ofReal (4 ^ θ * (2 * π ^ 2 * Mg) * Bw μ l ^ θ * kerFac θ μ s) *
        WaveTurbulence.Fourier.timeFourierNorm θ κ := by
  refine (mixedNorm_Tk_le_lintegral θ hκc hκs hs μ l).trans ?_
  set N := WaveTurbulence.Fourier.timeFourierNorm θ κ
  set Kc : ℝ := 2 ^ θ * 2 ^ (θ / 2) * (1 + s) ^ (θ / 2) * Bw μ l ^ θ with hKc
  have hB0 : 0 ≤ Bw μ l := by linarith [one_le_Bw μ l]
  have hKc0 : 0 ≤ Kc := by positivity
  have hpt : ∀ x : ℝ, ‖(Dg (μ / √s) x : ℂ)‖ₑ * (ENNReal.ofReal (2 ^ |θ|) *
        WaveTurbulence.Fourier.timeWeight |θ| (w3 s x μ l) * N) ≤
      (ENNReal.ofReal Kc * N) * ENNReal.ofReal (|Dg (μ / √s) x| * (1 + x ^ 2) ^ (θ / 2)) := by
    intro x
    have h := weight_pointwise hθ0 hs x μ l
    have e1 : ‖(Dg (μ / √s) x : ℂ)‖ₑ = ENNReal.ofReal |Dg (μ / √s) x| := by
      rw [← ofReal_norm, Complex.norm_real, Real.norm_eq_abs]
    rw [e1, abs_of_nonneg hθ0, WaveTurbulence.Fourier.timeWeight]
    have e2 : ENNReal.ofReal (2 ^ θ) * ENNReal.ofReal (WaveTurbulence.Fourier.timeBracket (w3 s x μ l) ^ θ)
        ≤ ENNReal.ofReal Kc * ENNReal.ofReal ((1 + x ^ 2) ^ (θ / 2)) := by
      rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul hKc0]
      exact ENNReal.ofReal_le_ofReal h
    calc ENNReal.ofReal |Dg (μ / √s) x| * (ENNReal.ofReal (2 ^ θ) *
          ENNReal.ofReal (WaveTurbulence.Fourier.timeBracket (w3 s x μ l) ^ θ) * N)
        ≤ ENNReal.ofReal |Dg (μ / √s) x| * (ENNReal.ofReal Kc *
          ENNReal.ofReal ((1 + x ^ 2) ^ (θ / 2)) * N) := by gcongr
      _ = _ := by
        rw [ENNReal.ofReal_mul (abs_nonneg _)]
        ring
  refine (lintegral_mono hpt).trans ?_
  have hN : N < ⊤ := WaveTurbulence.Fourier.timeFourierNorm_lt_top_of_smooth_compact θ hκc hκs
  rw [lintegral_const_mul' _ _ (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hN.ne)]
  have hg := lintegral_gam_diff_le (θ := θ / 2) (by linarith) (by linarith) (μ / √s)
  have hsq : 0 < √s := Real.sqrt_pos.mpr hs
  have hrel : ENNReal.ofReal Kc * ENNReal.ofReal (2 ^ (θ / 2) * (2 * π ^ 2 * Mg) *
      (1 + (μ / √s) ^ 2) ^ (θ / 2) * min 1 |μ / √s|) =
      ENNReal.ofReal (4 ^ θ * (2 * π ^ 2 * Mg) * Bw μ l ^ θ * kerFac θ μ s) := by
    rw [← ENNReal.ofReal_mul hKc0]
    congr 1
    have e1 : (μ / √s) ^ 2 = μ ^ 2 / s := by rw [div_pow, Real.sq_sqrt hs.le]
    have e2 : |μ / √s| = |μ| / √s := by rw [abs_div, abs_of_pos hsq]
    have e3 : (4 : ℝ) ^ θ = 2 ^ θ * 2 ^ θ := by
      rw [← Real.mul_rpow (by norm_num) (by norm_num)]; norm_num
    have e4 : (2 : ℝ) ^ θ = 2 ^ (θ / 2) * 2 ^ (θ / 2) := by
      rw [← Real.rpow_add (by norm_num)]; congr 1; ring
    have e5 : ((1 + s) * (1 + μ ^ 2 / s)) ^ (θ / 2) = (1 + s) ^ (θ / 2) * (1 + μ ^ 2 / s) ^ (θ / 2) :=
      Real.mul_rpow (by positivity) (by positivity)
    unfold kerFac
    rw [e1, e2, e5, hKc, e3]
    nth_rewrite 2 [e4]
    ring
  calc ENNReal.ofReal Kc * N * ∫⁻ x, ENNReal.ofReal (|Dg (μ / √s) x| * (1 + x ^ 2) ^ (θ / 2))
      ≤ ENNReal.ofReal Kc * N * ENNReal.ofReal (2 ^ (θ / 2) * (2 * π ^ 2 * Mg) *
          (1 + (μ / √s) ^ 2) ^ (θ / 2) * min 1 |μ / √s|) := by
        gcongr
        exact hg
    _ = _ := by rw [mul_right_comm, hrel]

end WaveTurbulence.VineEstS4c.TimeDiff
