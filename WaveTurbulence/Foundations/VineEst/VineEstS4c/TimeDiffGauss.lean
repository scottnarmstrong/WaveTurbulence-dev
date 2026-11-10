/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
public import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Tactic
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# V5 Step 4c, clause (c): the unit Gaussian density used to Fourier-expand `|u|^{-b}`

`gam x = √π e^{-π² x²}` has unit mass and `∫ gam x · 𝐞(x y) dx = e^{-y²}`.
-/

@[expose] public section
set_option autoImplicit false

open MeasureTheory Real Complex
open scoped FourierTransform

namespace WaveTurbulence.VineEstS4c.TimeDiff

/-- The unit-mass Gaussian density `√π e^{-π² x²}`. -/
@[expose] noncomputable def gam (x : ℝ) : ℝ := √π * Real.exp (-(π ^ 2) * x ^ 2)

theorem gam_pos (x : ℝ) : 0 < gam x := by
  unfold gam; positivity

theorem gam_nonneg (x : ℝ) : 0 ≤ gam x := (gam_pos x).le

@[fun_prop] theorem continuous_gam : Continuous gam := by
  unfold gam; fun_prop

theorem integrable_gam : Integrable gam := by
  unfold gam
  have := integrable_exp_neg_mul_sq (b := π ^ 2) (by positivity)
  exact this.const_mul _

theorem integral_gam : ∫ x, gam x = 1 := by
  unfold gam
  rw [integral_const_mul, integral_gaussian]
  have hpi : 0 < π := Real.pi_pos
  rw [show π / π ^ 2 = (√π) ⁻¹ ^ 2 by
    rw [inv_pow, Real.sq_sqrt hpi.le]; field_simp]
  rw [Real.sqrt_sq (by positivity)]
  field_simp

/-- The unit-modulus phase `e^{2πi x}`. -/
@[expose] noncomputable def ee (x : ℝ) : ℂ := Complex.exp (((2 * π * x : ℝ) : ℂ) * Complex.I)

theorem ee_add (x y : ℝ) : ee (x + y) = ee x * ee y := by
  unfold ee; rw [← Complex.exp_add]; congr 1; push_cast; ring

theorem norm_ee (x : ℝ) : ‖ee x‖ = 1 := by
  unfold ee; exact Complex.norm_exp_ofReal_mul_I _

@[fun_prop] theorem continuous_ee : Continuous ee := by
  unfold ee; fun_prop

theorem ee_eq_fourierChar (x : ℝ) : ee x = (Real.fourierChar x : ℂ) := by
  rw [Real.fourierChar_apply]; rfl

/-- Fourier inversion for the unit Gaussian density. -/
theorem gam_inversion (y : ℝ) : ∫ x, (gam x : ℂ) * ee (x * y) = Complex.exp (-(y : ℂ) ^ 2) := by
  have hb : 0 < ((π : ℂ) ^ 2).re := by
    simp only [← Complex.ofReal_pow, Complex.ofReal_re]; positivity
  have h := fourierIntegral_gaussian hb (2 * π * y)
  have hpi : 0 < π := Real.pi_pos
  have e1 : ∀ x : ℝ, (gam x : ℂ) * ee (x * y) =
      (√π : ℂ) * (Complex.exp (Complex.I * (2 * π * y) * x) * Complex.exp (-((π : ℂ) ^ 2) * x ^ 2)) := by
    intro x
    unfold gam ee
    push_cast
    rw [mul_assoc, ← Complex.exp_add, ← Complex.exp_add]
    congr 2
    ring
  simp_rw [e1]
  rw [integral_const_mul, h]
  have e2 : (π / (π : ℂ) ^ 2) ^ (1 / 2 : ℂ) = ((√π : ℝ) : ℂ)⁻¹ := by
    have : (π : ℂ) / (π : ℂ) ^ 2 = (((1 / π : ℝ)) : ℂ) := by
      push_cast
      field_simp
    rw [this]
    have h2 : ((1 / 2 : ℝ) : ℂ) = (1 / 2 : ℂ) := by push_cast; ring
    rw [← h2, ← Complex.ofReal_cpow (by positivity)]
    rw [← Complex.ofReal_inv]
    congr 1
    rw [Real.sqrt_eq_rpow, ← Real.inv_rpow hpi.le, one_div]
  rw [e2, ← mul_assoc, mul_inv_cancel₀ (by exact_mod_cast (Real.sqrt_pos.mpr hpi).ne'), one_mul]
  congr 1
  push_cast
  field_simp
  ring

open scoped ENNReal

theorem integrable_gam_mul_sq : Integrable (fun x => gam x * (1 + x ^ 2)) := by
  have h2 : Integrable (fun x : ℝ => x ^ 2 * Real.exp (-(π ^ 2) * x ^ 2)) := by
    have := integrable_rpow_mul_exp_neg_mul_sq (b := π ^ 2) (by positivity) (s := 2) (by norm_num)
    simpa using this
  have : Integrable (fun x : ℝ => √π * (Real.exp (-(π ^ 2) * x ^ 2) +
      x ^ 2 * Real.exp (-(π ^ 2) * x ^ 2))) :=
    (((integrable_exp_neg_mul_sq (b := π ^ 2) (by positivity))).add h2).const_mul _
  refine this.congr (Filter.Eventually.of_forall fun x => ?_)
  simp only [gam]; ring

/-- `Mg = ∫ gam (1 + x²)`: the moment constant. -/
@[expose] noncomputable def Mg : ℝ := ∫ x, gam x * (1 + x ^ 2)

theorem Mg_nonneg : 0 ≤ Mg :=
  integral_nonneg fun x => mul_nonneg (gam_nonneg x) (by positivity)

theorem one_le_Mg : 1 ≤ Mg := by
  unfold Mg
  have h : ∫ x, gam x ≤ ∫ x, gam x * (1 + x ^ 2) :=
    integral_mono integrable_gam integrable_gam_mul_sq (fun x => by
      have := gam_nonneg x; nlinarith [sq_nonneg x])
  linarith [integral_gam]

theorem rpow_one_add_sq_le {q : ℝ} (hq1 : q ≤ 1) (x : ℝ) :
    (1 + x ^ 2) ^ q ≤ 1 + x ^ 2 := by
  calc (1 + x ^ 2) ^ q ≤ (1 + x ^ 2) ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by nlinarith [sq_nonneg x]) hq1
    _ = _ := Real.rpow_one _

theorem lintegral_gam_wt_le {q : ℝ} (hq1 : q ≤ 1) :
    ∫⁻ x, ENNReal.ofReal (gam x * (1 + x ^ 2) ^ q) ≤ ENNReal.ofReal Mg := by
  unfold Mg
  rw [ofReal_integral_eq_lintegral_ofReal integrable_gam_mul_sq
    (Filter.Eventually.of_forall fun x => mul_nonneg (gam_nonneg x) (by positivity))]
  exact lintegral_mono fun x => ENNReal.ofReal_le_ofReal
    (mul_le_mul_of_nonneg_left (rpow_one_add_sq_le hq1 x) (gam_nonneg x))

theorem one_add_sq_add_le (x y : ℝ) : 1 + (x + y) ^ 2 ≤ 2 * (1 + x ^ 2) * (1 + y ^ 2) := by
  nlinarith [sq_nonneg (x - y), sq_nonneg (x * y), sq_nonneg x, sq_nonneg y]

theorem rpow_peetre {θ : ℝ} (hθ : 0 ≤ θ) (x y : ℝ) :
    (1 + (x + y) ^ 2) ^ θ ≤ 2 ^ θ * (1 + x ^ 2) ^ θ * (1 + y ^ 2) ^ θ := by
  calc (1 + (x + y) ^ 2) ^ θ ≤ (2 * (1 + x ^ 2) * (1 + y ^ 2)) ^ θ :=
        Real.rpow_le_rpow (by positivity) (one_add_sq_add_le x y) hθ
    _ = _ := by
      rw [Real.mul_rpow (by positivity) (by positivity), Real.mul_rpow (by positivity) (by positivity)]

theorem one_le_two_rpow_mul {θ : ℝ} (hθ : 0 ≤ θ) (s : ℝ) :
    1 ≤ 2 ^ θ * (1 + s ^ 2) ^ θ := by
  have h1 : (1 : ℝ) ≤ 2 ^ θ := Real.one_le_rpow (by norm_num) hθ
  have h2 : (1 : ℝ) ≤ (1 + s ^ 2) ^ θ := Real.one_le_rpow (by nlinarith [sq_nonneg s]) hθ
  nlinarith

theorem lintegral_gam_shift_wt_le {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (s : ℝ) :
    ∫⁻ x, ENNReal.ofReal (gam (x - s) * (1 + x ^ 2) ^ θ) ≤
      ENNReal.ofReal (2 ^ θ * (1 + s ^ 2) ^ θ * Mg) := by
  have h : ∫⁻ x, ENNReal.ofReal (gam (x - s) * (1 + x ^ 2) ^ θ) =
      ∫⁻ y, ENNReal.ofReal (gam y * (1 + (y + s) ^ 2) ^ θ) := by
    rw [← lintegral_sub_right_eq_self (μ := volume)
      (fun y => ENNReal.ofReal (gam y * (1 + (y + s) ^ 2) ^ θ)) s]
    simp
  rw [h]
  calc ∫⁻ y, ENNReal.ofReal (gam y * (1 + (y + s) ^ 2) ^ θ)
      ≤ ∫⁻ y, ENNReal.ofReal (2 ^ θ * (1 + s ^ 2) ^ θ) *
          ENNReal.ofReal (gam y * (1 + y ^ 2) ^ θ) := by
        refine lintegral_mono fun y => ?_
        rw [← ENNReal.ofReal_mul (by positivity)]
        apply ENNReal.ofReal_le_ofReal
        have := rpow_peetre hθ0 y s
        have hg := gam_nonneg y
        nlinarith [mul_le_mul_of_nonneg_left this hg]
    _ = ENNReal.ofReal (2 ^ θ * (1 + s ^ 2) ^ θ) * ∫⁻ y, ENNReal.ofReal (gam y * (1 + y ^ 2) ^ θ) :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal (2 ^ θ * (1 + s ^ 2) ^ θ) * ENNReal.ofReal Mg :=
        by gcongr; exact lintegral_gam_wt_le hθ1
    _ = _ := by rw [← ENNReal.ofReal_mul (by positivity)]

theorem lintegral_gam_diff_le_one {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (s : ℝ) :
    ∫⁻ x, ENNReal.ofReal (|gam (x - s) - gam x| * (1 + x ^ 2) ^ θ) ≤
      ENNReal.ofReal (2 * (2 ^ θ * (1 + s ^ 2) ^ θ * Mg)) := by
  have hm : Measurable fun x : ℝ => ENNReal.ofReal (gam x * (1 + x ^ 2) ^ θ) :=
    (by fun_prop : Measurable fun x : ℝ => gam x * (1 + x ^ 2) ^ θ).ennreal_ofReal
  calc ∫⁻ x, ENNReal.ofReal (|gam (x - s) - gam x| * (1 + x ^ 2) ^ θ)
      ≤ ∫⁻ x, (ENNReal.ofReal (gam (x - s) * (1 + x ^ 2) ^ θ) +
          ENNReal.ofReal (gam x * (1 + x ^ 2) ^ θ)) := by
        refine lintegral_mono fun x => ?_
        rw [← ENNReal.ofReal_add (mul_nonneg (gam_nonneg _) (by positivity))
          (mul_nonneg (gam_nonneg _) (by positivity))]
        apply ENNReal.ofReal_le_ofReal
        have hw : 0 ≤ (1 + x ^ 2) ^ θ := by positivity
        rw [← add_mul]
        refine mul_le_mul_of_nonneg_right ?_ hw
        have := gam_nonneg (x - s); have := gam_nonneg x
        rw [abs_le]; constructor <;> linarith
    _ = (∫⁻ x, ENNReal.ofReal (gam (x - s) * (1 + x ^ 2) ^ θ)) +
          ∫⁻ x, ENNReal.ofReal (gam x * (1 + x ^ 2) ^ θ) := lintegral_add_right _ hm
    _ ≤ ENNReal.ofReal (2 ^ θ * (1 + s ^ 2) ^ θ * Mg) + ENNReal.ofReal (2 ^ θ * (1 + s ^ 2) ^ θ * Mg) := by
        refine add_le_add (lintegral_gam_shift_wt_le hθ0 hθ1 s) ?_
        refine (lintegral_gam_wt_le hθ1).trans (ENNReal.ofReal_le_ofReal ?_)
        have := one_le_two_rpow_mul hθ0 s
        nlinarith [one_le_Mg]
    _ = _ := by
      rw [← ENNReal.ofReal_add (by have := Mg_nonneg; positivity) (by have := Mg_nonneg; positivity)]
      congr 1; ring

/-- `|gam'| = 2π² |x| gam x`. -/
@[expose] noncomputable def dgam (x : ℝ) : ℝ := 2 * π ^ 2 * |x| * gam x

theorem dgam_nonneg (x : ℝ) : 0 ≤ dgam x := by
  unfold dgam; have := gam_nonneg x; positivity

@[fun_prop] theorem continuous_dgam : Continuous dgam := by
  unfold dgam; have := continuous_gam; fun_prop

theorem hasDerivAt_gam (x : ℝ) : HasDerivAt gam (-(2 * π ^ 2 * x) * gam x) x := by
  unfold gam
  have h1 : HasDerivAt (fun x : ℝ => -(π ^ 2) * x ^ 2) (-(π ^ 2) * (2 * x)) x := by
    simpa using ((hasDerivAt_pow 2 x).const_mul (-(π ^ 2)))
  have h2 := (h1.exp).const_mul (√π)
  convert h2 using 1
  ring

theorem abs_deriv_gam_le (x : ℝ) : |-(2 * π ^ 2 * x) * gam x| = dgam x := by
  unfold dgam
  rw [abs_mul, abs_neg, abs_mul, abs_of_nonneg (gam_nonneg x),
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * π ^ 2)]

/-- Mean value formula in integral form, as a bound. -/
theorem abs_gam_sub_le (x s : ℝ) :
    |gam (x - s) - gam x| ≤ |s| * ∫ v in (0 : ℝ)..1, dgam (x - s + v * s) := by
  have hd : ∀ v ∈ Set.uIcc (0 : ℝ) 1, HasDerivAt (fun v : ℝ => gam (x - s + v * s))
      ((-(2 * π ^ 2 * (x - s + v * s)) * gam (x - s + v * s)) * s) v := by
    intro v _
    have h1 : HasDerivAt (fun v : ℝ => x - s + v * s) s v := by
      simpa using ((hasDerivAt_id v).mul_const s).const_add (x - s)
    exact (hasDerivAt_gam _).comp v h1
  have hc : Continuous fun v : ℝ => (-(2 * π ^ 2 * (x - s + v * s)) * gam (x - s + v * s)) * s := by
    have := continuous_gam; fun_prop
  have hI := intervalIntegral.integral_eq_sub_of_hasDerivAt hd (hc.intervalIntegrable _ _)
  have h0 : gam (x - s + 0 * s) = gam (x - s) := by simp
  have h1 : gam (x - s + 1 * s) = gam x := by simp
  rw [h0, h1] at hI
  have : gam (x - s) - gam x = -∫ v in (0 : ℝ)..1,
      (-(2 * π ^ 2 * (x - s + v * s)) * gam (x - s + v * s)) * s := by rw [hI]; ring
  rw [this, abs_neg]
  refine (intervalIntegral.abs_integral_le_integral_abs zero_le_one).trans ?_
  have : (fun v : ℝ => |(-(2 * π ^ 2 * (x - s + v * s)) * gam (x - s + v * s)) * s|) =
      fun v => |s| * dgam (x - s + v * s) := by
    funext v; rw [abs_mul, abs_deriv_gam_le]; ring
  rw [this, intervalIntegral.integral_const_mul]

theorem ofReal_abs_gam_sub_le (x s : ℝ) :
    ENNReal.ofReal |gam (x - s) - gam x| ≤
      ENNReal.ofReal |s| * ∫⁻ v in Set.Ioc (0 : ℝ) 1, ENNReal.ofReal (dgam (x - s + v * s)) := by
  refine (ENNReal.ofReal_le_ofReal (abs_gam_sub_le x s)).trans ?_
  rw [ENNReal.ofReal_mul (abs_nonneg s)]
  gcongr
  rw [intervalIntegral.integral_of_le zero_le_one]
  rw [ofReal_integral_eq_lintegral_ofReal]
  · have : Continuous fun v : ℝ => dgam (x - s + v * s) := by
      have := continuous_dgam; fun_prop
    exact (this.integrableOn_Icc).mono_set Set.Ioc_subset_Icc_self
  · exact Filter.Eventually.of_forall fun v => dgam_nonneg _

theorem dgam_wt_le {θ : ℝ} (hθ0 : 0 ≤ θ) (y : ℝ) :
    dgam y * (1 + y ^ 2) ^ θ ≤ 2 * π ^ 2 * (gam y * (1 + y ^ 2) ^ (1 / 2 + θ)) := by
  have h1 : |y| ≤ (1 + y ^ 2) ^ (1 / 2 : ℝ) := by
    rw [← Real.sqrt_eq_rpow]
    exact Real.abs_le_sqrt (by nlinarith [sq_nonneg y])
  rw [Real.rpow_add (by positivity)]
  unfold dgam
  have hg := gam_nonneg y
  have hw : 0 ≤ (1 + y ^ 2) ^ θ := by positivity
  have : 2 * π ^ 2 * |y| * gam y * (1 + y ^ 2) ^ θ ≤
      2 * π ^ 2 * (1 + y ^ 2) ^ (1 / 2 : ℝ) * gam y * (1 + y ^ 2) ^ θ := by
    have h2 : 0 ≤ 2 * π ^ 2 := by positivity
    gcongr
  linarith [this]

theorem lintegral_gam_diff_le_two {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1 / 2) (s : ℝ) :
    ∫⁻ x, ENNReal.ofReal (|gam (x - s) - gam x| * (1 + x ^ 2) ^ θ) ≤
      ENNReal.ofReal (|s| * (2 ^ θ * (1 + s ^ 2) ^ θ * (2 * π ^ 2 * Mg))) := by
  have hmeas : Measurable (fun p : ℝ × ℝ =>
      ENNReal.ofReal (dgam (p.1 - s + p.2 * s)) * ENNReal.ofReal ((1 + p.1 ^ 2) ^ θ)) := by
    have := continuous_dgam
    fun_prop
  have step : ∀ v ∈ Set.Ioc (0 : ℝ) 1,
      ∫⁻ x, ENNReal.ofReal (dgam (x - s + v * s)) * ENNReal.ofReal ((1 + x ^ 2) ^ θ) ≤
        ENNReal.ofReal (2 ^ θ * (1 + s ^ 2) ^ θ * (2 * π ^ 2 * Mg)) := by
    intro v hv
    obtain ⟨t, ht⟩ : ∃ t : ℝ, t = -s + v * s := ⟨_, rfl⟩
    have e1 : ∀ x : ℝ, ENNReal.ofReal (dgam (x - s + v * s)) * ENNReal.ofReal ((1 + x ^ 2) ^ θ) =
        (fun y : ℝ => ENNReal.ofReal (dgam y * (1 + (y - t) ^ 2) ^ θ)) (x + t) := by
      intro x
      rw [← ENNReal.ofReal_mul (dgam_nonneg _)]
      have h1 : x - s + v * s = x + t := by rw [ht]; ring
      have h2 : x + t - t = x := by ring
      simp only [h1, h2]
    simp_rw [e1]
    rw [lintegral_add_right_eq_self (μ := volume)
      (fun y : ℝ => ENNReal.ofReal (dgam y * (1 + (y - t) ^ 2) ^ θ)) t]
    have ht2 : t ^ 2 ≤ s ^ 2 := by
      have : t = (v - 1) * s := by rw [ht]; ring
      rw [this, mul_pow]
      have : (v - 1) ^ 2 ≤ 1 := by nlinarith [hv.1, hv.2]
      nlinarith [sq_nonneg s]
    calc ∫⁻ y, ENNReal.ofReal (dgam y * (1 + (y - t) ^ 2) ^ θ)
        ≤ ∫⁻ y, ENNReal.ofReal (2 ^ θ * (1 + s ^ 2) ^ θ) *
            ENNReal.ofReal (2 * π ^ 2 * (gam y * (1 + y ^ 2) ^ (1 / 2 + θ))) := by
          refine lintegral_mono fun y => ?_
          rw [← ENNReal.ofReal_mul (by positivity)]
          apply ENNReal.ofReal_le_ofReal
          have hp := rpow_peetre hθ0 y (-t)
          rw [← sub_eq_add_neg] at hp
          have hp2 : (1 + t ^ 2) ^ θ ≤ (1 + s ^ 2) ^ θ :=
            Real.rpow_le_rpow (by positivity) (by linarith) hθ0
          have hd := dgam_nonneg y
          have hq := dgam_wt_le hθ0 y
          have hneg : (1 + (-t) ^ 2) = 1 + t ^ 2 := by ring
          rw [hneg] at hp
          calc dgam y * (1 + (y - t) ^ 2) ^ θ ≤ dgam y * (2 ^ θ * (1 + y ^ 2) ^ θ * (1 + s ^ 2) ^ θ) := by
                gcongr; exact hp.trans (by gcongr)
            _ = 2 ^ θ * (1 + s ^ 2) ^ θ * (dgam y * (1 + y ^ 2) ^ θ) := by ring
            _ ≤ 2 ^ θ * (1 + s ^ 2) ^ θ * (2 * π ^ 2 * (gam y * (1 + y ^ 2) ^ (1 / 2 + θ))) := by
                gcongr
      _ = ENNReal.ofReal (2 ^ θ * (1 + s ^ 2) ^ θ) *
            ∫⁻ y, ENNReal.ofReal (2 * π ^ 2 * (gam y * (1 + y ^ 2) ^ (1 / 2 + θ))) :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal (2 ^ θ * (1 + s ^ 2) ^ θ) * ENNReal.ofReal (2 * π ^ 2 * Mg) := by
          gcongr
          simp_rw [ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 2 * π ^ 2)]
          rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
          gcongr
          exact lintegral_gam_wt_le (by linarith)
      _ = _ := by rw [← ENNReal.ofReal_mul (by positivity)]
  calc ∫⁻ x, ENNReal.ofReal (|gam (x - s) - gam x| * (1 + x ^ 2) ^ θ)
      = ∫⁻ x, ENNReal.ofReal |gam (x - s) - gam x| * ENNReal.ofReal ((1 + x ^ 2) ^ θ) := by
        refine lintegral_congr fun x => ?_
        rw [ENNReal.ofReal_mul (abs_nonneg _)]
    _ ≤ ∫⁻ x, (ENNReal.ofReal |s| *
          ∫⁻ v in Set.Ioc (0 : ℝ) 1, ENNReal.ofReal (dgam (x - s + v * s))) *
            ENNReal.ofReal ((1 + x ^ 2) ^ θ) := by
        refine lintegral_mono fun x => ?_
        gcongr
        exact ofReal_abs_gam_sub_le x s
    _ = ENNReal.ofReal |s| * ∫⁻ x, ∫⁻ v in Set.Ioc (0 : ℝ) 1,
          ENNReal.ofReal (dgam (x - s + v * s)) * ENNReal.ofReal ((1 + x ^ 2) ^ θ) := by
        rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        refine lintegral_congr fun x => ?_
        rw [mul_assoc, lintegral_mul_const' _ _ ENNReal.ofReal_ne_top]
    _ = ENNReal.ofReal |s| * ∫⁻ v in Set.Ioc (0 : ℝ) 1, ∫⁻ x,
          ENNReal.ofReal (dgam (x - s + v * s)) * ENNReal.ofReal ((1 + x ^ 2) ^ θ) := by
        rw [lintegral_lintegral_swap]
        exact hmeas.aemeasurable
    _ ≤ ENNReal.ofReal |s| * ∫⁻ v in Set.Ioc (0 : ℝ) 1,
          ENNReal.ofReal (2 ^ θ * (1 + s ^ 2) ^ θ * (2 * π ^ 2 * Mg)) := by
        have h := setLIntegral_mono' (μ := volume) measurableSet_Ioc step
        calc _ ≤ ENNReal.ofReal |s| * (∫⁻ v in Set.Ioc (0 : ℝ) 1,
            ENNReal.ofReal (2 ^ θ * (1 + s ^ 2) ^ θ * (2 * π ^ 2 * Mg))) := by gcongr
          _ = _ := rfl
    _ = _ := by
      rw [setLIntegral_const, Real.volume_Ioc]
      simp only [sub_zero, ENNReal.ofReal_one, mul_one]
      rw [ENNReal.ofReal_mul (abs_nonneg _)]

/-- The shifted-Gaussian `L¹` difference bound: weight `(1+x²)^θ`, shift `s`. -/
theorem lintegral_gam_diff_le {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1 / 2) (s : ℝ) :
    ∫⁻ x, ENNReal.ofReal (|gam (x - s) - gam x| * (1 + x ^ 2) ^ θ) ≤
      ENNReal.ofReal (2 ^ θ * (2 * π ^ 2 * Mg) * (1 + s ^ 2) ^ θ * min 1 |s|) := by
  have hM := Mg_nonneg
  have hpi : 1 ≤ π ^ 2 := by nlinarith [Real.pi_gt_three]
  rcases le_total |s| 1 with h | h
  · refine (lintegral_gam_diff_le_two hθ0 hθ1 s).trans (ENNReal.ofReal_le_ofReal ?_)
    rw [min_eq_right h]
    nlinarith [mul_nonneg (mul_nonneg (abs_nonneg s) (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) θ))
      (Real.rpow_nonneg (by positivity : (0 : ℝ) ≤ 1 + s ^ 2) θ), le_refl (2 * π ^ 2 * Mg)]
  · refine (lintegral_gam_diff_le_one hθ0 (by linarith) s).trans (ENNReal.ofReal_le_ofReal ?_)
    rw [min_eq_left h]
    have h2 : 0 ≤ 2 ^ θ * (1 + s ^ 2) ^ θ := by positivity
    nlinarith [mul_nonneg h2 hM, mul_nonneg (mul_nonneg h2 hM) (sub_nonneg.mpr hpi)]

end WaveTurbulence.VineEstS4c.TimeDiff
