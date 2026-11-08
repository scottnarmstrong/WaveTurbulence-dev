/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.ProtTa.Atom
public import WaveTurbulence.Foundations.Flower.ProtPin.Tensor2

/-! # PROT-PIN (D3-KINK): integration by parts against a character; the cutoff `Ψ₀`

* `ibp_cexp`, `norm_ibp_le`: `∫_0^R φ e^{av} = -(φ(0) + ∫_0^R φ' e^{av})/a` when `φ(R) = 0`.
* `Psi0`: the fixed one-time cutoff, smooth, `= 1` on `[-1,1]`, `= 0` off `(-2,2)`; `Psi1 = Ψ₀'`, `Psi2 = Ψ₀''`.
* `ez z w = e^{2πizw}` (the integrand of `ProtTa.hz`), `ea λ = -2πiλ` (the transform's character `e^{-2πiλv}`).
* `Jf μ = ∫_0^3 Ψ₀(v) e^{-2πiμv} dv`: `‖Jf μ‖ ≤ 3` and `2π|μ| ‖Jf μ‖ ≤ C2` (one integration by parts). -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open MeasureTheory WaveTurbulence.Fourier
open scoped ENNReal ContDiff

namespace WaveTurbulence.Flower.ProtPin

theorem hasDerivAt_cexp_div {a : ℂ} (ha : a ≠ 0) (x : ℝ) :
    HasDerivAt (fun v : ℝ => Complex.exp (a * v) / a) (Complex.exp (a * x)) x := by
  have h1 : HasDerivAt (fun v : ℝ => a * (v : ℂ)) a x := by
    simpa using ((hasDerivAt_id x).ofReal_comp).const_mul a
  have h2 := (h1.cexp).div_const a
  convert h2 using 1
  field_simp

/-- One integration by parts against `e^{av}` on `[0, R]`, the profile vanishing at `R`. -/
theorem ibp_cexp {φ φ' : ℝ → ℂ} {R : ℝ} {a : ℂ} (ha : a ≠ 0)
    (hd : ∀ x, HasDerivAt φ (φ' x) x) (hc : Continuous φ') (hR : φ R = 0) :
    ∫ x in (0:ℝ)..R, φ x * Complex.exp (a * x) =
      -(φ 0 + ∫ x in (0:ℝ)..R, φ' x * Complex.exp (a * x)) / a := by
  have h : ∫ x in (0:ℝ)..R, φ x * Complex.exp (a * x) =
      φ R * (Complex.exp (a * R) / a) - φ 0 * (Complex.exp (a * ((0:ℝ) : ℂ)) / a) -
        ∫ x in (0:ℝ)..R, φ' x * (Complex.exp (a * x) / a) :=
    intervalIntegral.integral_mul_deriv_eq_deriv_mul (fun x _ => hd x)
      (fun x _ => hasDerivAt_cexp_div ha x) (hc.intervalIntegrable _ _)
      ((by fun_prop : Continuous fun v : ℝ => Complex.exp (a * v)).intervalIntegrable _ _)
  have h2 : ∫ x in (0:ℝ)..R, φ' x * (Complex.exp (a * x) / a) =
      (∫ x in (0:ℝ)..R, φ' x * Complex.exp (a * x)) / a := by
    rw [← intervalIntegral.integral_div]
    congr 1
    funext x
    ring
  rw [h, h2, hR]
  simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero, zero_mul]
  field_simp
  ring

theorem norm_ibp_le {φ φ' : ℝ → ℂ} {R : ℝ} {a : ℂ} (ha : a ≠ 0)
    (hd : ∀ x, HasDerivAt φ (φ' x) x) (hc : Continuous φ') (hR : φ R = 0) :
    ‖a‖ * ‖∫ x in (0:ℝ)..R, φ x * Complex.exp (a * x)‖ ≤
      ‖φ 0‖ + ‖∫ x in (0:ℝ)..R, φ' x * Complex.exp (a * x)‖ := by
  rw [ibp_cexp ha hd hc hR, norm_div, norm_neg, mul_div_cancel₀ _ (norm_ne_zero_iff.mpr ha)]
  exact norm_add_le _ _

/-! ### The cutoff -/

/-- The bump behind `Ψ₀`. -/
def bump0 : ContDiffBump (0 : ℝ) := ⟨1, 2, by norm_num, by norm_num⟩

/-- The fixed one-time cutoff `Ψ₀`: smooth, equal to one on `[-1,1]`, vanishing off `(-2,2)`. -/
def Psi0 (v : ℝ) : ℂ := ((bump0 v : ℝ) : ℂ)

theorem Psi0_contDiff : ContDiff ℝ ∞ Psi0 :=
  Complex.ofRealCLM.contDiff.comp bump0.contDiff

theorem Psi0_continuous : Continuous Psi0 := Psi0_contDiff.continuous

theorem Psi0_one {v : ℝ} (h : |v| ≤ 1) : Psi0 v = 1 := by
  unfold Psi0
  rw [bump0.one_of_mem_closedBall]
  · simp
  · rw [Metric.mem_closedBall, Real.dist_eq, sub_zero]
    exact h

theorem Psi0_zero {v : ℝ} (h : 2 ≤ |v|) : Psi0 v = 0 := by
  unfold Psi0
  rw [bump0.zero_of_le_dist]
  · simp
  · rw [Real.dist_eq, sub_zero]
    exact h

theorem Psi0_at_zero : Psi0 0 = 1 := Psi0_one (by simp)

theorem Psi0_at_three : Psi0 3 = 0 := Psi0_zero (by norm_num)

theorem norm_Psi0_le (v : ℝ) : ‖Psi0 v‖ ≤ 1 := by
  unfold Psi0
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg bump0.nonneg]
  exact bump0.le_one

theorem Psi0_compact : HasCompactSupport Psi0 :=
  bump0.hasCompactSupport.comp_left Complex.ofReal_zero

/-- `Ψ₀'`. -/
def Psi1 : ℝ → ℂ := deriv Psi0

/-- `Ψ₀''`. -/
def Psi2 : ℝ → ℂ := deriv Psi1

theorem Psi1_contDiff : ContDiff ℝ ∞ Psi1 := (contDiff_infty_iff_deriv.mp Psi0_contDiff).2

theorem Psi2_contDiff : ContDiff ℝ ∞ Psi2 := (contDiff_infty_iff_deriv.mp Psi1_contDiff).2

theorem hasDerivAt_Psi0 (x : ℝ) : HasDerivAt Psi0 (Psi1 x) x :=
  ((contDiff_infty_iff_deriv.mp Psi0_contDiff).1 x).hasDerivAt

theorem hasDerivAt_Psi1 (x : ℝ) : HasDerivAt Psi1 (Psi2 x) x :=
  ((contDiff_infty_iff_deriv.mp Psi1_contDiff).1 x).hasDerivAt

theorem Psi1_zero_of_gt {x : ℝ} (hx : 2 < x) : Psi1 x = 0 := by
  have h : Psi0 =ᶠ[nhds x] fun _ => 0 := by
    filter_upwards [Ioi_mem_nhds hx] with y hy
    have hy' : (2 : ℝ) < y := hy
    exact Psi0_zero (by rw [abs_of_pos (by linarith)]; linarith)
  unfold Psi1
  rw [h.deriv_eq, deriv_const]

theorem Psi1_at_three : Psi1 3 = 0 := Psi1_zero_of_gt (by norm_num)

/-! ### Characters -/

/-- The integrand of `h_z`: `e^{2πizw}`. -/
def ez (z w : ℝ) : ℂ := Complex.exp (((2 * Real.pi * z * w : ℝ) : ℂ) * Complex.I)

theorem ez_continuous (z : ℝ) : Continuous (ez z) := by
  unfold ez
  fun_prop

theorem norm_ez (z w : ℝ) : ‖ez z w‖ = 1 := Complex.norm_exp_ofReal_mul_I _

theorem hasDerivAt_hz (z x : ℝ) : HasDerivAt (ProtTa.hz z) (ez z x) x :=
  ((ez_continuous z).integral_hasStrictDerivAt 0 x).hasDerivAt

theorem hz_at_zero (z : ℝ) : ProtTa.hz z 0 = 0 := by
  simp [ProtTa.hz]

/-- The coefficient `-2πiλ` of the transform's character `e^{-2πiλv}`. -/
def ea (l : ℝ) : ℂ := -2 * Real.pi * l * Complex.I

theorem cexp_ea (l v : ℝ) :
    Complex.exp (ea l * v) = Complex.exp (((-2 * Real.pi * l * v : ℝ) : ℂ) * Complex.I) := by
  unfold ea
  congr 1
  push_cast
  ring

theorem norm_cexp_ea (l v : ℝ) : ‖Complex.exp (ea l * v)‖ = 1 := by
  rw [cexp_ea]
  exact Complex.norm_exp_ofReal_mul_I _

theorem norm_ea (l : ℝ) : ‖ea l‖ = 2 * Real.pi * |l| := by
  unfold ea
  rw [norm_mul, norm_mul, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Complex.norm_real,
    Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  norm_num

theorem ea_ne_zero {l : ℝ} (hl : l ≠ 0) : ea l ≠ 0 := by
  unfold ea
  have : (l : ℂ) ≠ 0 := by exact_mod_cast hl
  simp [this, Real.pi_ne_zero, Complex.I_ne_zero]

theorem ez_mul_cexp_ea (z l v : ℝ) :
    ez z v * Complex.exp (ea l * v) = Complex.exp (ea (l - z) * v) := by
  unfold ez ea
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

/-! ### `J(μ) = ∫_0^3 Ψ₀(v) e^{-2πiμv} dv` -/

/-- `J(μ) = ∫_0^3 Ψ₀(v) e^{-2πiμv} dv`. -/
def Jf (μ : ℝ) : ℂ := ∫ v in (0:ℝ)..3, Psi0 v * Complex.exp (ea μ * v)

theorem norm_Jf_le (μ : ℝ) : ‖Jf μ‖ ≤ 3 := by
  unfold Jf
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := 3) (C := 1)
    (f := fun v => Psi0 v * Complex.exp (ea μ * v))
    (fun v _ => by rw [norm_mul, norm_cexp_ea, mul_one]; exact norm_Psi0_le v)
  norm_num at h
  exact h

/-- `C2 = 1 + ∫_0^3 |Ψ₀'|`. -/
def C2 : ℝ := 1 + ∫ v in (0:ℝ)..3, ‖Psi1 v‖

theorem C2_pos : 0 < C2 := by
  unfold C2
  have : 0 ≤ ∫ v in (0:ℝ)..3, ‖Psi1 v‖ :=
    intervalIntegral.integral_nonneg (by norm_num) (fun _ _ => norm_nonneg _)
  linarith

theorem mul_norm_Jf_le (μ : ℝ) : 2 * Real.pi * |μ| * ‖Jf μ‖ ≤ C2 := by
  by_cases hμ : μ = 0
  · subst hμ
    simp only [abs_zero, mul_zero, zero_mul]
    exact C2_pos.le
  have h := norm_ibp_le (R := 3) (ea_ne_zero hμ) hasDerivAt_Psi0 Psi1_contDiff.continuous Psi0_at_three
  rw [norm_ea] at h
  unfold Jf
  refine h.trans ?_
  unfold C2
  rw [Psi0_at_zero, norm_one]
  gcongr
  refine (intervalIntegral.norm_integral_le_integral_norm (by norm_num)).trans (le_of_eq ?_)
  congr 1
  funext v
  rw [norm_mul, norm_cexp_ea, mul_one]

end WaveTurbulence.Flower.ProtPin
