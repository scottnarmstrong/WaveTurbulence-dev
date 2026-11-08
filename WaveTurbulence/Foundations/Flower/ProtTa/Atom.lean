/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import Mathlib
public import WaveTurbulence.Foundations.Fourier.SchwartzNorm
public import WaveTurbulence.Foundations.Fourier.TimeBasic
public import WaveTurbulence.Foundations.Sumint.NormIntegralMinkowski

/-! # PROT-TA, atoms: o73 Proposition 5.1 (uniform `A^θ` bound of the one-link kernel)

Convention: Lean's time Fourier transform is `∫ f(t) e^{-2πi λ·t} dt` (`timeFourier`); the source writes `πiλt`, so
the source's `A` is `2z` here. `hz z v = ∫_0^v e^{2πi z w} dw` is the source's `h_z` (with `h_0(v) = v`), and
`psi z (t,s) = Φ(t,s) hz z (t - s)` is the product of the fixed cutoff with `h_z(t-s)`.

* `psi_uniform` (o73 Prop 5.1, for the weight `max⟨λ_i⟩^θ`, `0 ≤ θ ≤ 1`): `sup_z ‖psi z‖_{A^θ} < ∞`.
* `psi_uniform_translate`: uniformly in the layer index `q`.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
open MeasureTheory WaveTurbulence.Fourier
open scoped ENNReal ContDiff

namespace WaveTurbulence.Flower.ProtTa

/-- The source's `h_z(v) = (e^{πizv}-1)/(πiz)`, `h_0(v) = v` (in the `2π` convention), as `∫_0^v e^{2πizw} dw`. -/
def hz (z v : ℝ) : ℂ := ∫ w in (0 : ℝ)..v, Complex.exp (((2 * Real.pi * z * w : ℝ) : ℂ) * Complex.I)

theorem hz_continuous : Continuous (fun p : ℝ × ℝ => hz p.1 p.2) := by
  unfold hz
  exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous (a₀ := 0)
    (f := fun (p : ℝ × ℝ) (w : ℝ) => Complex.exp (((2 * Real.pi * p.1 * w : ℝ) : ℂ) * Complex.I))
    (by fun_prop) continuous_snd

theorem norm_hz_le (z v : ℝ) : ‖hz z v‖ ≤ |v| := by
  unfold hz
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := v) (C := 1)
    (f := fun w : ℝ => Complex.exp (((2 * Real.pi * z * w : ℝ) : ℂ) * Complex.I))
    (fun w _ => by rw [Complex.norm_exp_ofReal_mul_I])
  simpa using h

theorem hz_of_ne {z : ℝ} (hz0 : z ≠ 0) (v : ℝ) :
    hz z v = (Complex.exp (((2 * Real.pi * z * v : ℝ) : ℂ) * Complex.I) - 1) /
      (2 * Real.pi * z * Complex.I) := by
  have hc : (2 * Real.pi * z * Complex.I : ℂ) ≠ 0 := by
    have : (z : ℂ) ≠ 0 := by exact_mod_cast hz0
    simp [Real.pi_ne_zero, this, Complex.I_ne_zero]
  unfold hz
  have h := integral_exp_mul_complex (a := 0) (b := v) hc
  have e : ∀ w : ℝ, Complex.exp (((2 * Real.pi * z * w : ℝ) : ℂ) * Complex.I) =
      Complex.exp ((2 * Real.pi * z * Complex.I : ℂ) * (w : ℂ)) := fun w => by
    congr 1; push_cast; ring
  simp_rw [e]
  rw [h]
  simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero]

theorem hz_eq_mul (z v : ℝ) :
    hz z v = (v : ℂ) * ∫ r in (0 : ℝ)..1,
      Complex.exp (((2 * Real.pi * (z * r) * v : ℝ) : ℂ) * Complex.I) := by
  have h := intervalIntegral.smul_integral_comp_mul_left (a := 0) (b := 1) (c := v)
    (fun w : ℝ => Complex.exp (((2 * Real.pi * z * w : ℝ) : ℂ) * Complex.I))
  simp only [mul_zero, mul_one] at h
  unfold hz
  rw [← h, Complex.real_smul]
  congr 2
  funext r
  congr 3
  ring

/-- The fixed cutoff `Φ`: smooth, compactly supported, equal to one on the unit square `[0,1]²`. -/
def bump : ContDiffBump (![1 / 2, 1 / 2] : Fin 2 → ℝ) := ⟨1 / 2, 1, by norm_num, by norm_num⟩

def Phi (y : Fin 2 → ℝ) : ℂ := ((bump y : ℝ) : ℂ)

theorem Phi_one {y : Fin 2 → ℝ} (h0 : 0 ≤ y 0) (h1 : y 0 ≤ 1) (h2 : 0 ≤ y 1) (h3 : y 1 ≤ 1) :
    Phi y = 1 := by
  unfold Phi
  have : y ∈ Metric.closedBall (![1 / 2, 1 / 2] : Fin 2 → ℝ) bump.rIn := by
    rw [mem_closedBall_iff_norm]
    show ‖y - ![1 / 2, 1 / 2]‖ ≤ 1 / 2
    rw [pi_norm_le_iff_of_nonneg (by norm_num)]
    intro i
    fin_cases i <;> simp [Real.norm_eq_abs, abs_le, bump] <;> constructor <;> linarith
  rw [bump.one_of_mem_closedBall this]
  simp

theorem Phi_contDiff : ContDiff ℝ ∞ Phi :=
  Complex.ofRealCLM.contDiff.comp bump.contDiff

theorem Phi_compact : HasCompactSupport Phi :=
  bump.hasCompactSupport.comp_left Complex.ofReal_zero

theorem Phi_norm_lt_top (θ : ℝ) : timeFourierNorm θ Phi < ⊤ :=
  timeFourierNorm_lt_top_of_smooth_compact θ Phi_compact Phi_contDiff

/-- `χ(t,s) = Φ(t,s)(t-s)`. -/
def chi (y : Fin 2 → ℝ) : ℂ := Phi y * ((y 0 - y 1 : ℝ) : ℂ)

theorem chi_contDiff : ContDiff ℝ ∞ chi :=
  Phi_contDiff.mul (Complex.ofRealCLM.contDiff.comp (by fun_prop : ContDiff ℝ ∞ fun y : Fin 2 → ℝ => y 0 - y 1))

theorem chi_compact : HasCompactSupport chi := Phi_compact.mul_right

theorem chi_norm_lt_top (θ : ℝ) : timeFourierNorm θ chi < ⊤ :=
  timeFourierNorm_lt_top_of_smooth_compact θ chi_compact chi_contDiff

/-- The cutoff atom `ψ_z(t,s) = Φ(t,s) h_z(t-s)`. -/
def psi (z : ℝ) (y : Fin 2 → ℝ) : ℂ := Phi y * hz z (y 0 - y 1)

/-- The frequency vector `(z,-z)` of the character `e^{2πi z (t-s)}`. -/
def sig (z : ℝ) : Fin 2 → ℝ := ![z, -z]

theorem pairing_sig (z : ℝ) (y : Fin 2 → ℝ) : timePairing 2 y (sig z) = z * (y 0 - y 1) := by
  change (∑ i, y i * sig z i) = _
  simp [sig, Fin.sum_univ_two]
  ring

theorem char_smul (a : Fin 2 → ℝ) (y : Fin 2 → ℝ) (c : ℂ) :
    Real.fourierChar (timePairing 2 y a) • c =
      Complex.exp (((2 * Real.pi * timePairing 2 y a : ℝ) : ℂ) * Complex.I) * c := by
  rw [Circle.smul_def, smul_eq_mul, Real.fourierChar_apply]

theorem timeBracket_sig_le {z a : ℝ} (ha : 1 ≤ a) (hz : |z| ≤ a) (h2 : 1 + z ^ 2 ≤ a ^ 2) :
    timeBracket (sig z) ≤ a := by
  apply timeBracket_le ha
  intro j
  apply Real.sqrt_le_iff.mpr
  refine ⟨by linarith, ?_⟩
  fin_cases j <;> simp [sig] <;> linarith

/-- Large `|z|`: `ψ_z = (2πiz)^{-1} (Φ e^{2πiz(t-s)} - Φ)`. -/
theorem psi_large {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) {z : ℝ} (hz1 : 1 ≤ |z|) :
    timeFourierNorm θ (psi z) ≤ timeFourierNorm θ Phi := by
  have hz0 : z ≠ 0 := fun h => by simp [h] at hz1; linarith
  have hform : psi z = fun y => (1 / (2 * Real.pi * z * Complex.I) : ℂ) •
      (Real.fourierChar (timePairing 2 y (sig z)) • Phi y + (-1 : ℂ) • Phi y) := by
    funext y
    rw [char_smul, pairing_sig, psi, hz_of_ne hz0]
    simp only [smul_eq_mul]
    have : ((2 * Real.pi * (z * (y 0 - y 1)) : ℝ) : ℂ) = ((2 * Real.pi * z * (y 0 - y 1) : ℝ) : ℂ) := by
      congr 1; ring
    rw [this]
    ring
  rw [hform, timeFourierNorm_smul]
  have hN := Phi_norm_lt_top θ
  have hmod := timeFourierNorm_modulate_le hθ0 Phi (sig z)
  have hneg : timeFourierNorm θ (fun y => (-1 : ℂ) • Phi y) = timeFourierNorm θ Phi := by
    rw [timeFourierNorm_smul]; simp
  have hadd := timeFourierNorm_add_le θ
    (fun y => Real.fourierChar (timePairing 2 y (sig z)) • Phi y) (fun y => (-1 : ℂ) • Phi y)
  have hw : timeWeight θ (sig z) ≤ ENNReal.ofReal (2 * |z|) := by
    unfold timeWeight
    have hb : timeBracket (sig z) ≤ 2 * |z| := by
      apply timeBracket_sig_le (by linarith) (by linarith [abs_nonneg z])
      nlinarith [sq_abs z]
    calc ENNReal.ofReal (timeBracket (sig z) ^ θ) ≤ ENNReal.ofReal ((2 * |z|) ^ θ) :=
          ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow (timeBracket_pos _).le hb hθ0)
      _ ≤ ENNReal.ofReal (2 * |z|) := by
          apply ENNReal.ofReal_le_ofReal
          calc (2 * |z|) ^ θ ≤ (2 * |z|) ^ (1 : ℝ) :=
                Real.rpow_le_rpow_of_exponent_le (by linarith) hθ1
            _ = 2 * |z| := Real.rpow_one _
  have h2 : (2 : ℝ) ^ θ ≤ 2 := by
    calc (2 : ℝ) ^ θ ≤ (2 : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hθ1
      _ = 2 := Real.rpow_one _
  have hNe : timeFourierNorm θ Phi = ENNReal.ofReal (timeFourierNorm θ Phi).toReal :=
    (ENNReal.ofReal_toReal hN.ne).symm
  have hN0 : 0 ≤ (timeFourierNorm θ Phi).toReal := ENNReal.toReal_nonneg
  generalize (timeFourierNorm θ Phi).toReal = N at hNe hN0
  have hc : ‖(1 / (2 * Real.pi * z * Complex.I) : ℂ)‖ₑ =
      ENNReal.ofReal (1 / (2 * Real.pi * |z|)) := by
    rw [← ofReal_norm]
    congr 1
    simp [norm_div, Real.pi_pos.le, abs_of_pos Real.pi_pos]
  rw [hc]
  calc ENNReal.ofReal (1 / (2 * Real.pi * |z|)) * timeFourierNorm θ (fun y =>
        Real.fourierChar (timePairing 2 y (sig z)) • Phi y + (-1 : ℂ) • Phi y)
      ≤ ENNReal.ofReal (1 / (2 * Real.pi * |z|)) *
        (ENNReal.ofReal (2 ^ θ) * ENNReal.ofReal (2 * |z|) * timeFourierNorm θ Phi +
          timeFourierNorm θ Phi) := by
        apply mul_le_mul_right
        refine hadd.trans ?_
        rw [hneg]
        gcongr
        refine hmod.trans ?_
        gcongr
    _ ≤ timeFourierNorm θ Phi := by
        rw [hNe]
        have hz' : 0 < |z| := by linarith
        rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
          ← ENNReal.ofReal_add (by positivity) hN0, ← ENNReal.ofReal_mul (by positivity)]
        apply ENNReal.ofReal_le_ofReal
        have hpi := Real.pi_gt_three
        have : (2 : ℝ) ^ θ * (2 * |z|) + 1 ≤ 2 * Real.pi * |z| := by
          have h5 : (2 : ℝ) ^ θ * (2 * |z|) ≤ 4 * |z| := by nlinarith [abs_nonneg z]
          nlinarith
        have e : 1 / (2 * Real.pi * |z|) * (2 ^ θ * (2 * |z|) * N + N) =
            ((2 ^ θ * (2 * |z|) + 1) / (2 * Real.pi * |z|)) * N := by
          field_simp
        rw [e]
        have : (2 ^ θ * (2 * |z|) + 1) / (2 * Real.pi * |z|) ≤ 1 :=
          (div_le_one (by positivity)).mpr this
        nlinarith

end WaveTurbulence.Flower.ProtTa
