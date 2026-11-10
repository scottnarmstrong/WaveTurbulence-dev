/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.ProtTa.Atom

/-! # PROT-TA, atoms: the small-`|z|` bound and Proposition 5.1

For `|z| ≤ 1`: `ψ_z = ∫_0^1 χ e^{2πi (zr)(t-s)} dr` with `χ = Φ·(t-s)`, and Minkowski in `A^θ`
(`Sumint.mixedFourierNorm00_integral_le`, `Unit` carrier) bounds it by `4‖χ‖`. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open MeasureTheory WaveTurbulence.Fourier
open scoped ENNReal ContDiff

namespace WaveTurbulence.Flower.ProtTa

theorem psi_eq_integral (z : ℝ) : psi z = fun y =>
    ∫ r, Real.fourierChar (timePairing 2 y (sig (z * r))) • chi y ∂(volume.restrict (Set.Ioc (0 : ℝ) 1)) := by
  funext y
  calc psi z y = chi y * ∫ r in (0 : ℝ)..1,
        Complex.exp (((2 * Real.pi * (z * r) * (y 0 - y 1) : ℝ) : ℂ) * Complex.I) := by
        rw [psi, hz_eq_mul, chi]; ring
    _ = ∫ r in (0 : ℝ)..1, chi y *
        Complex.exp (((2 * Real.pi * (z * r) * (y 0 - y 1) : ℝ) : ℂ) * Complex.I) :=
        (intervalIntegral.integral_const_mul _ _).symm
    _ = _ := by
        rw [intervalIntegral.integral_of_le zero_le_one]
        refine integral_congr_ae (ae_of_all _ fun r => ?_)
        simp only [char_smul, pairing_sig]
        rw [mul_comm]
        congr 3
        ring

theorem psi_small {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) {z : ℝ} (hz1 : |z| ≤ 1) :
    timeFourierNorm θ (psi z) ≤ ENNReal.ofReal 4 * timeFourierNorm θ chi := by
  set μ : Measure ℝ := volume.restrict (Set.Ioc (0 : ℝ) 1) with hμ
  let F : ℝ → (Fin 2 → ℝ) → Unit → ℂ := fun r y _ =>
    Real.fourierChar (timePairing 2 y (sig (z * r))) • chi y
  have hcont : Continuous (fun p : ℝ × (Fin 2 → ℝ) => F p.1 p.2 ()) := by
    simp only [F, char_smul, pairing_sig]
    have := chi_contDiff.continuous
    fun_prop
  have hFm : ∀ v : Unit, Measurable (fun p : ℝ × (Fin 2 → ℝ) => F p.1 p.2 v) :=
    fun _ => hcont.measurable
  have hchi_int : Integrable chi := chi_contDiff.continuous.integrable_of_hasCompactSupport chi_compact
  have hFbd : ∀ (r : ℝ) (y : Fin 2 → ℝ), ‖F r y ()‖ ≤ ‖chi y‖ := fun r y => by
    simp only [F, Circle.norm_smul, le_refl]
  have hFi : ∀ v : Unit, Integrable (fun p : ℝ × (Fin 2 → ℝ) => F p.1 p.2 v) (μ.prod volume) := by
    intro v
    have h1 : Integrable (fun p : ℝ × (Fin 2 → ℝ) => (1 : ℝ) * ‖chi p.2‖) (μ.prod volume) :=
      Integrable.mul_prod (f := fun _ : ℝ => (1 : ℝ)) (g := fun y => ‖chi y‖)
        (integrable_const _) hchi_int.norm
    refine h1.mono' hcont.aestronglyMeasurable ?_
    exact ae_of_all _ fun p => by simpa using hFbd p.1 p.2
  have hFs : ∀ (r : ℝ) (v : Unit), Integrable (fun t => F r t v) volume := by
    intro r v
    refine hchi_int.norm.mono' ?_ (ae_of_all _ fun y => hFbd r y)
    have : Continuous (fun y : Fin 2 → ℝ => F r y ()) := by
      simp only [F, char_smul, pairing_sig]
      have := chi_contDiff.continuous
      fun_prop
    exact this.aestronglyMeasurable
  have hM := Sumint.mixedFourierNorm00_integral_le (μ := μ) θ F hFm hFi hFs
  have hpsi : (fun (t : Fin 2 → ℝ) (_ : Unit) => psi z t) = fun t v => ∫ a, F a t v ∂μ := by
    funext t v
    exact congrFun (psi_eq_integral z) t
  rw [← hpsi, mixedFourierNorm00_unit] at hM
  refine hM.trans ?_
  have hslice : ∀ r ∈ Set.Ioc (0 : ℝ) 1,
      mixedFourierNorm00 θ (F r) ≤ ENNReal.ofReal 4 * timeFourierNorm θ chi := by
    intro r hr
    have : mixedFourierNorm00 θ (F r) = timeFourierNorm θ (fun y => Real.fourierChar (timePairing 2 y (sig (z * r))) • chi y) :=
      mixedFourierNorm00_unit θ _
    rw [this]
    refine (timeFourierNorm_modulate_le hθ0 chi (sig (z * r))).trans ?_
    have hzr : |z * r| ≤ 1 := by
      rw [abs_mul]
      have : |r| ≤ 1 := by rw [abs_of_pos hr.1]; exact hr.2
      nlinarith [abs_nonneg z, abs_nonneg r]
    have hb : timeBracket (sig (z * r)) ≤ 2 := by
      apply timeBracket_sig_le (by norm_num) (by linarith)
      nlinarith [sq_abs (z * r), abs_nonneg (z * r)]
    have h2θ : (2 : ℝ) ^ θ ≤ 2 := by
      calc (2 : ℝ) ^ θ ≤ (2 : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hθ1
        _ = 2 := Real.rpow_one _
    have hw : timeWeight θ (sig (z * r)) ≤ ENNReal.ofReal 2 := by
      unfold timeWeight
      apply ENNReal.ofReal_le_ofReal
      exact (Real.rpow_le_rpow (timeBracket_pos _).le hb hθ0).trans h2θ
    calc ENNReal.ofReal (2 ^ θ) * timeWeight θ (sig (z * r)) * timeFourierNorm θ chi
        ≤ ENNReal.ofReal 2 * ENNReal.ofReal 2 * timeFourierNorm θ chi := by
          gcongr
      _ = ENNReal.ofReal 4 * timeFourierNorm θ chi := by
          rw [← ENNReal.ofReal_mul (by norm_num)]; norm_num
  calc ∫⁻ a, mixedFourierNorm00 θ (F a) ∂μ ≤ ∫⁻ _, ENNReal.ofReal 4 * timeFourierNorm θ chi ∂μ := by
        apply lintegral_mono_ae
        rw [hμ, ae_restrict_iff' measurableSet_Ioc]
        exact ae_of_all _ hslice
    _ = ENNReal.ofReal 4 * timeFourierNorm θ chi := by
        rw [lintegral_const, hμ, Measure.restrict_apply MeasurableSet.univ]
        simp

/-- **o73 Proposition 5.1** (uniform `A^θ` bound of the one-link kernel with its fixed cutoff), `0 ≤ θ ≤ 1`:
`sup_z ‖Φ · h_z(t - s)‖_{A^θ} < ∞`. -/
theorem psi_uniform {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    ∃ B : ℝ≥0∞, B < ⊤ ∧ ∀ z : ℝ, timeFourierNorm θ (psi z) ≤ B := by
  refine ⟨max (timeFourierNorm θ Phi) (ENNReal.ofReal 4 * timeFourierNorm θ chi),
    max_lt (Phi_norm_lt_top θ) (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (chi_norm_lt_top θ)), fun z => ?_⟩
  by_cases h : 1 ≤ |z|
  · exact (psi_large hθ0 hθ1 h).trans (le_max_left _ _)
  · exact (psi_small hθ0 hθ1 (not_le.mp h).le).trans (le_max_right _ _)

end WaveTurbulence.Flower.ProtTa
