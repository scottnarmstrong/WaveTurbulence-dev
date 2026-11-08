/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Sumint.TensorScalarMass
public import WaveTurbulence.Foundations.Regref.FourierAE
public import WaveTurbulence.Foundations.Flower.ProtTa.Congr

/-! # PROT-PIN (D3-KINK): the tensor of two one-time functions

`timeFourierNorm_tensor2_le`: `‖f ⊗ g‖_{A^θ(ℝ²)} ≤ ‖f‖_{A^θ(ℝ)} ‖g‖_{A^θ(ℝ)}` for `θ ≥ 0`, with no further
hypothesis. Fubini factorizes the transform (`timeFourier_coordinate_product`), and
`max(1, ⟨λ₀⟩, ⟨λ₁⟩)^θ ≤ ⟨λ₀⟩^θ ⟨λ₁⟩^θ`. The degenerate cases: a zero norm forces an a.e. zero factor (Fourier
inversion), hence an a.e. zero tensor; an infinite norm against a nonzero one makes the right side infinite. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open MeasureTheory WaveTurbulence.Fourier
open scoped ENNReal FourierTransform

namespace WaveTurbulence.Flower.ProtPin

/-- `A^θ` norms only see almost everywhere classes. -/
theorem timeFourierNorm_congr_ae {r : ℕ} {θ : ℝ} {f g : (Fin r → ℝ) → ℂ} (h : f =ᵐ[volume] g) :
    timeFourierNorm θ f = timeFourierNorm θ g := by
  by_cases hf : Integrable f
  · have hg : Integrable g := (integrable_congr h).mp hf
    rw [timeFourierNorm_eq_lintegral hf, timeFourierNorm_eq_lintegral hg, ProtTa.timeFourier_congr_ae h]
  · have hg : ¬ Integrable g := fun hg => hf ((integrable_congr h).mpr hg)
    rw [timeFourierNorm_of_not_integrable hf, timeFourierNorm_of_not_integrable hg]

/-- A zero `A^θ` norm forces an almost everywhere zero function. -/
theorem ae_eq_zero_of_timeFourierNorm_eq_zero {r : ℕ} {θ : ℝ} {f : (Fin r → ℝ) → ℂ}
    (h : timeFourierNorm θ f = 0) : f =ᵐ[volume] fun _ => 0 := by
  have hfi : Integrable f := by
    by_contra hn
    rw [timeFourierNorm_of_not_integrable hn] at h
    exact ENNReal.top_ne_zero h
  have hm : Measurable (fun ξ => timeWeight θ ξ * ‖timeFourier f ξ‖ₑ) :=
    (timeWeight_measurable θ).mul (timeFourier_continuous hfi).measurable.enorm
  rw [timeFourierNorm_eq_lintegral hfi, lintegral_eq_zero_iff hm] at h
  have hz : timeFourier f =ᵐ[volume] fun _ => 0 := by
    filter_upwards [h] with ξ hξ
    have hw : timeWeight θ ξ ≠ 0 := by
      unfold timeWeight
      exact (ENNReal.ofReal_pos.mpr (Real.rpow_pos_of_pos (timeBracket_pos ξ) θ)).ne'
    have h1 : timeWeight θ ξ * ‖timeFourier f ξ‖ₑ = 0 := hξ
    exact enorm_eq_zero.mp ((mul_eq_zero.mp h1).resolve_left hw)
  have hhat : Integrable (timeFourier f) := (integrable_congr hz).mpr (integrable_zero _ _ _)
  filter_upwards [Regref.timeFourier_inversion_ae hfi hhat] with t ht
  rw [← ht, ProtTa.timeFourier_congr_ae hz, timeFourier_zero]
  rfl

/-- The constant embedding `ℝ → (Fin 1 → ℝ)` preserves volume. -/
theorem measurePreserving_const_one :
    MeasurePreserving (fun x : ℝ => (fun _ : Fin 1 => x)) volume volume := by
  have he : (fun x : ℝ => (fun _ : Fin 1 => x)) = (MeasurableEquiv.funUnique (Fin 1) ℝ).symm := by
    funext x i
    rw [Fin.fin_one_eq_zero i]
    rfl
  rw [he]
  exact (volume_preserving_funUnique (Fin 1) ℝ).symm

/-- The tensor with an a.e. zero left factor is a.e. zero. -/
theorem tensor2_ae_zero_left {f : (Fin 1 → ℝ) → ℂ} (g : (Fin 1 → ℝ) → ℂ) (hf : f =ᵐ[volume] fun _ => 0) :
    (fun t : Fin 2 → ℝ => f (fun _ => t 0) * g (fun _ => t 1)) =ᵐ[volume] fun _ => 0 := by
  have h1 : (fun x : ℝ => f (fun _ => x)) =ᵐ[volume] fun _ => 0 :=
    measurePreserving_const_one.quasiMeasurePreserving.ae_eq_comp hf
  have h2 := h1.comp_tendsto (Measure.tendsto_eval_ae_ae (μ := fun _ : Fin 2 => (volume : Measure ℝ))
    (i := 0))
  filter_upwards [h2] with t ht
  simp only [Function.comp_apply, Function.eval] at ht
  rw [ht, zero_mul]

/-- The tensor with an a.e. zero right factor is a.e. zero. -/
theorem tensor2_ae_zero_right (f : (Fin 1 → ℝ) → ℂ) {g : (Fin 1 → ℝ) → ℂ} (hg : g =ᵐ[volume] fun _ => 0) :
    (fun t : Fin 2 → ℝ => f (fun _ => t 0) * g (fun _ => t 1)) =ᵐ[volume] fun _ => 0 := by
  have h1 : (fun x : ℝ => g (fun _ => x)) =ᵐ[volume] fun _ => 0 :=
    measurePreserving_const_one.quasiMeasurePreserving.ae_eq_comp hg
  have h2 := h1.comp_tendsto (Measure.tendsto_eval_ae_ae (μ := fun _ : Fin 2 => (volume : Measure ℝ))
    (i := 1))
  filter_upwards [h2] with t ht
  simp only [Function.comp_apply, Function.eval] at ht
  rw [ht, mul_zero]

/-- The two-time maximal bracket weight is at most the product of the coordinate weights. -/
theorem timeWeight_two_le {θ : ℝ} (hθ : 0 ≤ θ) (ξ : Fin 2 → ℝ) :
    timeWeight θ ξ ≤ ENNReal.ofReal (Sumint.scalarBracket (ξ 0) ^ θ) *
      ENNReal.ofReal (Sumint.scalarBracket (ξ 1) ^ θ) := by
  have h := Sumint.timeBracket_le_scalarBracket_product ξ
  rw [Fin.prod_univ_two] at h
  have h0 : 0 ≤ Sumint.scalarBracket (ξ 0) := zero_le_one.trans (Sumint.one_le_scalarBracket _)
  have h1 : 0 ≤ Sumint.scalarBracket (ξ 1) := zero_le_one.trans (Sumint.one_le_scalarBracket _)
  unfold timeWeight
  rw [← ENNReal.ofReal_mul (Real.rpow_nonneg h0 _), ← Real.mul_rpow h0 h1]
  exact ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow (timeBracket_pos ξ).le h hθ)

/-- The one-time norm of a lifted scalar function, as a scalar weighted Fourier mass. -/
theorem lintegral_lift_one (θ : ℝ) (φ : ℝ → ℂ) :
    ∫⁻ ξ : Fin 1 → ℝ, timeWeight θ ξ * ‖timeFourier (fun t : Fin 1 → ℝ => φ (t 0)) ξ‖ₑ =
      ∫⁻ x : ℝ, ENNReal.ofReal (Sumint.scalarBracket x ^ θ) * ‖𝓕 φ x‖ₑ := by
  simp_rw [Sumint.timeFourier_scalar_lift, timeWeight, Sumint.timeBracket_one_eq]
  exact (volume_preserving_funUnique (Fin 1) ℝ).lintegral_comp_emb
    (MeasurableEquiv.funUnique (Fin 1) ℝ).measurableEmbedding
    (fun x : ℝ => ENNReal.ofReal (Sumint.scalarBracket x ^ θ) * ‖𝓕 φ x‖ₑ)

theorem eq_lift_one (f : (Fin 1 → ℝ) → ℂ) : f = fun t => (fun x : ℝ => f (fun _ => x)) (t 0) := by
  funext t
  congr 1
  funext i
  rw [Fin.fin_one_eq_zero i]

/-- The one-time norm of an integrable function as a scalar weighted Fourier mass. -/
theorem timeFourierNorm_one_eq {θ : ℝ} {f : (Fin 1 → ℝ) → ℂ} (hf : Integrable f) :
    timeFourierNorm θ f =
      ∫⁻ x : ℝ, ENNReal.ofReal (Sumint.scalarBracket x ^ θ) * ‖𝓕 (fun y : ℝ => f (fun _ => y)) x‖ₑ := by
  rw [timeFourierNorm_eq_lintegral hf, ← lintegral_lift_one θ (fun y : ℝ => f (fun _ => y))]
  conv_lhs => rw [eq_lift_one f]

theorem integrable_lift_one {f : (Fin 1 → ℝ) → ℂ} (hf : Integrable f) :
    Integrable (fun x : ℝ => f (fun _ => x)) :=
  measurePreserving_const_one.integrable_comp_of_integrable hf

theorem measurable_fourier_real {φ : ℝ → ℂ} (hφ : Integrable φ) : Measurable (𝓕 φ) :=
  (VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar (innerSL ℝ).continuous₂
    hφ).measurable

/-- **(1) Tensor of two one-time functions.** -/
theorem timeFourierNorm_tensor2_le {θ : ℝ} (hθ : 0 ≤ θ) (f g : (Fin 1 → ℝ) → ℂ) :
    timeFourierNorm θ (fun t : Fin 2 → ℝ => f (fun _ => t 0) * g (fun _ => t 1)) ≤
      timeFourierNorm θ f * timeFourierNorm θ g := by
  by_cases hf0 : timeFourierNorm θ f = 0
  · rw [timeFourierNorm_congr_ae (tensor2_ae_zero_left g (ae_eq_zero_of_timeFourierNorm_eq_zero hf0)),
      timeFourierNorm_zero]
    exact bot_le
  by_cases hg0 : timeFourierNorm θ g = 0
  · rw [timeFourierNorm_congr_ae (tensor2_ae_zero_right f (ae_eq_zero_of_timeFourierNorm_eq_zero hg0)),
      timeFourierNorm_zero]
    exact bot_le
  by_cases hft : timeFourierNorm θ f = ⊤
  · rw [hft, ENNReal.top_mul hg0]
    exact le_top
  by_cases hgt : timeFourierNorm θ g = ⊤
  · rw [hgt, ENNReal.mul_top hf0]
    exact le_top
  have hfi := integrable_of_timeFourierNorm_lt_top (lt_top_iff_ne_top.mpr hft)
  have hgi := integrable_of_timeFourierNorm_lt_top (lt_top_iff_ne_top.mpr hgt)
  rw [timeFourierNorm_one_eq hfi, timeFourierNorm_one_eq hgi]
  have hφ := integrable_lift_one hfi
  have hψ := integrable_lift_one hgi
  set φ : ℝ → ℂ := fun y => f (fun _ => y) with hφdef
  set ψ : ℝ → ℂ := fun y => g (fun _ => y) with hψdef
  let F : Fin 2 → ℝ → ℂ := ![φ, ψ]
  have hL : (fun t : Fin 2 → ℝ => f (fun _ => t 0) * g (fun _ => t 1)) = fun t => ∏ j, F j (t j) := by
    funext t
    simp [F, Fin.prod_univ_two, hφdef, hψdef]
  have hFi : ∀ j, Integrable (F j) := by
    intro j
    fin_cases j
    · exact hφ
    · exact hψ
  have hi : Integrable (fun t : Fin 2 → ℝ => ∏ j, F j (t j)) := Integrable.fintype_prod hFi
  rw [hL, timeFourierNorm_eq_lintegral hi]
  have hb : Measurable (fun x : ℝ => ENNReal.ofReal (Sumint.scalarBracket x ^ θ)) := by
    have : Continuous Sumint.scalarBracket := by unfold Sumint.scalarBracket; fun_prop
    exact (this.measurable.pow_const θ).ennreal_ofReal
  let W : Fin 2 → ℝ → ℝ≥0∞ := ![fun x => ENNReal.ofReal (Sumint.scalarBracket x ^ θ) * ‖𝓕 φ x‖ₑ,
    fun x => ENNReal.ofReal (Sumint.scalarBracket x ^ θ) * ‖𝓕 ψ x‖ₑ]
  have hWm : ∀ j, Measurable (W j) := by
    intro j
    fin_cases j
    · exact hb.mul (measurable_fourier_real hφ).enorm
    · exact hb.mul (measurable_fourier_real hψ).enorm
  calc ∫⁻ ξ, timeWeight θ ξ * ‖timeFourier (fun t : Fin 2 → ℝ => ∏ j, F j (t j)) ξ‖ₑ
      ≤ ∫⁻ ξ : Fin 2 → ℝ, ∏ j, W j (ξ j) := by
        refine lintegral_mono fun ξ => ?_
        rw [timeFourier_coordinate_product, Fin.prod_univ_two, Fin.prod_univ_two, enorm_mul]
        simp only [F, W, Matrix.cons_val_zero, Matrix.cons_val_one]
        calc timeWeight θ ξ * (‖𝓕 φ (ξ 0)‖ₑ * ‖𝓕 ψ (ξ 1)‖ₑ)
            ≤ (ENNReal.ofReal (Sumint.scalarBracket (ξ 0) ^ θ) *
                ENNReal.ofReal (Sumint.scalarBracket (ξ 1) ^ θ)) * (‖𝓕 φ (ξ 0)‖ₑ * ‖𝓕 ψ (ξ 1)‖ₑ) := by
              gcongr
              exact timeWeight_two_le hθ ξ
          _ = _ := by ring
    _ = _ := by
        refine (Sumint.lintegral_fintype_prod_eq_prod (Fin 2) (μ := fun _ => volume) W hWm).trans ?_
        rw [Fin.prod_univ_two]
        rfl

end WaveTurbulence.Flower.ProtPin
