/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.ProtTa.Congr
public import WaveTurbulence.Foundations.Sumint.TimeBridge
public import WaveTurbulence.Foundations.Fourier.TimeProduct
public import WaveTurbulence.Foundations.Fourier.Norm00V
public import WaveTurbulence.Foundations.Sumint.FourierFubini
public import WaveTurbulence.Foundations.Sumint.ParametricFourierMeasurability

/-! # PROT-OPS: Fourier synthesis `G(y,k) = ∫ ĥ_k(l) atom(l)(y) dl` and its norm (generic form of PROT-TA Synth)

For `H` of finite `𝔛^{θ,0,0}` norm and a continuous family of atoms `atom l` with a common integrable majorant `Ψ` and
`‖atom l‖_{A^θ} ≤ Cw · w_θ(l)`, the synthesized output has `mixedFourierNorm00 θ (synth atom H) ≤ Cw ‖H‖`. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open MeasureTheory WaveTurbulence.Fourier
open scoped ENNReal ContDiff

namespace WaveTurbulence.Flower.ProtOps

variable {n p : ℕ} {V : Type*}

/-- The synthesized output. -/
def synth (atom : (Fin n → ℝ) → (Fin p → ℝ) → ℂ) (H : (Fin n → ℝ) → V → ℂ) (y : Fin p → ℝ) (k : V) : ℂ :=
  ∫ l, timeFourier (fun t => H t k) l * atom l y

variable {atom : (Fin n → ℝ) → (Fin p → ℝ) → ℂ} {H : (Fin n → ℝ) → V → ℂ}

theorem synth_prod_integrable (hc : Continuous (fun q : (Fin n → ℝ) × (Fin p → ℝ) => atom q.1 q.2))
    {Ψ : (Fin p → ℝ) → ℝ} (hΨ : Integrable Ψ) (hbd : ∀ l y, ‖atom l y‖ ≤ Ψ y)
    (hk : ∀ k, Integrable (fun t => H t k))
    (hhat : ∀ k, Integrable (timeFourier fun t => H t k)) (k : V) :
    Integrable (fun q : (Fin n → ℝ) × (Fin p → ℝ) =>
      timeFourier (fun t => H t k) q.1 * atom q.1 q.2) (volume.prod volume) := by
  have h1 : Integrable (fun q : (Fin n → ℝ) × (Fin p → ℝ) =>
      ‖timeFourier (fun t => H t k) q.1‖ * Ψ q.2) (volume.prod volume) :=
    Integrable.mul_prod (f := fun l => ‖timeFourier (fun t => H t k) l‖) (g := Ψ) (hhat k).norm hΨ
  refine h1.mono' ?_ (ae_of_all _ fun q => ?_)
  · exact (((timeFourier_continuous (hk k)).comp continuous_fst).mul hc).aestronglyMeasurable
  · simp only [norm_mul]
    exact mul_le_mul_of_nonneg_left (hbd _ _) (norm_nonneg _)

theorem atom_integrable_of_bound (hc : Continuous (fun q : (Fin n → ℝ) × (Fin p → ℝ) => atom q.1 q.2))
    {Ψ : (Fin p → ℝ) → ℝ} (hΨ : Integrable Ψ) (hbd : ∀ l y, ‖atom l y‖ ≤ Ψ y) (l : Fin n → ℝ) :
    Integrable (atom l) := by
  refine hΨ.mono' ?_ (ae_of_all _ fun y => hbd l y)
  exact (hc.comp (by fun_prop : Continuous fun y : Fin p → ℝ => (l, y))).aestronglyMeasurable

theorem synth_integrable (hc : Continuous (fun q : (Fin n → ℝ) × (Fin p → ℝ) => atom q.1 q.2))
    {Ψ : (Fin p → ℝ) → ℝ} (hΨ : Integrable Ψ) (hbd : ∀ l y, ‖atom l y‖ ≤ Ψ y)
    (hk : ∀ k, Integrable (fun t => H t k))
    (hhat : ∀ k, Integrable (timeFourier fun t => H t k)) (k : V) :
    Integrable (fun y => synth atom H y k) :=
  (synth_prod_integrable hc hΨ hbd hk hhat k).integral_prod_right

theorem timeFourier_synth (hc : Continuous (fun q : (Fin n → ℝ) × (Fin p → ℝ) => atom q.1 q.2))
    {Ψ : (Fin p → ℝ) → ℝ} (hΨ : Integrable Ψ) (hbd : ∀ l y, ‖atom l y‖ ≤ Ψ y)
    (hk : ∀ k, Integrable (fun t => H t k))
    (hhat : ∀ k, Integrable (timeFourier fun t => H t k)) (k : V) (m : Fin p → ℝ) :
    timeFourier (fun y => synth atom H y k) m =
      ∫ l, timeFourier (fun t => H t k) l * timeFourier (atom l) m := by
  have h := Sumint.timeFourier_integral (μ := (volume : Measure (Fin n → ℝ)))
    (fun l y => timeFourier (fun t => H t k) l * atom l y) (synth_prod_integrable hc hΨ hbd hk hhat k) m
  refine h.trans (integral_congr_ae (ae_of_all _ fun l => ?_))
  exact congrFun (timeFourier_smul (timeFourier (fun t => H t k) l) (atom l)) m

theorem envelope_synth_le (hc : Continuous (fun q : (Fin n → ℝ) × (Fin p → ℝ) => atom q.1 q.2))
    {Ψ : (Fin p → ℝ) → ℝ} (hΨ : Integrable Ψ) (hbd : ∀ l y, ‖atom l y‖ ≤ Ψ y)
    (hk : ∀ k, Integrable (fun t => H t k))
    (hhat : ∀ k, Integrable (timeFourier fun t => H t k)) (m : Fin p → ℝ) :
    mixedFourierEnvelope00 (synth atom H) m ≤
      ∫⁻ l, mixedFourierEnvelope00 H l * ‖timeFourier (atom l) m‖ₑ := by
  refine iSup_le fun k => ?_
  change ‖timeFourier (fun y => synth atom H y k) m‖ₑ ≤ _
  rw [timeFourier_synth hc hΨ hbd hk hhat k m]
  refine (enorm_integral_le_lintegral_enorm _).trans (lintegral_mono fun l => ?_)
  rw [enorm_mul]
  exact mul_le_mul_left (le_iSup (fun k => ‖timeFourier (fun t => H t k) l‖ₑ) k) _

theorem synth_norm_le {θ : ℝ} (hθ0 : 0 ≤ θ)
    (hc : Continuous (fun q : (Fin n → ℝ) × (Fin p → ℝ) => atom q.1 q.2))
    {Ψ : (Fin p → ℝ) → ℝ} (hΨ : Integrable Ψ) (hbd : ∀ l y, ‖atom l y‖ ≤ Ψ y)
    {Cw : ℝ≥0∞} (hCw : ∀ l, timeFourierNorm θ (atom l) ≤ Cw * timeWeight θ l)
    (hH : mixedFourierNorm00 θ H < ⊤) :
    mixedFourierNorm00 θ (synth atom H) ≤ Cw * mixedFourierNorm00 θ H := by
  have hk : ∀ k, Integrable (fun t => H t k) := integrable_of_mixedFourierNorm00_lt_top hH
  have hhat : ∀ k, Integrable (timeFourier fun t => H t k) := fun k =>
    integrable_timeFourier_of_norm_lt_top hθ0
      ((timeFourierNorm_slice_le_mixedFourierNorm00 θ H k).trans_lt hH)
  have hG : ∀ k, Integrable (fun y => synth atom H y k) := synth_integrable hc hΨ hbd hk hhat
  have hMm : Measurable (mixedFourierEnvelope00 H) := measurable_mixedFourierEnvelope00 hk
  have hAm : Measurable (fun q : (Fin p → ℝ) × (Fin n → ℝ) => ‖timeFourier (atom q.2) q.1‖ₑ) := by
    have := Sumint.measurable_parametric_timeFourier (fun (l : Fin n → ℝ) (y : Fin p → ℝ) => atom l y)
      hc.measurable
    exact (this.comp measurable_swap).enorm
  rw [mixedFourierNorm00_eq_lintegral hG]
  have step1 : ∫⁻ m, timeWeight θ m * mixedFourierEnvelope00 (synth atom H) m ≤
      ∫⁻ m, ∫⁻ l, timeWeight θ m * (mixedFourierEnvelope00 H l * ‖timeFourier (atom l) m‖ₑ) := by
    refine lintegral_mono fun m => ?_
    rw [lintegral_const_mul' (timeWeight θ m) _ ENNReal.ofReal_ne_top]
    exact mul_le_mul_right (envelope_synth_le hc hΨ hbd hk hhat m) _
  refine step1.trans ?_
  rw [lintegral_lintegral_swap]
  swap
  · exact ((timeWeight_measurable θ).comp measurable_fst).mul
      ((hMm.comp measurable_snd).mul hAm) |>.aemeasurable
  have hai : ∀ l, Integrable (atom l) := atom_integrable_of_bound hc hΨ hbd
  have step2 : ∀ l, ∫⁻ m, timeWeight θ m * (mixedFourierEnvelope00 H l * ‖timeFourier (atom l) m‖ₑ) =
      mixedFourierEnvelope00 H l * timeFourierNorm θ (atom l) := by
    intro l
    rw [timeFourierNorm_eq_lintegral (hai l), ← lintegral_const_mul'']
    · exact lintegral_congr fun m => by ring
    · exact ((timeWeight_measurable θ).mul
        ((timeFourier_continuous (hai l)).measurable.enorm)).aemeasurable
  simp_rw [step2]
  calc ∫⁻ l, mixedFourierEnvelope00 H l * timeFourierNorm θ (atom l)
      ≤ ∫⁻ l, mixedFourierEnvelope00 H l * (Cw * timeWeight θ l) :=
        lintegral_mono fun l => mul_le_mul_right (hCw l) _
    _ = Cw * ∫⁻ l, timeWeight θ l * mixedFourierEnvelope00 H l := by
        rw [← lintegral_const_mul'' Cw
          (f := fun l => timeWeight θ l * mixedFourierEnvelope00 H l)
          ((timeWeight_measurable θ).mul hMm).aemeasurable]
        exact lintegral_congr fun l => by ring
    _ = _ := by rw [mixedFourierNorm00_eq_lintegral hk]

end WaveTurbulence.Flower.ProtOps
