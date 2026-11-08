/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.ProtTa.AtomFT
public import WaveTurbulence.Foundations.Flower.ProtTa.Congr
public import WaveTurbulence.Foundations.Sumint.TimeBridge

/-! # PROT-TA, Lemma 12.1: the synthesized output `G₀ = ∫ ĥ_k(l) atom(l) dl` and its norm

For a family `H : ℝ³ → V → ℂ` of finite `𝔛^{θ,0,0}` norm, `G₀(y,k) = ∫ ĥ_k(l) · atom_A(l)(y) dl` has
`mixedFourierNorm00 θ G₀ ≤ 2^θ·2^θ·B·mixedFourierNorm00 θ H` (the `k`-supremum stays inside, `M(l) = sup_k |ĥ_k(l)|`
is lower semicontinuous hence measurable). -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open MeasureTheory WaveTurbulence.Fourier
open scoped ENNReal ContDiff

namespace WaveTurbulence.Flower.ProtTa

variable {V : Type*}

/-- The synthesized output. -/
def G0 (A : ℝ) (H : (Fin 3 → ℝ) → V → ℂ) (y : Fin 2 → ℝ) (k : V) : ℂ :=
  ∫ l, timeFourier (fun t => H t k) l * atom A l y

variable {A : ℝ} {H : (Fin 3 → ℝ) → V → ℂ}

theorem G0_prod_integrable (hk : ∀ k, Integrable (fun t => H t k))
    (hhat : ∀ k, Integrable (timeFourier fun t => H t k)) (k : V) :
    Integrable (fun p : (Fin 3 → ℝ) × (Fin 2 → ℝ) =>
      timeFourier (fun t => H t k) p.1 * atom A p.1 p.2) (volume.prod volume) := by
  have h1 : Integrable (fun p : (Fin 3 → ℝ) × (Fin 2 → ℝ) =>
      ‖timeFourier (fun t => H t k) p.1‖ * ‖chi p.2‖) (volume.prod volume) :=
    Integrable.mul_prod (f := fun l => ‖timeFourier (fun t => H t k) l‖) (g := fun y => ‖chi y‖)
      (hhat k).norm chi_integrable.norm
  refine h1.mono' ?_ (ae_of_all _ fun p => ?_)
  · exact (((timeFourier_continuous (hk k)).comp continuous_fst).mul
      (atom_continuous A)).aestronglyMeasurable
  · simp only [norm_mul]
    exact mul_le_mul_of_nonneg_left (norm_atom_le A p.1 p.2) (norm_nonneg _)

theorem G0_integrable (hk : ∀ k, Integrable (fun t => H t k))
    (hhat : ∀ k, Integrable (timeFourier fun t => H t k)) (k : V) :
    Integrable (fun y => G0 A H y k) :=
  (G0_prod_integrable hk hhat k).integral_prod_right

theorem timeFourier_G0 (hk : ∀ k, Integrable (fun t => H t k))
    (hhat : ∀ k, Integrable (timeFourier fun t => H t k)) (k : V) (m : Fin 2 → ℝ) :
    timeFourier (fun y => G0 A H y k) m =
      ∫ l, timeFourier (fun t => H t k) l * timeFourier (atom A l) m := by
  have h := Sumint.timeFourier_integral (μ := (volume : Measure (Fin 3 → ℝ)))
    (fun l y => timeFourier (fun t => H t k) l * atom A l y) (G0_prod_integrable hk hhat k) m
  refine h.trans (integral_congr_ae (ae_of_all _ fun l => ?_))
  exact congrFun (timeFourier_smul (timeFourier (fun t => H t k) l) (atom A l)) m

theorem envelope_G0_le (hk : ∀ k, Integrable (fun t => H t k))
    (hhat : ∀ k, Integrable (timeFourier fun t => H t k)) (m : Fin 2 → ℝ) :
    mixedFourierEnvelope00 (G0 A H) m ≤
      ∫⁻ l, mixedFourierEnvelope00 H l * ‖timeFourier (atom A l) m‖ₑ := by
  refine iSup_le fun k => ?_
  change ‖timeFourier (fun y => G0 A H y k) m‖ₑ ≤ _
  rw [timeFourier_G0 hk hhat k m]
  refine (enorm_integral_le_lintegral_enorm _).trans (lintegral_mono fun l => ?_)
  rw [enorm_mul]
  exact mul_le_mul_left (le_iSup (fun k => ‖timeFourier (fun t => H t k) l‖ₑ) k) _

theorem G0_norm_le {θ : ℝ} (hθ0 : 0 ≤ θ) {B : ℝ≥0∞} (hB : ∀ z : ℝ, timeFourierNorm θ (psi z) ≤ B)
    (hH : mixedFourierNorm00 θ H < ⊤) :
    mixedFourierNorm00 θ (G0 A H) ≤
      ENNReal.ofReal (2 ^ θ) * ENNReal.ofReal (2 ^ θ) * B * mixedFourierNorm00 θ H := by
  have hk : ∀ k, Integrable (fun t => H t k) := integrable_of_mixedFourierNorm00_lt_top hH
  have hhat : ∀ k, Integrable (timeFourier fun t => H t k) := fun k =>
    integrable_timeFourier_of_norm_lt_top hθ0
      ((timeFourierNorm_slice_le_mixedFourierNorm00 θ H k).trans_lt hH)
  have hG : ∀ k, Integrable (fun y => G0 A H y k) := G0_integrable hk hhat
  have hMm : Measurable (mixedFourierEnvelope00 H) := measurable_mixedFourierEnvelope00 hk
  have hAm : Measurable (fun p : (Fin 2 → ℝ) × (Fin 3 → ℝ) => ‖timeFourier (atom A p.2) p.1‖ₑ) := by
    have := Sumint.measurable_parametric_timeFourier (fun (l : Fin 3 → ℝ) (y : Fin 2 → ℝ) => atom A l y)
      (atom_continuous A).measurable
    exact (this.comp measurable_swap).enorm
  rw [mixedFourierNorm00_eq_lintegral hG]
  have step1 : ∫⁻ m, timeWeight θ m * mixedFourierEnvelope00 (G0 A H) m ≤
      ∫⁻ m, ∫⁻ l, timeWeight θ m * (mixedFourierEnvelope00 H l * ‖timeFourier (atom A l) m‖ₑ) := by
    refine lintegral_mono fun m => ?_
    rw [lintegral_const_mul' (timeWeight θ m) _ ENNReal.ofReal_ne_top]
    exact mul_le_mul_right (envelope_G0_le hk hhat m) _
  refine step1.trans ?_
  rw [lintegral_lintegral_swap]
  swap
  · exact ((timeWeight_measurable θ).comp measurable_fst).mul
      ((hMm.comp measurable_snd).mul hAm) |>.aemeasurable
  have step2 : ∀ l, ∫⁻ m, timeWeight θ m * (mixedFourierEnvelope00 H l * ‖timeFourier (atom A l) m‖ₑ) =
      mixedFourierEnvelope00 H l * timeFourierNorm θ (atom A l) := by
    intro l
    rw [timeFourierNorm_eq_lintegral (atom_integrable A l), ← lintegral_const_mul'']
    · exact lintegral_congr fun m => by ring
    · exact ((timeWeight_measurable θ).mul
        ((timeFourier_continuous (atom_integrable A l)).measurable.enorm)).aemeasurable
  simp_rw [step2]
  calc ∫⁻ l, mixedFourierEnvelope00 H l * timeFourierNorm θ (atom A l)
      ≤ ∫⁻ l, mixedFourierEnvelope00 H l *
        ((ENNReal.ofReal (2 ^ θ) * ENNReal.ofReal (2 ^ θ) * B) * timeWeight θ l) := by
        refine lintegral_mono fun l => mul_le_mul_right ?_ _
        refine (atom_norm_le hθ0 hB A l).trans ?_
        calc ENNReal.ofReal (2 ^ θ) * timeWeight θ (nu l) * B
            ≤ ENNReal.ofReal (2 ^ θ) * (ENNReal.ofReal (2 ^ θ) * timeWeight θ l) * B := by
              gcongr
              exact timeWeight_nu_le hθ0 l
          _ = _ := by ring
    _ = (ENNReal.ofReal (2 ^ θ) * ENNReal.ofReal (2 ^ θ) * B) *
          ∫⁻ l, timeWeight θ l * mixedFourierEnvelope00 H l := by
        rw [← lintegral_const_mul'' (ENNReal.ofReal (2 ^ θ) * ENNReal.ofReal (2 ^ θ) * B)
          (f := fun l => timeWeight θ l * mixedFourierEnvelope00 H l)
          ((timeWeight_measurable θ).mul hMm).aemeasurable]
        exact lintegral_congr fun l => by ring
    _ = _ := by rw [mixedFourierNorm00_eq_lintegral hk]

end WaveTurbulence.Flower.ProtTa
