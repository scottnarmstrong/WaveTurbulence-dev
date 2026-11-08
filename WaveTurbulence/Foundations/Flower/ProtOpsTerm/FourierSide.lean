/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.ProtOpsTerm.Agree
public import WaveTurbulence.Foundations.Flower.ProtTa.Op
public import WaveTurbulence.Foundations.Sumint.ParametricFourierMeasurability

/-! # PROT-OPS-TERM: the Fourier side of `T_A` with spectators

`fh h (μ, λ) = ĥ(μ, λ)`, `W A h ((μ, m), λ) = ĥ(μ, λ) · â_λ(m)` (integrable), and
`uHat A h ζ = ∫ ĥ(ζ_spec, λ) â_λ(ζ_tail) dλ`. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open MeasureTheory WaveTurbulence.Fourier WaveTurbulence.Flower.ProtTa
open scoped ENNReal ContDiff

namespace WaveTurbulence.Flower.ProtOpsTerm

variable {r : ℕ}

/-- The transform `ĥ` read on `ℝ^r × ℝ³`. -/
def fh (h : (Fin (r + 3) → ℝ) → ℂ) (q : (Fin r → ℝ) × (Fin 3 → ℝ)) : ℂ :=
  timeFourier h (Fin.append q.1 q.2)

theorem fh_eq (h : (Fin (r + 3) → ℝ) → ℂ) :
    (fun z : Fin (r + 3) → ℝ => fh h (hd z, tl z)) = timeFourier h := by
  funext z; simp [fh, append_hd_tl]

theorem measurable_append {n m : ℕ} :
    Measurable (fun q : (Fin n → ℝ) × (Fin m → ℝ) => (Fin.append q.1 q.2 : Fin (n + m) → ℝ)) := by
  have := (splitE n m).symm.measurable
  convert this using 1
  funext q
  exact (splitE_symm q.1 q.2).symm

theorem fh_integrable {h : (Fin (r + 3) → ℝ) → ℂ} (hhat : Integrable (timeFourier h)) :
    Integrable (fh h) (volume.prod volume) := by
  rw [← integrable_split]
  rw [fh_eq]; exact hhat

theorem measurable_fh {h : (Fin (r + 3) → ℝ) → ℂ} (hint : Integrable h) : Measurable (fh h) :=
  (timeFourier_continuous hint).measurable.comp measurable_append

theorem atom_l1 (A : ℝ) : ∃ B : ℝ≥0∞, B < ⊤ ∧ ∀ l : Fin 3 → ℝ,
    ∫⁻ m, ‖timeFourier (atom A l) m‖ₑ ≤ B := by
  obtain ⟨B, hBt, hB⟩ := psi_uniform (le_refl (0 : ℝ)) zero_le_one
  refine ⟨B, hBt, fun l => ?_⟩
  have h1 := atom_norm_le (le_refl (0 : ℝ)) hB A l
  rw [timeFourierNorm_eq_lintegral (atom_integrable A l)] at h1
  simpa [timeWeight] using h1

/-- `W ((μ, m), λ) = ĥ(μ, λ) · â_λ(m)`. -/
def W (A : ℝ) (h : (Fin (r + 3) → ℝ) → ℂ)
    (q : ((Fin r → ℝ) × (Fin 2 → ℝ)) × (Fin 3 → ℝ)) : ℂ :=
  fh h (q.1.1, q.2) * timeFourier (atom A q.2) q.1.2

theorem measurable_atomFT (A : ℝ) :
    Measurable (fun q : (Fin 3 → ℝ) × (Fin 2 → ℝ) => timeFourier (atom A q.1) q.2) :=
  Sumint.measurable_parametric_timeFourier (fun (l : Fin 3 → ℝ) (y : Fin 2 → ℝ) => atom A l y)
    (atom_continuous A).measurable

theorem measurable_W (A : ℝ) {h : (Fin (r + 3) → ℝ) → ℂ} (hint : Integrable h) : Measurable (W A h) := by
  have hf := measurable_fh hint
  have hg := measurable_atomFT A
  have h1 : Measurable (fun q : ((Fin r → ℝ) × (Fin 2 → ℝ)) × (Fin 3 → ℝ) => fh h (q.1.1, q.2)) := by
    refine hf.comp (Measurable.prodMk ?_ ?_)
    · exact measurable_fst.comp measurable_fst
    · exact measurable_snd
  have h3 : Measurable (fun q : ((Fin r → ℝ) × (Fin 2 → ℝ)) × (Fin 3 → ℝ) =>
      timeFourier (atom A q.2) q.1.2) := by
    have hp : Measurable (fun q : ((Fin r → ℝ) × (Fin 2 → ℝ)) × (Fin 3 → ℝ) => (q.2, q.1.2)) :=
      measurable_snd.prodMk (measurable_snd.comp measurable_fst)
    simpa only [Function.comp_def] using hg.comp hp
  have e : W A h = fun q => fh h (q.1.1, q.2) * timeFourier (atom A q.2) q.1.2 := rfl
  rw [e]
  exact h1.mul h3

theorem W_integrable (A : ℝ) {h : (Fin (r + 3) → ℝ) → ℂ} (hint : Integrable h)
    (hhat : Integrable (timeFourier h)) :
    Integrable (W A h) (((volume : Measure (Fin r → ℝ)).prod (volume : Measure (Fin 2 → ℝ))).prod
      (volume : Measure (Fin 3 → ℝ))) := by
  obtain ⟨B, hBt, hB⟩ := atom_l1 A
  refine ⟨(measurable_W A hint).aestronglyMeasurable, ?_⟩
  have hfh := fh_integrable hhat
  unfold HasFiniteIntegral
  have hm : Measurable (fun q : ((Fin r → ℝ) × (Fin 2 → ℝ)) × (Fin 3 → ℝ) => ‖W A h q‖ₑ) :=
    (measurable_W A hint).enorm
  rw [lintegral_prod_symm _ hm.aemeasurable]
  have hstep : ∀ l : Fin 3 → ℝ,
      ∫⁻ p : (Fin r → ℝ) × (Fin 2 → ℝ), ‖W A h (p, l)‖ₑ ∂(volume.prod volume) ≤
        (∫⁻ μ : Fin r → ℝ, ‖fh h (μ, l)‖ₑ) * B := by
    intro l
    have e : ∀ p : (Fin r → ℝ) × (Fin 2 → ℝ), ‖W A h (p, l)‖ₑ =
        ‖fh h (p.1, l)‖ₑ * ‖timeFourier (atom A l) p.2‖ₑ := fun p => by
      simp [W, enorm_mul]
    simp_rw [e]
    have hf1 : Measurable (fun μ : Fin r → ℝ => ‖fh h (μ, l)‖ₑ) :=
      ((measurable_fh hint).comp (measurable_id.prodMk measurable_const)).enorm
    have hg1 : Measurable (fun m : Fin 2 → ℝ => ‖timeFourier (atom A l) m‖ₑ) :=
      ((measurable_atomFT A).comp (measurable_const.prodMk measurable_id)).enorm
    have := lintegral_prod_mul (μ := (volume : Measure (Fin r → ℝ))) (ν := (volume : Measure (Fin 2 → ℝ)))
      hf1.aemeasurable hg1.aemeasurable
    rw [this]
    exact mul_le_mul_right (hB l) _
  calc ∫⁻ l, ∫⁻ p, ‖W A h (p, l)‖ₑ ∂(volume.prod volume)
      ≤ ∫⁻ l, (∫⁻ μ : Fin r → ℝ, ‖fh h (μ, l)‖ₑ) * B := lintegral_mono hstep
    _ = (∫⁻ l, ∫⁻ μ : Fin r → ℝ, ‖fh h (μ, l)‖ₑ) * B := by
        rw [lintegral_mul_const]
        exact (measurable_fh hint).enorm.lintegral_prod_left'
    _ < ⊤ := by
        rw [← lintegral_prod_symm (fun q : (Fin r → ℝ) × (Fin 3 → ℝ) => ‖fh h q‖ₑ)
          (measurable_fh hint).enorm.aemeasurable]
        exact ENNReal.mul_lt_top hfh.2 hBt

end WaveTurbulence.Flower.ProtOpsTerm
