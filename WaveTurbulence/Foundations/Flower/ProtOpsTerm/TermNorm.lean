/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.ProtOpsTerm.TermG
public import WaveTurbulence.Foundations.Flower.ProtOpsTerm.Weights
public import WaveTurbulence.Foundations.Flower.ProtOpsTerm.Ess

/-! # PROT-OPS-TERM: the `𝔛^{θ,0,0}` bound for the cutoff operator `Φ · T_A` with `r` spectators -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open MeasureTheory WaveTurbulence.Fourier WaveTurbulence.Flower.ProtTa
open scoped ENNReal ContDiff

namespace WaveTurbulence.Flower.ProtOpsTerm

variable {r : ℕ}

/-- The weighted `L¹` norm of an output atom's transform. -/
theorem atom_weighted_le {θ : ℝ} (hθ0 : 0 ≤ θ) {B : ℝ≥0∞} (hB : ∀ z : ℝ, timeFourierNorm θ (psi z) ≤ B)
    (A : ℝ) (l : Fin 3 → ℝ) :
    ∫⁻ m, timeWeight θ m * ‖timeFourier (atom A l) m‖ₑ ≤
      ENNReal.ofReal (2 ^ θ) * ENNReal.ofReal (2 ^ θ) * B * timeWeight θ l := by
  rw [← timeFourierNorm_eq_lintegral (atom_integrable A l)]
  refine (atom_norm_le hθ0 hB A l).trans ?_
  calc ENNReal.ofReal (2 ^ θ) * timeWeight θ (nu l) * B
      ≤ ENNReal.ofReal (2 ^ θ) * (ENNReal.ofReal (2 ^ θ) * timeWeight θ l) * B := by
        gcongr
        exact timeWeight_nu_le hθ0 l
    _ = _ := by ring

theorem atom_l1_le {B0 : ℝ≥0∞} (hB0 : ∀ z : ℝ, timeFourierNorm 0 (psi z) ≤ B0) (A : ℝ) (l : Fin 3 → ℝ) :
    ∫⁻ m, ‖timeFourier (atom A l) m‖ₑ ≤ B0 := by
  have := atom_weighted_le (le_refl (0 : ℝ)) hB0 A l
  simpa [timeWeight] using this

theorem I_bound {θ : ℝ} (hθ0 : 0 ≤ θ) {B0 Bθ : ℝ≥0∞}
    (hB0 : ∀ z : ℝ, timeFourierNorm 0 (psi z) ≤ B0) (hBθ : ∀ z : ℝ, timeFourierNorm θ (psi z) ≤ Bθ)
    (A : ℝ) (μ : Fin r → ℝ) (l : Fin 3 → ℝ) :
    ∫⁻ m : Fin 2 → ℝ, timeWeight θ (Fin.append μ m) * ‖timeFourier (atom A l) m‖ₑ ≤
      (B0 + ENNReal.ofReal (2 ^ θ) * ENNReal.ofReal (2 ^ θ) * Bθ) * timeWeight θ (Fin.append μ l) := by
  have hm : Measurable (fun m : Fin 2 → ℝ => ‖timeFourier (atom A l) m‖ₑ) :=
    (timeFourier_continuous (atom_integrable A l)).measurable.enorm
  calc ∫⁻ m : Fin 2 → ℝ, timeWeight θ (Fin.append μ m) * ‖timeFourier (atom A l) m‖ₑ
      ≤ ∫⁻ m : Fin 2 → ℝ, (timeWeight θ μ * ‖timeFourier (atom A l) m‖ₑ +
          timeWeight θ m * ‖timeFourier (atom A l) m‖ₑ) := by
        refine lintegral_mono fun m => ?_
        rw [← add_mul]
        exact mul_le_mul_left (tw_append_le hθ0 μ m) _
    _ = timeWeight θ μ * (∫⁻ m, ‖timeFourier (atom A l) m‖ₑ) +
          (∫⁻ m, timeWeight θ m * ‖timeFourier (atom A l) m‖ₑ) := by
        rw [lintegral_add_left (hm.const_mul _), lintegral_const_mul _ hm]
    _ ≤ timeWeight θ μ * B0 + ENNReal.ofReal (2 ^ θ) * ENNReal.ofReal (2 ^ θ) * Bθ * timeWeight θ l := by
        gcongr
        · exact atom_l1_le hB0 A l
        · exact atom_weighted_le hθ0 hBθ A l
    _ ≤ B0 * timeWeight θ (Fin.append μ l) +
          ENNReal.ofReal (2 ^ θ) * ENNReal.ofReal (2 ^ θ) * Bθ * timeWeight θ (Fin.append μ l) := by
        rw [mul_comm (timeWeight θ μ) B0]
        gcongr
        · exact tw_left_le hθ0 μ l
        · exact tw_right_le hθ0 μ l
    _ = _ := by ring

theorem term_norm_core {θ : ℝ} (hθ0 : 0 ≤ θ) {B0 Bθ : ℝ≥0∞}
    (hB0 : ∀ z : ℝ, timeFourierNorm 0 (psi z) ≤ B0) (hBθ : ∀ z : ℝ, timeFourierNorm θ (psi z) ≤ Bθ)
    (A : ℝ) {V : Type*} (H : (Fin (r + 3) → ℝ) → V → ℂ) (hH : mixedFourierNorm00 θ H < ⊤) :
    mixedFourierNorm00 θ (fun ts k => Gf A (fun t => H t k) ts) ≤
      (B0 + ENNReal.ofReal (2 ^ θ) * ENNReal.ofReal (2 ^ θ) * Bθ) * mixedFourierNorm00 θ H := by
  set C : ℝ≥0∞ := B0 + ENNReal.ofReal (2 ^ θ) * ENNReal.ofReal (2 ^ θ) * Bθ with hC
  have hk : ∀ k, Integrable (fun t => H t k) := integrable_of_mixedFourierNorm00_lt_top hH
  have hhat : ∀ k, Integrable (timeFourier fun t => H t k) := fun k =>
    integrable_timeFourier_of_norm_lt_top hθ0
      ((timeFourierNorm_slice_le_mixedFourierNorm00 θ H k).trans_lt hH)
  have hG : ∀ k, Integrable (fun ts => Gf A (fun t => H t k) ts) := fun k => Gf_integrable A (hk k)
  have hMm : Measurable (mixedFourierEnvelope00 H) := measurable_mixedFourierEnvelope00 hk
  rw [mixedFourierNorm00_eq_lintegral hG]
  let Ψ : (Fin (r + 2) → ℝ) → ℝ≥0∞ := fun ζ =>
    ∫⁻ l : Fin 3 → ℝ, mixedFourierEnvelope00 H (Fin.append (hd ζ) l) * ‖timeFourier (atom A l) (tl ζ)‖ₑ
  -- the a.e. bound of the envelope
  have hae : ∀ᵐ ζ : Fin (r + 2) → ℝ, mixedFourierEnvelope00 (fun ts k => Gf A (fun t => H t k) ts) ζ ≤ Ψ ζ := by
    refine ae_iSup_le_of_continuous volume
      (fun k ζ => ‖timeFourier (fun ts => Gf A (fun t => H t k) ts) ζ‖ₑ)
      (fun k => continuous_enorm.comp (timeFourier_continuous (hG k))) Ψ (fun k => ?_)
    have hu := uHat_integrable A (hk k) (hhat k)
    have hft := uniq_ft (hG k) hu (Gf_ae A (hk k) (hhat k)).symm
    filter_upwards [hft] with ζ hζ
    rw [hζ]
    refine (enorm_integral_le_lintegral_enorm _).trans (lintegral_mono fun l => ?_)
    rw [enorm_mul]
    refine mul_le_mul_left ?_ _
    have : ‖fh (fun t => H t k) (hd ζ, l)‖ₑ ≤ mixedFourierEnvelope00 H (Fin.append (hd ζ) l) :=
      le_iSup (fun k => ‖timeFourier (fun t => H t k) (Fin.append (hd ζ) l)‖ₑ) k
    exact this
  have step1 : ∫⁻ ζ, timeWeight θ ζ * mixedFourierEnvelope00 (fun ts k => Gf A (fun t => H t k) ts) ζ ≤
      ∫⁻ ζ, timeWeight θ ζ * Ψ ζ := lintegral_mono_ae (hae.mono fun ζ h => mul_le_mul_right h _)
  refine step1.trans ?_
  let F : ((Fin r → ℝ) × (Fin 2 → ℝ)) × (Fin 3 → ℝ) → ℝ≥0∞ := fun q =>
    timeWeight θ (Fin.append q.1.1 q.1.2) * (mixedFourierEnvelope00 H (Fin.append q.1.1 q.2) *
      ‖timeFourier (atom A q.2) q.1.2‖ₑ)
  have hFm : Measurable F := by
    have h1 : Measurable (fun q : ((Fin r → ℝ) × (Fin 2 → ℝ)) × (Fin 3 → ℝ) =>
        timeWeight θ (Fin.append q.1.1 q.1.2)) :=
      (timeWeight_measurable θ).comp (measurable_append.comp measurable_fst)
    have h2 : Measurable (fun q : ((Fin r → ℝ) × (Fin 2 → ℝ)) × (Fin 3 → ℝ) =>
        mixedFourierEnvelope00 H (Fin.append q.1.1 q.2)) :=
      hMm.comp (measurable_append.comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd))
    have h3 : Measurable (fun q : ((Fin r → ℝ) × (Fin 2 → ℝ)) × (Fin 3 → ℝ) =>
        ‖timeFourier (atom A q.2) q.1.2‖ₑ) := by
      have hp : Measurable (fun q : ((Fin r → ℝ) × (Fin 2 → ℝ)) × (Fin 3 → ℝ) => (q.2, q.1.2)) :=
        measurable_snd.prodMk (measurable_snd.comp measurable_fst)
      simpa only [Function.comp_def] using ((measurable_atomFT A).comp hp).enorm
    exact h1.mul (h2.mul h3)
  have e1 : ∫⁻ ζ, timeWeight θ ζ * Ψ ζ = ∫⁻ p : (Fin r → ℝ) × (Fin 2 → ℝ), ∫⁻ l, F (p, l) := by
    refine Eq.trans ?_ (lintegral_split (fun p : (Fin r → ℝ) × (Fin 2 → ℝ) => ∫⁻ l, F (p, l)))
    refine lintegral_congr fun ζ => ?_
    simp only [F, Ψ, append_hd_tl]
    exact (lintegral_const_mul' _ _ (by unfold timeWeight; exact ENNReal.ofReal_ne_top)).symm
  have e2 : ∫⁻ p : (Fin r → ℝ) × (Fin 2 → ℝ), ∫⁻ l, F (p, l) =
      ∫⁻ l, ∫⁻ p : (Fin r → ℝ) × (Fin 2 → ℝ), F (p, l) :=
    lintegral_lintegral_swap hFm.aemeasurable
  have hbd : ∀ l : Fin 3 → ℝ, ∫⁻ p : (Fin r → ℝ) × (Fin 2 → ℝ), F (p, l) ≤
      ∫⁻ μ : Fin r → ℝ, mixedFourierEnvelope00 H (Fin.append μ l) * (C * timeWeight θ (Fin.append μ l)) := by
    intro l
    have hFl : Measurable (fun p : (Fin r → ℝ) × (Fin 2 → ℝ) => F (p, l)) :=
      hFm.comp (measurable_id.prodMk measurable_const)
    refine (lintegral_prod _ hFl.aemeasurable).trans_le ?_
    refine lintegral_mono fun μ => ?_
    have hm : Measurable (fun m : Fin 2 → ℝ => ‖timeFourier (atom A l) m‖ₑ) :=
      (timeFourier_continuous (atom_integrable A l)).measurable.enorm
    have e : ∀ m : Fin 2 → ℝ, F ((μ, m), l) = mixedFourierEnvelope00 H (Fin.append μ l) *
        (timeWeight θ (Fin.append μ m) * ‖timeFourier (atom A l) m‖ₑ) := fun m => by
      simp only [F]; ring
    simp_rw [e]
    have hmm : Measurable (fun m : Fin 2 → ℝ => timeWeight θ (Fin.append μ m) * ‖timeFourier (atom A l) m‖ₑ) :=
      ((timeWeight_measurable θ).comp (measurable_append.comp (measurable_const.prodMk measurable_id))).mul hm
    rw [lintegral_const_mul _ hmm]
    exact mul_le_mul_right (I_bound hθ0 hB0 hBθ A μ l) _
  calc ∫⁻ ζ, timeWeight θ ζ * Ψ ζ = ∫⁻ p : (Fin r → ℝ) × (Fin 2 → ℝ), ∫⁻ l, F (p, l) := e1
    _ = ∫⁻ l, ∫⁻ p : (Fin r → ℝ) × (Fin 2 → ℝ), F (p, l) := e2
    _ ≤ ∫⁻ l, ∫⁻ μ : Fin r → ℝ, mixedFourierEnvelope00 H (Fin.append μ l) *
          (C * timeWeight θ (Fin.append μ l)) := lintegral_mono hbd
    _ = ∫⁻ q : (Fin r → ℝ) × (Fin 3 → ℝ), mixedFourierEnvelope00 H (Fin.append q.1 q.2) *
          (C * timeWeight θ (Fin.append q.1 q.2)) := by
        exact (lintegral_prod_symm _ ((hMm.comp measurable_append).mul (measurable_const.mul
          ((timeWeight_measurable θ).comp measurable_append))).aemeasurable).symm
    _ = ∫⁻ z : Fin (r + 3) → ℝ, mixedFourierEnvelope00 H z * (C * timeWeight θ z) := by
        have := lintegral_split (fun q : (Fin r → ℝ) × (Fin 3 → ℝ) =>
          mixedFourierEnvelope00 H (Fin.append q.1 q.2) * (C * timeWeight θ (Fin.append q.1 q.2)))
        simp only [append_hd_tl] at this
        exact this.symm
    _ = C * ∫⁻ z, timeWeight θ z * mixedFourierEnvelope00 H z := by
        calc ∫⁻ z : Fin (r + 3) → ℝ, mixedFourierEnvelope00 H z * (C * timeWeight θ z)
            = ∫⁻ z : Fin (r + 3) → ℝ, C * (timeWeight θ z * mixedFourierEnvelope00 H z) :=
              lintegral_congr fun z => by ring
          _ = _ := lintegral_const_mul C ((timeWeight_measurable θ).mul hMm)
    _ = C * mixedFourierNorm00 θ H := by rw [mixedFourierNorm00_eq_lintegral hk]

end WaveTurbulence.Flower.ProtOpsTerm
