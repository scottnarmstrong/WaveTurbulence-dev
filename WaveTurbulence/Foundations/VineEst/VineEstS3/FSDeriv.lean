/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Layered.ParamFinite
public import WaveTurbulence.Foundations.Layered.InverseFourier
public import WaveTurbulence.Foundations.Regref.ParamDerivFin
public import WaveTurbulence.Foundations.Fourier.MixedNorm
public import WaveTurbulence.Foundations.Regref.TraceDeriv

/-! # Momentum derivatives of frequency mixtures (B2, step 5)

For a family `Φ(λ, k)` that is `C^N` in the momentum with finite weighted coordinate-word envelopes
`E_σ(λ) = sup_k ⟨k⟩^{Λ₂} |∂_σ Φ(λ,k)|` of integrable size, and a bounded measurable multiplier `a(λ)`, the
mixture `c(k) = ∫ a(λ) Φ(λ,k) dλ` is `C^N` and
`⟨k⟩^{Λ₂} |∂_σ c(k)| ≤ ∫ |a(λ)| E_σ(λ) dλ`.
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineEstS3.FS
open WaveTurbulence WaveTurbulence.Fourier MeasureTheory Set Filter
open scoped ENNReal ContDiff

variable {r d : ℕ}

/-- The weighted coordinate-word envelope `sup_k ⟨k⟩^{Λ₂} |∂_σ f(k)|`. -/
noncomputable def wenv (Λ₂ : ℕ) {n : ℕ} (σ : Fin n → Fin d) (f : Mom d → ℂ) : ℝ≥0∞ :=
  ⨆ k, ENNReal.ofReal (momentumBracket k ^ Λ₂ * ‖momentumDerivative σ f k‖)

theorem one_le_momentumBracket (k : Mom d) : 1 ≤ momentumBracket k := by
  unfold momentumBracket
  rw [Real.one_le_sqrt]
  nlinarith [sq_nonneg ‖k‖]

theorem continuous_momentumBracket : Continuous (momentumBracket (d := d)) := by
  unfold momentumBracket
  fun_prop

theorem le_wenv {Λ₂ n : ℕ} (σ : Fin n → Fin d) (f : Mom d → ℂ) (k : Mom d) :
    ENNReal.ofReal (momentumBracket k ^ Λ₂ * ‖momentumDerivative σ f k‖) ≤ wenv Λ₂ σ f :=
  le_iSup (fun k => ENNReal.ofReal (momentumBracket k ^ Λ₂ * ‖momentumDerivative σ f k‖)) k

theorem norm_le_toReal_wenv {Λ₂ n : ℕ} (σ : Fin n → Fin d) (f : Mom d → ℂ)
    (h : wenv Λ₂ σ f < ⊤) (k : Mom d) :
    ‖momentumDerivative σ f k‖ ≤ (wenv Λ₂ σ f).toReal := by
  have h1 := le_wenv (Λ₂ := Λ₂) σ f k
  have h2 : momentumBracket k ^ Λ₂ * ‖momentumDerivative σ f k‖ ≤ (wenv Λ₂ σ f).toReal :=
    (ENNReal.ofReal_le_iff_le_toReal h.ne).mp h1
  have h3 : 1 ≤ momentumBracket k ^ Λ₂ := one_le_pow₀ (one_le_momentumBracket k)
  have h4 := norm_nonneg (momentumDerivative σ f k)
  nlinarith

section Measurability

variable {N Λ₂ : ℕ} {Φ : (Fin r → ℝ) → Mom d → ℂ}

theorem measurable_wenv (hs : ∀ ξ, ContDiff ℝ N (Φ ξ)) (hm : ∀ k, StronglyMeasurable fun ξ => Φ ξ k)
    {n : ℕ} (hn : n ≤ N) (σ : Fin n → Fin d) :
    Measurable fun ξ => wenv Λ₂ σ (Φ ξ) := by
  obtain ⟨D, hDc, hD⟩ := TopologicalSpace.exists_countable_dense (Mom d)
  have : Countable D := hDc.to_subtype
  have he : (fun ξ => wenv Λ₂ σ (Φ ξ)) =
      fun ξ => ⨆ q : D, ENNReal.ofReal (momentumBracket q.1 ^ Λ₂ * ‖momentumDerivative σ (Φ ξ) q.1‖) := by
    funext ξ
    unfold wenv
    refine Regref.iSup_eq_iSup_dense hD ?_
    exact ENNReal.continuous_ofReal.comp
      ((continuous_momentumBracket.pow Λ₂).mul
        (continuous_norm.comp (Regref.continuous_momentumDerivative hn σ (hs ξ))))
  rw [he]
  refine Measurable.iSup fun q => ?_
  have hsm := Regref.stronglyMeasurable_iteratedFDeriv_param_of_le (f := fun k ξ => Φ ξ k) hs hm n hn q.1
  have h1 : Measurable fun ξ => ‖momentumDerivative σ (Φ ξ) q.1‖ :=
    (((continuous_eval_const (fun i => EuclideanSpace.single (σ i) (1 : ℝ))).comp_stronglyMeasurable
      hsm).measurable).norm
  exact ENNReal.measurable_ofReal.comp (measurable_const.mul h1)

end Measurability


section Mixture

variable {N Λ₂ : ℕ} {Φ : (Fin r → ℝ) → Mom d → ℂ}

theorem mixture_hyps {a : (Fin r → ℝ) → ℂ} {Ka : ℝ} (ha : Measurable a) (hab : ∀ lam, ‖a lam‖ ≤ Ka)
    (hs : ∀ lam, ContDiff ℝ N (Φ lam)) (hm : ∀ k, StronglyMeasurable fun lam => Φ lam k)
    (hfin : ∀ n ≤ N, ∀ σ : Fin n → Fin d, ∀ lam, wenv Λ₂ σ (Φ lam) < ⊤)
    (hint : ∀ n ≤ N, ∀ σ : Fin n → Fin d, ∫⁻ lam, wenv Λ₂ σ (Φ lam) ≠ ⊤) :
    (∀ lam, ContDiff ℝ N (fun k => a lam * Φ lam k)) ∧
    (∀ j ≤ N, ∀ e, AEStronglyMeasurable
      (fun lam => iteratedFDeriv ℝ j (fun k => a lam * Φ lam k) e) volume) ∧
    (∀ j ≤ N, ∃ B : (Fin r → ℝ) → ℝ, Integrable B volume ∧
      ∀ᵐ lam, ∀ e, ‖iteratedFDeriv ℝ j (fun k => a lam * Φ lam k) e‖ ≤ B lam) := by
  have hf : ∀ lam, ContDiff ℝ N (fun k => a lam * Φ lam k) := fun lam => contDiff_const.mul (hs lam)
  refine ⟨hf, fun j hj e => ?_, fun j hj => ?_⟩
  · have := Regref.stronglyMeasurable_iteratedFDeriv_param_of_le
      (f := fun k lam => a lam * Φ lam k) hf (fun k => ha.stronglyMeasurable.mul (hm k)) j hj e
    exact this.aestronglyMeasurable
  · refine ⟨fun lam => Ka * ∑ σ : Fin j → Fin d, (wenv Λ₂ σ (Φ lam)).toReal, ?_, ae_of_all _ fun lam e => ?_⟩
    · refine Integrable.const_mul (integrable_finsetSum _ fun σ _ => ?_) _
      refine integrable_toReal_of_lintegral_ne_top ?_ (hint j hj σ)
      exact (measurable_wenv hs hm hj σ).aemeasurable
    · have h1 : iteratedFDeriv ℝ j (fun k => a lam * Φ lam k) e = a lam • iteratedFDeriv ℝ j (Φ lam) e := by
        have := Layered.iteratedFDeriv_const_mul_param (hs lam) (a lam) hj e
        simpa only [mul_comm] using this
      rw [h1, norm_smul]
      have h2 := Regref.norm_le_sum_coordWords (iteratedFDeriv ℝ j (Φ lam) e)
      have h3 : ∑ σ : Fin j → Fin d, ‖iteratedFDeriv ℝ j (Φ lam) e (fun i => EuclideanSpace.single (σ i) 1)‖ ≤
          ∑ σ : Fin j → Fin d, (wenv Λ₂ σ (Φ lam)).toReal :=
        Finset.sum_le_sum fun σ _ => norm_le_toReal_wenv σ (Φ lam) (hfin j hj σ lam) e
      exact mul_le_mul (hab lam) (h2.trans h3) (norm_nonneg _) (le_trans (norm_nonneg _) (hab lam))

/-- **Momentum regularity and bounds of a frequency mixture.** -/
theorem mixture_bound {a : (Fin r → ℝ) → ℂ} {Ka : ℝ} (ha : Measurable a) (hab : ∀ lam, ‖a lam‖ ≤ Ka)
    (hs : ∀ lam, ContDiff ℝ N (Φ lam)) (hm : ∀ k, StronglyMeasurable fun lam => Φ lam k)
    (hfin : ∀ n ≤ N, ∀ σ : Fin n → Fin d, ∀ lam, wenv Λ₂ σ (Φ lam) < ⊤)
    (hint : ∀ n ≤ N, ∀ σ : Fin n → Fin d, ∫⁻ lam, wenv Λ₂ σ (Φ lam) ≠ ⊤) :
    ContDiff ℝ N (fun k => ∫ lam, a lam * Φ lam k) ∧
    ∀ n ≤ N, ∀ σ : Fin n → Fin d, ∀ k,
      ENNReal.ofReal (momentumBracket k ^ Λ₂ *
          ‖momentumDerivative σ (fun k => ∫ lam, a lam * Φ lam k) k‖) ≤
        ∫⁻ lam, ENNReal.ofReal ‖a lam‖ * wenv Λ₂ σ (Φ lam) := by
  obtain ⟨h1, h2, h3⟩ := mixture_hyps ha hab hs hm hfin hint
  refine ⟨Layered.contDiff_integral_param_of_le (μ := volume) h1 h2 h3, fun n hn σ k => ?_⟩
  have he := Layered.iteratedFDeriv_integral_param_of_le (μ := volume) h1 h2 h3 n hn
  have hval : momentumDerivative σ (fun k => ∫ lam, a lam * Φ lam k) k =
      ∫ lam, a lam * momentumDerivative σ (Φ lam) k := by
    unfold momentumDerivative
    rw [he]
    obtain ⟨B, hBi, hB⟩ := h3 n hn
    have hi : Integrable (fun lam => iteratedFDeriv ℝ n (fun k => a lam * Φ lam k) k) volume :=
      hBi.mono' (h2 n hn k) (by filter_upwards [hB] with lam hl using hl k)
    have hL := ContinuousLinearMap.integral_comp_comm
      (ContinuousMultilinearMap.apply ℝ (fun _ : Fin n => Mom d) ℂ
        (fun i => EuclideanSpace.single (σ i) (1 : ℝ))) hi
    simp only [ContinuousMultilinearMap.apply_apply] at hL
    rw [← hL]
    refine integral_congr_ae (ae_of_all _ fun lam => ?_)
    have h1' : iteratedFDeriv ℝ n (fun k => a lam * Φ lam k) k =
        a lam • iteratedFDeriv ℝ n (Φ lam) k := by
      have := Layered.iteratedFDeriv_const_mul_param (hs lam) (a lam) hn k
      simpa only [mul_comm] using this
    show (iteratedFDeriv ℝ n (fun k => a lam * Φ lam k) k) _ = a lam * (iteratedFDeriv ℝ n (Φ lam) k) _
    rw [h1']
    simp
  rw [hval]
  have hmul : ENNReal.ofReal (momentumBracket k ^ Λ₂ *
      ‖∫ lam, a lam * momentumDerivative σ (Φ lam) k‖) =
      ENNReal.ofReal (momentumBracket k ^ Λ₂) * ‖∫ lam, a lam * momentumDerivative σ (Φ lam) k‖ₑ := by
    rw [ENNReal.ofReal_mul (pow_nonneg (le_trans zero_le_one (one_le_momentumBracket k)) _), ofReal_norm]
  rw [hmul]
  calc ENNReal.ofReal (momentumBracket k ^ Λ₂) * ‖∫ lam, a lam * momentumDerivative σ (Φ lam) k‖ₑ
      ≤ ENNReal.ofReal (momentumBracket k ^ Λ₂) *
        ∫⁻ lam, ‖a lam * momentumDerivative σ (Φ lam) k‖ₑ :=
        mul_le_mul_right (enorm_integral_le_lintegral_enorm _) _
    _ = ∫⁻ lam, ENNReal.ofReal (momentumBracket k ^ Λ₂) * ‖a lam * momentumDerivative σ (Φ lam) k‖ₑ :=
        (lintegral_const_mul' _ _ ENNReal.ofReal_ne_top).symm
    _ ≤ ∫⁻ lam, ENNReal.ofReal ‖a lam‖ * wenv Λ₂ σ (Φ lam) := by
        refine lintegral_mono fun lam => ?_
        have hl := le_wenv (Λ₂ := Λ₂) σ (Φ lam) k
        calc ENNReal.ofReal (momentumBracket k ^ Λ₂) * ‖a lam * momentumDerivative σ (Φ lam) k‖ₑ
            = ENNReal.ofReal ‖a lam‖ *
              ENNReal.ofReal (momentumBracket k ^ Λ₂ * ‖momentumDerivative σ (Φ lam) k‖) := by
              rw [enorm_mul, ENNReal.ofReal_mul (pow_nonneg (le_trans zero_le_one
                (one_le_momentumBracket k)) _), ofReal_norm, ofReal_norm]
              ring
          _ ≤ ENNReal.ofReal ‖a lam‖ * wenv Λ₂ σ (Φ lam) := mul_le_mul_right hl _

end Mixture

end WaveTurbulence.VineEstS3.FS
