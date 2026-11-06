/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Spine.PL2330Draft.MultNorm
public import WaveTurbulence.Foundations.Fourier.TimeProduct

/-!
# Weighted convolution estimates and measurability of the operator envelopes (PL23-30D)

* `ae_lintegral_conv_lt_top`: the convolution of two nonnegative integrable functions is finite almost
  everywhere;
* `lintegral_conv_weight_le`: `∫ w_θ (E₁ ⋆ E₂) ≤ 2^θ (∫ w_θ E₁)(∫ w_θ E₂)` (`θ ≥ 0`);
* `measurable_dsup`: `ξ ↦ dsup Λ₂ i (Φ ξ)` is measurable for `Φ` smooth in `k` and measurable in `ξ`.
-/

@[expose] public section

open MeasureTheory Set Filter Finset
open scoped ENNReal ContDiff

namespace WaveTurbulence.PL2330

open WaveTurbulence.Fourier WaveTurbulence.Regref

variable {r d : ℕ}

theorem measurable_conv {E₁ E₂ : (Fin r → ℝ) → ℝ≥0∞} (h1 : Measurable E₁) (h2 : Measurable E₂) :
    Measurable fun ξ => ∫⁻ η, E₁ (ξ - η) * E₂ η := by
  have hjoint : Measurable (fun p : (Fin r → ℝ) × (Fin r → ℝ) => E₁ (p.1 - p.2) * E₂ p.2) :=
    (h1.comp (measurable_fst.sub measurable_snd)).mul (h2.comp measurable_snd)
  exact hjoint.lintegral_prod_right'

theorem lintegral_conv_eq {E₁ E₂ : (Fin r → ℝ) → ℝ≥0∞} (h1 : Measurable E₁) (h2 : Measurable E₂) :
    ∫⁻ ξ, ∫⁻ η, E₁ (ξ - η) * E₂ η = (∫⁻ ξ, E₁ ξ) * ∫⁻ η, E₂ η := by
  have hjoint : Measurable (fun p : (Fin r → ℝ) × (Fin r → ℝ) => E₁ (p.1 - p.2) * E₂ p.2) :=
    (h1.comp (measurable_fst.sub measurable_snd)).mul (h2.comp measurable_snd)
  calc ∫⁻ ξ, ∫⁻ η, E₁ (ξ - η) * E₂ η = ∫⁻ η, ∫⁻ ξ, E₁ (ξ - η) * E₂ η :=
        lintegral_lintegral_swap hjoint.aemeasurable
    _ = ∫⁻ η, (∫⁻ ξ, E₁ ξ) * E₂ η := by
        refine lintegral_congr fun η => ?_
        have hm1 : Measurable fun ξ : Fin r → ℝ => E₁ (ξ - η) := h1.comp (measurable_id.sub_const η)
        rw [lintegral_mul_const (f := fun ξ : Fin r → ℝ => E₁ (ξ - η)) _ hm1, lintegral_sub_right_eq_self]
    _ = _ := lintegral_const_mul _ h2

theorem ae_lintegral_conv_lt_top {E₁ E₂ : (Fin r → ℝ) → ℝ≥0∞} (h1 : Measurable E₁) (h2 : Measurable E₂)
    (f1 : ∫⁻ ξ, E₁ ξ ≠ ⊤) (f2 : ∫⁻ ξ, E₂ ξ ≠ ⊤) : ∀ᵐ ξ, ∫⁻ η, E₁ (ξ - η) * E₂ η < ⊤ := by
  refine ae_lt_top (measurable_conv h1 h2) ?_
  rw [lintegral_conv_eq h1 h2]
  exact ENNReal.mul_ne_top f1 f2

/-- **The weighted convolution estimate.** -/
theorem lintegral_conv_weight_le {θ : ℝ} (hθ : 0 ≤ θ) {E₁ E₂ : (Fin r → ℝ) → ℝ≥0∞} (h1 : Measurable E₁)
    (h2 : Measurable E₂) :
    ∫⁻ ξ, timeWeight θ ξ * ∫⁻ η, E₁ (ξ - η) * E₂ η ≤
      ENNReal.ofReal (2 ^ θ) * (∫⁻ ξ, timeWeight θ ξ * E₁ ξ) * ∫⁻ ξ, timeWeight θ ξ * E₂ ξ := by
  have hu : Measurable fun ξ => timeWeight θ ξ * E₁ ξ := (timeWeight_measurable θ).mul h1
  have hv : Measurable fun ξ => timeWeight θ ξ * E₂ ξ := (timeWeight_measurable θ).mul h2
  have hpoint : ∀ ξ, timeWeight θ ξ * ∫⁻ η, E₁ (ξ - η) * E₂ η ≤
      ∫⁻ η, ENNReal.ofReal (2 ^ θ) * (timeWeight θ (ξ - η) * E₁ (ξ - η)) * (timeWeight θ η * E₂ η) := by
    intro ξ
    have hm : Measurable (fun η => E₁ (ξ - η) * E₂ η) :=
      (h1.comp (measurable_const.sub measurable_id)).mul h2
    rw [← lintegral_const_mul _ hm]
    refine lintegral_mono fun η => ?_
    have hw := timeWeight_add_le hθ (ξ - η) η
    rw [sub_add_cancel] at hw
    calc timeWeight θ ξ * (E₁ (ξ - η) * E₂ η)
        ≤ (ENNReal.ofReal (2 ^ θ) * timeWeight θ (ξ - η) * timeWeight θ η) * (E₁ (ξ - η) * E₂ η) :=
          mul_le_mul_left hw _
      _ = _ := by ring
  have hjoint : Measurable (fun p : (Fin r → ℝ) × (Fin r → ℝ) =>
      ENNReal.ofReal (2 ^ θ) * (timeWeight θ (p.1 - p.2) * E₁ (p.1 - p.2)) * (timeWeight θ p.2 * E₂ p.2)) :=
    (measurable_const.mul (hu.comp (measurable_fst.sub measurable_snd))).mul (hv.comp measurable_snd)
  calc ∫⁻ ξ, timeWeight θ ξ * ∫⁻ η, E₁ (ξ - η) * E₂ η
      ≤ ∫⁻ ξ, ∫⁻ η, ENNReal.ofReal (2 ^ θ) * (timeWeight θ (ξ - η) * E₁ (ξ - η)) *
        (timeWeight θ η * E₂ η) := lintegral_mono hpoint
    _ = ∫⁻ η, ∫⁻ ξ, ENNReal.ofReal (2 ^ θ) * (timeWeight θ (ξ - η) * E₁ (ξ - η)) *
        (timeWeight θ η * E₂ η) := lintegral_lintegral_swap hjoint.aemeasurable
    _ = ∫⁻ η, (ENNReal.ofReal (2 ^ θ) * ∫⁻ ξ, timeWeight θ ξ * E₁ ξ) * (timeWeight θ η * E₂ η) := by
        refine lintegral_congr fun η => ?_
        have hm1 : Measurable fun ξ : Fin r → ℝ => timeWeight θ (ξ - η) * E₁ (ξ - η) :=
          hu.comp (measurable_id.sub_const η)
        rw [lintegral_mul_const (f := fun ξ : Fin r → ℝ => ENNReal.ofReal (2 ^ θ) *
          (timeWeight θ (ξ - η) * E₁ (ξ - η))) _ (measurable_const.mul hm1),
          lintegral_const_mul (f := fun ξ : Fin r → ℝ => timeWeight θ (ξ - η) * E₁ (ξ - η)) _ hm1,
          lintegral_sub_right_eq_self (f := fun ξ : Fin r → ℝ => timeWeight θ ξ * E₁ ξ)]
    _ = _ := by
        rw [lintegral_const_mul _ hv]

theorem measurable_dsup {Λ : ℕ} {Φ : (Fin r → ℝ) → Mom d → ℂ} (Λ₂ : ℕ)
    (hs : ∀ ξ, ContDiff ℝ Λ (Φ ξ)) (hm : ∀ k, StronglyMeasurable fun ξ => Φ ξ k)
    {i : ℕ} (hi : i ≤ Λ) : Measurable fun ξ => dsup Λ₂ i (Φ ξ) := by
  obtain ⟨D, hDc, hD⟩ := TopologicalSpace.exists_countable_dense (Mom d)
  have : Countable D := hDc.to_subtype
  have he : (fun ξ => dsup Λ₂ i (Φ ξ)) =
      fun ξ => ⨆ q : D, ENNReal.ofReal (momentumBracket q.1 ^ Λ₂) * ‖iteratedFDeriv ℝ i (Φ ξ) q.1‖ₑ := by
    funext ξ
    unfold dsup
    have hco : Continuous fun k : Mom d => ENNReal.ofReal (momentumBracket k ^ Λ₂) *
        ‖iteratedFDeriv ℝ i (Φ ξ) k‖ₑ := by
      have h1 : (fun k : Mom d => ENNReal.ofReal (momentumBracket k ^ Λ₂) *
          ‖iteratedFDeriv ℝ i (Φ ξ) k‖ₑ) =
          fun k => ENNReal.ofReal (momentumBracket k ^ Λ₂ * ‖iteratedFDeriv ℝ i (Φ ξ) k‖) := by
        funext k
        rw [ENNReal.ofReal_mul (pow_nonneg (momentumBracket_nonneg k) _), ofReal_norm]
      rw [h1]
      exact ENNReal.continuous_ofReal.comp
        ((continuous_momentumBracket.pow Λ₂).mul
          (continuous_norm.comp ((hs ξ).continuous_iteratedFDeriv (by exact_mod_cast hi))))
    exact iSup_eq_iSup_dense hD hco
  rw [he]
  refine Measurable.iSup fun q => ?_
  have hsm := stronglyMeasurable_iteratedFDeriv_param_of_le (f := fun k ξ => Φ ξ k) hs hm i hi q.1
  exact measurable_const.mul hsm.enorm

end WaveTurbulence.PL2330
