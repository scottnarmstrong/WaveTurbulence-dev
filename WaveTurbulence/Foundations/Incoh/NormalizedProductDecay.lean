/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Incoh.AbsorbedProductDecay
public import WaveTurbulence.Foundations.Incoh.CouplingScale

/-!
# The normalized localized product bound

TARGET (incohproof9), (incohproof16)–(incohproof18). This proves the
pointwise bulk bound for every time-order subdomain of the actual link boxes.
Fourier regularity requires the subsequent root-density construction.
-/

public section
noncomputable section
open MeasureTheory Set
open scoped ENNReal

namespace WaveTurbulence.Incoh

/-- The normalization converts the full bulk estimate into `(C₀δ)^n` and the incoherence decay. -/
theorem exists_normalizedLinkIntegral_bound (d : ℕ) (hd : 3 ≤ d) :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ γ : ℝ, γ ∈ Ioo (0 : ℝ) 1 →
      ∀ η : ℝ, 0 < η → η < incoherenceExponent d γ →
      ∀ δ : ℝ, 0 < δ → ∀ D : ℝ, 0 < D →
      ∃ L₀ : ℝ, 1 ≤ L₀ ∧ ∀ L ≥ L₀, ∀ n : ℕ, ∀ Q : Fin n → LayerLink d,
        (∀ i, |((Q i).leftLayer : ℝ) - (Q i).rightLayer| + 1 ≤ D) →
        ∀ I : Set (Fin n → Fin 2 → ℝ), I ⊆ univ.pi (fun i => linkBox (Q i)) →
        ‖normalizedLinkIntegral L γ δ Q I‖ₑ ≤
          ENNReal.ofReal ((C₀ * δ) ^ n * L ^ (-(incoherenceExponent d γ - 2 * η) * incoherenceCount Q)) := by
  obtain ⟨C₀, hC₀, hb⟩ := exists_absorbed_linkProduct_decay d hd
  refine ⟨C₀, hC₀, ?_⟩
  intro γ hγ η hη hηg δ hδ D hD
  obtain ⟨L₀, hL₀, hb⟩ := hb γ hγ η hη hηg δ hδ D hD
  refine ⟨L₀, hL₀, ?_⟩
  intro L hL n Q hspan I hI
  have hLp := zero_lt_one.trans_le (hL₀.trans hL)
  have hc : 0 ≤ (δ / (2 * L ^ ((d : ℝ) - γ))) ^ (2 * n) := by positivity
  have hnorm : ‖normalizedLinkIntegral L γ δ Q I‖ₑ =
      ENNReal.ofReal ((δ / (2 * L ^ ((d : ℝ) - γ))) ^ (2 * n)) *
        ‖∫ t in I, ∏ i, linkTimeFactor L γ δ (Q i) (t i)‖ₑ := by
    rw [normalizedLinkIntegral, enorm_mul]
    congr 1
    rw [← ofReal_norm]
    simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hc]
  rw [hnorm]
  calc
    _ ≤ ENNReal.ofReal ((δ / (2 * L ^ ((d : ℝ) - γ))) ^ (2 * n)) *
        ENNReal.ofReal ((C₀ * kineticLinkScale d γ δ L) ^ n *
          L ^ (-(incoherenceExponent d γ - 2 * η) * incoherenceCount Q)) :=
      mul_le_mul' le_rfl (hb L hL n Q hspan I hI)
    _ = ENNReal.ofReal (((δ / (2 * L ^ ((d : ℝ) - γ))) ^ (2 * n) *
        (C₀ * kineticLinkScale d γ δ L) ^ n) *
          L ^ (-(incoherenceExponent d γ - 2 * η) * incoherenceCount Q)) := by
      rw [← ENNReal.ofReal_mul hc, mul_assoc]
    _ ≤ _ := by
      apply ENNReal.ofReal_le_ofReal
      exact mul_le_mul_of_nonneg_right (coupling_scale_le hLp hδ hC₀.le γ) (Real.rpow_nonneg hLp.le _)

end WaveTurbulence.Incoh
