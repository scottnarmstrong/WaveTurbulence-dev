/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Incoh.AbsorbedReplacementDecay
public import WaveTurbulence.Foundations.Incoh.CouplingScale

/-!
# Normalized mass after selected-link phase expansion

TARGET (incohproof27)–(incohproof28): selected links pay their actual
absolute phase coefficient bounds. Every other link keeps its integrated
oscillatory mass, including all incoherence gains.
-/

public section
noncomputable section
open Set
open scoped ENNReal

namespace WaveTurbulence.Incoh

/-- Coupling-normalized product mass, with selected links replaced only once. -/
@[expose] def normalizedReplacedLinkMass {d n : ℕ} (L γ δ : ℝ)
    (Q : Fin n → LayerLink d) (J : Finset (Fin n)) : ℝ≥0∞ :=
  ENNReal.ofReal ((δ / (2 * L ^ ((d : ℝ) - γ))) ^ (2 * n)) *
    ∏ i, replacedLinkMass L γ δ Q J i

/-- TARGET's selected-link loss, uniform in the number of links and the chosen set. -/
theorem exists_normalizedReplacedLinkMass_decay (d : ℕ) (hd : 3 ≤ d) :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ γ : ℝ, γ ∈ Ioo (0 : ℝ) 1 →
      ∀ η : ℝ, 0 < η → η < incoherenceExponent d γ →
      ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∀ D : ℝ, 0 < D →
      ∃ L₀ : ℝ, 1 ≤ L₀ ∧ ∀ L ≥ L₀, ∀ n : ℕ, ∀ Q : Fin n → LayerLink d,
        (∀ i, |((Q i).leftLayer : ℝ) - (Q i).rightLayer| + 1 ≤ D) →
        ∀ k : ℕ, ∀ J : Finset (Fin n), J.card ≤ k →
        normalizedReplacedLinkMass L γ δ Q J ≤
          ENNReal.ofReal ((C₀ * δ) ^ n *
            L ^ (-(incoherenceExponent d γ - 2 * η) * incoherenceCount Q) * L ^ ((d : ℝ) * k)) := by
  obtain ⟨C₀, hC₀, hb⟩ := exists_absorbed_replacedLinkMass_decay d hd
  refine ⟨C₀, hC₀, ?_⟩
  intro γ hγ η hη hηg δ hδ hδ₁ D hD
  obtain ⟨L₀, hL₀, hb⟩ := hb γ hγ η hη hηg δ hδ hδ₁ D hD
  refine ⟨L₀, hL₀, ?_⟩
  intro L hL n Q hspan k J hJ
  have hLp := zero_lt_one.trans_le (hL₀.trans hL)
  have hc : 0 ≤ (δ / (2 * L ^ ((d : ℝ) - γ))) ^ (2 * n) := by positivity
  unfold normalizedReplacedLinkMass
  apply (mul_le_mul' le_rfl (hb L hL n Q hspan k J hJ)).trans
  rw [← ENNReal.ofReal_mul hc]
  apply ENNReal.ofReal_le_ofReal
  calc
    _ = (((δ / (2 * L ^ ((d : ℝ) - γ))) ^ (2 * n) *
        (C₀ * kineticLinkScale d γ δ L) ^ n) *
        L ^ (-(incoherenceExponent d γ - 2 * η) * incoherenceCount Q)) * L ^ ((d : ℝ) * k) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (coupling_scale_le hLp hδ hC₀.le γ)
        (Real.rpow_nonneg hLp.le _)) (Real.rpow_nonneg hLp.le _)

end WaveTurbulence.Incoh
