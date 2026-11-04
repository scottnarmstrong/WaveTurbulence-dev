/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Incoh.RootEnvelopeMass
public import WaveTurbulence.Foundations.Incoh.RootEnvelopeDominates
public import WaveTurbulence.Foundations.Incoh.AbsorbedReplacementDecay

/-!
# Uniform bounds for actual selected-coordinate densities

TARGET (incohproof18), (incohproof27): freezing `r` selected vertex times
costs at most `L^(dr)`. In particular two roots cost `L^(2d)` and four
boundary vertices cost `L^(4d)`. The density is always the actual marginal.
-/

public section
noncomputable section
open MeasureTheory Set
open scoped ENNReal

namespace WaveTurbulence.Incoh

/-- Actual selected-coordinate densities retain the full incoherence decay with the explicit `L^(dr)` loss. -/
theorem exists_selectedDensity_bound (d : ℕ) (hd : 3 ≤ d) :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ γ : ℝ, γ ∈ Ioo (0 : ℝ) 1 →
      ∀ η : ℝ, 0 < η → η < incoherenceExponent d γ →
      ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∀ D : ℝ, 0 < D →
      ∃ L₀ : ℝ, 1 ≤ L₀ ∧ ∀ L ≥ L₀, ∀ n : ℕ, ∀ Q : Fin n → LayerLink d,
        (∀ i, |((Q i).leftLayer : ℝ) - (Q i).rightLayer| + 1 ≤ D) →
        ∀ I : Set (Fin n → Fin 2 → ℝ), I ⊆ univ.pi (fun i => linkBox (Q i)) →
        ∀ r : ℕ, ∀ R : RootCoordinates n r, ∀ t : Fin r → ℝ,
        ‖R.linkDensity L γ δ Q I t‖ₑ ≤
          ENNReal.ofReal ((C₀ * δ) ^ n * L ^ (-(incoherenceExponent d γ - 2 * η) * incoherenceCount Q) *
            L ^ ((d : ℝ) * r)) := by
  obtain ⟨C₀, hC₀, hb⟩ := exists_absorbed_replacedLinkMass_decay d hd
  refine ⟨C₀, hC₀, ?_⟩
  intro γ hγ η hη hηg δ hδ hδ₁ D hD
  obtain ⟨L₀, hL₀, hb⟩ := hb γ hγ η hη hηg δ hδ hδ₁ D hD
  refine ⟨L₀, hL₀, ?_⟩
  intro L hL n Q hspan I hbox r R t
  have hLone := hL₀.trans hL
  have hLp := zero_lt_one.trans_le hLone
  have hc : 0 ≤ (δ / (2 * L ^ ((d : ℝ) - γ))) ^ (2 * n) := by positivity
  apply (R.enorm_linkDensity_le_envelope hLone hδ γ Q hbox t).trans
  calc
    _ ≤ ENNReal.ofReal ((δ / (2 * L ^ ((d : ℝ) - γ))) ^ (2 * n)) *
        (∏ i, replacedLinkMass L γ δ Q R.rootLinks i) :=
      mul_le_mul' le_rfl (R.lintegral_envelope_le_replacedMass hLone γ δ Q)
    _ ≤ ENNReal.ofReal ((δ / (2 * L ^ ((d : ℝ) - γ))) ^ (2 * n)) *
        ENNReal.ofReal ((C₀ * kineticLinkScale d γ δ L) ^ n *
          L ^ (-(incoherenceExponent d γ - 2 * η) * incoherenceCount Q) * L ^ ((d : ℝ) * r)) :=
      mul_le_mul' le_rfl (hb L hL n Q hspan r R.rootLinks R.card_rootLinks_le)
    _ = ENNReal.ofReal (((δ / (2 * L ^ ((d : ℝ) - γ))) ^ (2 * n) *
        (C₀ * kineticLinkScale d γ δ L) ^ n) *
          L ^ (-(incoherenceExponent d γ - 2 * η) * incoherenceCount Q) * L ^ ((d : ℝ) * r)) := by
      rw [← ENNReal.ofReal_mul hc]
      congr 1
      ring
    _ ≤ _ := by
      apply ENNReal.ofReal_le_ofReal
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (coupling_scale_le hLp hδ hC₀.le γ) (Real.rpow_nonneg hLp.le _))
        (Real.rpow_nonneg hLp.le _)

end WaveTurbulence.Incoh
