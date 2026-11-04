/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Incoh.FactoredLinkMass
public import WaveTurbulence.Foundations.Incoh.ConstantAbsorption

/-!
# Uniform one-link decay

TARGET (incohproof16): a fixed dimensional base constant for every link,
and a secondary constant only for incoherent links. All estimates are
proved for the literal masked lattice factor and its actual layer box.
-/

public section
noncomputable section
open MeasureTheory Set
open scoped ENNReal

namespace WaveTurbulence.Incoh

/-- TARGET's per-link estimate, with the base constant chosen before coupling and layer range. -/
theorem exists_oneLink_decay (d : ℕ) (hd : 3 ≤ d) :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ γ : ℝ, γ ∈ Ioo (0 : ℝ) 1 →
      ∀ η : ℝ, 0 < η → η < incoherenceExponent d γ →
      ∀ δ : ℝ, 0 < δ → ∀ D : ℝ, 0 < D →
      ∃ C₂ L₀ : ℝ, 1 ≤ C₂ ∧ 1 ≤ L₀ ∧ ∀ L ≥ L₀, ∀ Q : LayerLink d,
        |(Q.leftLayer : ℝ) - Q.rightLayer| + 1 ≤ D →
        (layerLinkMass L (δ * L ^ (2 * γ)) Q ≤ ENNReal.ofReal (C₀ * kineticLinkScale d γ δ L)) ∧
        (Q.IsIncoherent → layerLinkMass L (δ * L ^ (2 * γ)) Q ≤
          ENNReal.ofReal (C₀ * C₂ * kineticLinkScale d γ δ L * L ^ (-(incoherenceExponent d γ - η)))) := by
  obtain ⟨C, hC, hb⟩ := exists_factored_linkMass_bounds d hd
  refine ⟨C + 1, by positivity, ?_⟩
  intro γ hγ η hη hηg δ hδ D hD
  obtain ⟨B, L₁, hB, hL₁, hb⟩ := hb γ hγ η hη δ hδ D hD
  have hexp : 0 < 2 * ((d : ℝ) - 1) * (1 - γ) - η := by
    linarith [incoherenceExponent_le_longGain d γ]
  obtain ⟨L₂, hL₂, hsmall⟩ := exists_decaying_constant_threshold (C := B) hexp
  let C₂ : ℝ := max 1 (C * δ⁻¹ + B)
  have hC₂ : 1 ≤ C₂ := le_max_left _ _
  have hC₂₀ : 0 ≤ C₂ := zero_le_one.trans hC₂
  have hbig : C * δ⁻¹ + B ≤ (C + 1) * C₂ := by
    have hm : C * δ⁻¹ + B ≤ C₂ := le_max_right _ _
    nlinarith only [hm, mul_nonneg hC.le hC₂₀]
  refine ⟨C₂, max L₁ L₂, hC₂, (hL₁.trans (le_max_left _ _)), ?_⟩
  intro L hL Q hspan
  have hLa : L₁ ≤ L := (le_max_left _ _).trans hL
  have hLb : L₂ ≤ L := (le_max_right _ _).trans hL
  have hLone : 1 ≤ L := hL₁.trans hLa
  have hLp := zero_lt_one.trans_le hLone
  have hbase : 0 ≤ kineticLinkScale d γ δ L := by unfold kineticLinkScale; positivity
  have hdecay : B * L ^ (-(2 * ((d : ℝ) - 1) * (1 - γ)) + η) ≤ 1 := by
    have h := hsmall L hLb
    rw [show -(2 * ((d : ℝ) - 1) * (1 - γ) - η) =
      -(2 * ((d : ℝ) - 1) * (1 - γ)) + η by ring] at h
    exact h
  have hraw := hb L hLa Q hspan
  constructor
  · apply hraw.1.trans
    apply ENNReal.ofReal_le_ofReal
    calc
      _ ≤ kineticLinkScale d γ δ L * (C + 1) :=
        mul_le_mul_of_nonneg_left (add_le_add le_rfl hdecay) hbase
      _ = _ := by ring
  · intro hQ
    apply (hraw.2 hQ).trans
    apply ENNReal.ofReal_le_ofReal
    calc
      _ ≤ kineticLinkScale d γ δ L *
          ((C * δ⁻¹ + B) * L ^ (-(incoherenceExponent d γ - η))) :=
        mul_le_mul_of_nonneg_left (incoherent_gain_le hLone hη.le (by positivity) hB.le) hbase
      _ ≤ kineticLinkScale d γ δ L *
          (((C + 1) * C₂) * L ^ (-(incoherenceExponent d γ - η))) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hbig (Real.rpow_nonneg hLp.le _)) hbase
      _ = _ := by ring

end WaveTurbulence.Incoh
