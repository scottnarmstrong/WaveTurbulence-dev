/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.FiltGate.Quarter
public import WaveTurbulence.Foundations.Flower.FiltProd.Sel

/-! # D5b-3 FILT-GATE: the filtered `θ = 1/4` couple cell bound (o82 Lemma 16.1 with the filters)

`exists_coupleExtension_quarter_decayFilt`: `Quarter.exists_coupleExtension_quarter_decay` for D5b-1's filtered
canonical couple extension `RootCoordinates.coupleExtensionFilt`, over D5b-2's filtered endpoint bounds
`exists_rootDensityFilt_endpoint_bounds` (o82 §15: the filters change only the base constant, `K * C₀`). -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped ENNReal ContDiff

namespace WaveTurbulence.Flower.FiltGate
open WaveTurbulence.Incoh WaveTurbulence.Flower.FiltLink WaveTurbulence.Flower.FiltSrc
  WaveTurbulence.Flower.FiltProd

/-- **o82 Lemma 16.1, filtered incoherent couple**: the `X^{1/4}` cell bound with loss `L^{4d}`. -/
theorem exists_coupleExtension_quarter_decayFilt (d : ℕ) (hd : 3 ≤ d) :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ η : ℝ, 0 < η →
      ∀ χ : ℝ → ℝ, ContDiff ℝ ∞ χ → HasCompactSupport χ →
      ∀ γ : ℝ, γ ∈ Ioo (0 : ℝ) 1 → η < incoherenceExponent d γ →
      ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∀ D : ℝ, 0 < D →
      ∃ L₀ : ℝ, 1 ≤ L₀ ∧ ∀ L ≥ L₀, ∀ n : ℕ, ∀ Q : Fin n → LayerLink d,
        1 ≤ incoherenceCount Q →
        (∀ i, |((Q i).leftLayer : ℝ) - (Q i).rightLayer| + 1 ≤ D) →
        ∀ (K : ℝ), 0 ≤ K → ∀ φ : Fin n → ℝ → ℂ, (∀ i, PresentedMult L K (φ i)) →
        ∀ I : Set (Fin n → Fin 2 → ℝ), MeasurableSet I → I ⊆ univ.pi (fun i => linkBox (Q i)) →
        ∀ R : RootCoordinates n,
        Fourier.timeFourierNorm (1 / 4) (RootCoordinates.coupleExtensionFilt R χ L γ δ Q φ I) ≤
          ENNReal.ofReal ((K * C₀ * δ) ^ n *
            L ^ (-(incoherenceExponent d γ - 100 * (d : ℝ) * η) * incoherenceCount Q) *
              L ^ (4 * (d : ℝ))) := by
  obtain ⟨C₀, hC₀, hb⟩ := exists_rootDensityFilt_endpoint_bounds d hd
  refine ⟨C₀, hC₀, ?_⟩
  intro η hη χ hχ hcχ
  obtain ⟨Cₜ, hCₜ, htime⟩ := exists_translated_quarter_bound hχ hcχ
  obtain ⟨Lₐ, hLₐ, ha⟩ := exists_constant_absorption_threshold Cₜ hη
  intro γ hγ hηg δ hδ hδ₁ D hD
  obtain ⟨Lᵦ, hLᵦ, hb⟩ := hb γ hγ η hη hηg δ hδ hδ₁ D hD
  refine ⟨max Lₐ Lᵦ, hLₐ.trans (le_max_left _ _), ?_⟩
  intro L hL n Q hg hspan K hK φ hφ I hI hbox R
  have hLa := (le_max_left Lₐ Lᵦ).trans hL
  have hLb := (le_max_right Lₐ Lᵦ).trans hL
  have hLone := hLₐ.trans hLa
  have hLp := zero_lt_one.trans_le hLone
  obtain ⟨h1, hinf⟩ := hb L hLb n Q hspan K hK φ hφ I hI hbox R
  have hgR : (1 : ℝ) ≤ incoherenceCount Q := by exact_mod_cast hg
  have hCt : Cₜ ≤ L ^ (η * incoherenceCount Q) := (ha L hLa).trans
    (Real.rpow_le_rpow_of_exponent_le hLone (by nlinarith only [hgR, hη.le]))
  have hΛ : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (L ^ (2 * (d : ℝ))) := by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal (Real.one_le_rpow hLone (by positivity))
  have hq := htime (RootCoordinates.linkDensityFilt R L γ δ Q φ I) (R.baseRootTimes Q)
    (RootCoordinates.integrable_linkDensityFilt R hLp γ δ Q φ hI hbox).aestronglyMeasurable _ _ hΛ h1 hinf
  exact hq.trans (quarter_cell_rate_le (by omega) hLone hη.le (by positivity) hCₜ.le hCt)

end WaveTurbulence.Flower.FiltGate
