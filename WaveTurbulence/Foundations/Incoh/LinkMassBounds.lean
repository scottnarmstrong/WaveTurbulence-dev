/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Incoh.FrequencySplit

/-!
# Full one-link mass bounds

TARGET (incohproof13)–(incohproof16). The short-time constant is selected
before the coupling and time-range parameters. The long-time constant is
kept separate until its decay is absorbed at a large-box threshold.
-/

public section
noncomputable section
open MeasureTheory Set
open scoped ENNReal

namespace WaveTurbulence.Incoh

/-- Full literal link mass, with the exact coherent and incoherent frequency-scale factors. -/
theorem exists_linkMass_bounds (d : ℕ) (hd : 3 ≤ d) :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ γ : ℝ, γ ∈ Ioo (0 : ℝ) 1 → ∀ η : ℝ, 0 < η →
      ∀ δ : ℝ, 0 < δ → ∀ D : ℝ, 0 < D →
      ∃ C₁ L₀ : ℝ, 0 < C₁ ∧ 1 ≤ L₀ ∧ ∀ L ≥ L₀, ∀ Q : LayerLink d,
        |(Q.leftLayer : ℝ) - Q.rightLayer| + 1 ≤ D →
        (layerLinkMass L (δ * L ^ (2 * γ)) Q ≤
          ENNReal.ofReal (δ * L ^ (2 * γ))⁻¹ *
            (ENNReal.ofReal (C₀ * L ^ (2 * d)) +
              ENNReal.ofReal (C₁ * L ^ (2 * (d : ℝ) - 2 * ((d : ℝ) - 1) * (1 - γ) + η)))) ∧
        (Q.IsIncoherent → layerLinkMass L (δ * L ^ (2 * γ)) Q ≤
          (ENNReal.ofReal (δ * L ^ (2 * γ))⁻¹) ^ 2 * ENNReal.ofReal (C₀ * L ^ (2 * d)) +
            ENNReal.ofReal (δ * L ^ (2 * γ))⁻¹ *
              ENNReal.ofReal (C₁ * L ^ (2 * (d : ℝ) - 2 * ((d : ℝ) - 1) * (1 - γ) + η))) := by
  obtain ⟨C₀, hC₀, hs⟩ := exists_shortTime_box_bounds d hd
  refine ⟨C₀, hC₀, ?_⟩
  intro γ hγ η hη δ hδ D hD
  obtain ⟨C₁, L₀, hC₁, hL₀, hl⟩ := exists_longTime_box_bounds d hd γ hγ η hη (D * δ) (mul_pos hD hδ)
  refine ⟨C₁, L₀, hC₁, hL₀, ?_⟩
  intro L hL Q hspan
  have hL₁ := hL₀.trans hL
  have hLp := zero_lt_one.trans_le hL₁
  have hscale : 0 < δ * L ^ (2 * γ) := by positivity
  have hshort := hs L hL₁ (δ * L ^ (2 * γ)) hscale Q
  have hlong := hl L hL (δ * L ^ (2 * γ)) hscale Q
  have hwindow : (D * δ) * L ^ (2 * γ) = D * (δ * L ^ (2 * γ)) := by ring
  rw [hwindow] at hlong
  have hsplit := layerLinkMass_le_short_add_long hLp hscale.le Q hspan
  constructor
  · rw [mul_add]
    exact hsplit.trans (add_le_add hshort.1 hlong)
  · intro hQ
    exact hsplit.trans (add_le_add (hshort.2 hQ) hlong)

end WaveTurbulence.Incoh
