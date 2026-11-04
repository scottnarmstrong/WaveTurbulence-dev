/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Incoh.TreePhaseExtension

/-!
# Incoherence decay of the literal positive-regularity tree extensions

TARGET (incohproof28), for the phase/internal-clock representation. The
constant per link is dimensional. The Fourier prefactor depends only on
the fixed cutoff. Thresholds are uniform in the link family and its size.
-/

public section
noncomputable section
open MeasureTheory Set
open scoped ENNReal ContDiff

namespace WaveTurbulence.Incoh

/-- Positive regularity for both literal tree phase mixtures, with no assumed amplitude bound. -/
theorem exists_treePhaseExtension_quarter_bound (d : ℕ) (hd : 3 ≤ d) :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ χ : ℝ → ℝ, ContDiff ℝ ∞ χ → HasCompactSupport χ →
      ∃ C : ℝ, 0 < C ∧ ∀ γ : ℝ, γ ∈ Ioo (0 : ℝ) 1 →
      ∀ η : ℝ, 0 < η → η < incoherenceExponent d γ →
      ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∀ D : ℝ, 0 < D →
      ∃ L₀ : ℝ, 1 ≤ L₀ ∧ ∀ L ≥ L₀, ∀ n g k : ℕ, ∀ V : Type*,
        ∀ Q : V → Fin n → LayerLink d,
        (∀ v i, |((Q v i).leftLayer : ℝ) - (Q v i).rightLayer| + 1 ≤ D) →
        (∀ v, incoherenceCount (Q v) = g) → ∀ J : Finset (Fin n), J.card ≤ k →
        ∀ S : V → Set (Fin n → LinkMixturePoint d), (∀ v, MeasurableSet (S v)) →
        ∀ p : V → (Fin n → LinkMixturePoint d) → Mom 6, (∀ v, Measurable (p v)) →
        Fourier.mixedFourierNorm00 (1 / 4) (treePhaseExtensionU χ L γ δ Q J S p) ≤
          ENNReal.ofReal C * ENNReal.ofReal ((C₀ * δ) ^ n *
            L ^ (-(incoherenceExponent d γ - 2 * η) * g) * L ^ ((d : ℝ) * k)) ∧
        Fourier.mixedFourierNorm00 (1 / 4) (treePhaseExtensionV χ L γ δ Q J S p) ≤
          ENNReal.ofReal C * ENNReal.ofReal ((C₀ * δ) ^ n *
            L ^ (-(incoherenceExponent d γ - 2 * η) * g) * L ^ ((d : ℝ) * k)) := by
  obtain ⟨C₀, hC₀, hb⟩ := exists_normalizedReplacedLinkMass_decay d hd
  refine ⟨C₀, hC₀, ?_⟩
  intro χ hχ hcχ
  obtain ⟨C, hC, hu, hv⟩ := exists_universalRectangle_phase_bound hχ hcχ
  obtain ⟨h⟩ := Fourier.exists_cutoffControl hχ hcχ
  refine ⟨C, hC, ?_⟩
  intro γ hγ η hη hηg δ hδ hδ₁ D hD
  obtain ⟨L₀, hL₀, hb⟩ := hb γ hγ η hη hηg δ hδ hδ₁ D hD
  refine ⟨L₀, hL₀, ?_⟩
  intro L hL n g k V Q hspan hg J hJ S hS p hp
  let M := ENNReal.ofReal ((C₀ * δ) ^ n *
    L ^ (-(incoherenceExponent d γ - 2 * η) * g) * L ^ ((d : ℝ) * k))
  have hm (v : V) : normalizedReplacedLinkMass L γ δ (Q v) J ≤ M := by
    simpa only [hg v] using hb L hL n (Q v) (hspan v) k J hJ
  constructor
  · exact (treePhaseExtensionU_norm_le hχ.continuous.measurable h (hL₀.trans hL) hδ γ Q J S hS p hp hm).trans
      ((mul_le_mul' le_rfl hu).trans_eq (mul_comm M _))
  · exact (treePhaseExtensionV_norm_le hχ.continuous.measurable h (hL₀.trans hL) hδ γ Q J S hS p hp hm).trans
      ((mul_le_mul' le_rfl hv).trans_eq (mul_comm M _))

end WaveTurbulence.Incoh
