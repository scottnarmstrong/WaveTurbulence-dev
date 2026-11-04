/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Incoh.FullRawCoupleUpperRestrictionDecay
public import WaveTurbulence.Foundations.Incoh.ExponentialCoefficientAbsorption
public import WaveTurbulence.Foundations.Incoh.FinalExponentLoss

/-! # The printed Proposition 5.1 rate for literal raw couples

All source localization, derivative and weight coefficients are absorbed
into one order-independent exponential constant. The final square-root
eta loss is the one printed in TARGET (layerregest1).
-/

public section
noncomputable section
open MeasureTheory Set
open scoped ENNReal ContDiff

namespace WaveTurbulence.Incoh

/-- TARGET Proposition 5.1, the actual raw two-clock couple term, with the printed spatial
orders, source finite input budget and final incoherence exponent. -/
theorem exists_rawCoupleKernel_upper_propositionRate (d : ℕ) (hd : 3 ≤ d)
    (B : ℝ) (hB : 0 ≤ B) :
    ∃ C₁ : ℝ, 0 < C₁ ∧ ∀ η : ℝ, 0 < η → η ≤ 1 / 3 →
      (100 * (d : ℝ)) ^ 2 * η ≤ 1 →
      ∀ χ : ℝ → ℝ, ContDiff ℝ ∞ χ → HasCompactSupport χ → ∀ γ : ℝ, γ ∈ Ioo (0 : ℝ) 1 → η < incoherenceExponent d γ →
      ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∀ D : ℝ, 0 < D →
      ∃ L₀ : ℝ, 1 ≤ L₀ ∧ ∀ L ≥ L₀, ∀ n m w : ℕ, m ≤ 3 * n →
        ∀ P : MomentumTreeData n m w, RootInputCoordinates P →
        (∀ i p, p ∈ (P.tree i).leaves → P.leafInput i p ≠ none) →
        ∀ Q : Fin n → LayerLink d,
        (∀ i, |((Q i).leftLayer : ℝ) - (Q i).rightLayer| + 1 ≤ D) →
        1 ≤ incoherenceCount Q → ∀ R : RootCoordinates n,
        ∀ I : Set (Fin n → Fin 2 → ℝ), MeasurableSet I → I ⊆ univ.pi (fun i => linkBox (Q i)) →
        ∀ f : Fin m → Mom d → ℂ,
        (∀ a, Fourier.spatialNorm (40 * d) (40 * d) (f a) ≤ ENNReal.ofReal B) →
        ∀ E : Set (Fin 2 → ℝ), (∀ t ∈ E, R.baseRootTimes Q ≤ t) →
        (∀ t ∈ E, ∀ j : Fin 2, ∀ s ∈ Icc (0 : ℝ) ((t - R.baseRootTimes Q) j), χ s = 1) →
        ∀ ζ : Circle, ∀ A : Set (Mom d),
        Fourier.mixedRestrictionNorm η (30 * d) (30 * d) E A
          (fun t k => P.sourceCoupleKernel ζ R L γ δ Q I f t k) ≤
            ENNReal.ofReal ((C₁ * δ) ^ n *
              L ^ (-(incoherenceExponent d γ - Real.sqrt η) * incoherenceCount Q)) := by
  obtain ⟨Cₗ, hCₗ, C₀, hC₀, hb⟩ := exists_rawCoupleKernel_upperRestriction_bound d hd
  let C₁ := maskedSourceExponentialCoefficient d (30 * d) (40 * d) (30 * d) B Cₗ * C₀
  have hC₁ : 0 < C₁ := mul_pos (maskedSourceExponentialCoefficient_pos _ _ _ _ _ _) hC₀
  refine ⟨C₁, hC₁, ?_⟩
  intro η hη hη₁ hsmall χ hχ hcχ γ hγ hηγ δ hδ hδ₁ D hD
  obtain ⟨L₀, hL₀, hb⟩ := hb η hη hη₁ χ hχ hcχ γ hγ hηγ δ hδ hδ₁ D hD
  refine ⟨L₀, hL₀, ?_⟩
  intro L hL n m w hm P Croot hinputs Q hspan hg R I hI hbox f hf E hE hχone ζ A
  have hn := one_le_linkCount_of_incoherent Q hg
  have hLone := hL₀.trans hL
  have hraw := hb L hL n m w (30 * d) (30 * d) (40 * d) (40 * d) P Croot hinputs Q hspan hg
    R I hI hbox f B (by omega) (by omega) hB hf E hE hχone ζ A
  apply hraw.trans
  apply (masked_source_ennreal_coefficient_le hn hm hB hCₗ.le hC₀.le hδ.le
    (Real.rpow_nonneg (zero_le_one.trans hLone) _)).trans
  apply ENNReal.ofReal_le_ofReal
  change (C₁ * δ) ^ n * L ^ (-(incoherenceExponent d γ - 100 * (d : ℝ) * η) * incoherenceCount Q) ≤ _
  exact mul_le_mul_of_nonneg_left (incoherence_rpow_le_sqrt_loss hLone hη.le hsmall)
    (pow_nonneg (mul_nonneg hC₁.le hδ.le) _)

end WaveTurbulence.Incoh
