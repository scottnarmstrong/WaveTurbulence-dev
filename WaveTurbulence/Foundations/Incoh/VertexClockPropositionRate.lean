/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Incoh.FullRawVertexClockRestrictionDecay
public import WaveTurbulence.Foundations.Incoh.ExponentialCoefficientAbsorption
public import WaveTurbulence.Foundations.Incoh.FinalExponentLoss

/-! # The printed Proposition 5.1 rate for literal raw one-clock couples

All source localization, derivative and weight coefficients are absorbed
into one order-independent exponential constant. The final square-root
eta loss is the one printed in TARGET (layerregest1).
-/

public section
noncomputable section
open MeasureTheory Set
open scoped ENNReal

namespace WaveTurbulence.Incoh

/-- TARGET Proposition 5.1, the actual raw one-clock couple term, with the printed spatial
orders, source finite input budget and final incoherence exponent. -/
theorem exists_rawVertexClockKernel_propositionRate (d : ℕ) (hd : 3 ≤ d)
    (η : ℝ) (hη : 0 < η) (hη₁ : η ≤ 1 / 3)
    (hsmall : (100 * (d : ℝ)) ^ 2 * η ≤ 1) (B : ℝ) (hB : 0 ≤ B) :
    ∃ C₁ : ℝ, 0 < C₁ ∧ ∀ γ : ℝ, γ ∈ Ioo (0 : ℝ) 1 → η < incoherenceExponent d γ →
      ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∀ D : ℝ, 0 < D →
      ∃ L₀ : ℝ, 1 ≤ L₀ ∧ ∀ L ≥ L₀, ∀ n m w : ℕ, m ≤ 3 * n →
        ∀ P : MomentumTreeData n m w, RootInputCoordinates P →
        (∀ i p, p ∈ (P.tree i).leaves → P.leafInput i p ≠ none) →
        ∀ Q : Fin n → LayerLink d,
        (∀ i, |((Q i).leftLayer : ℝ) - (Q i).rightLayer| + 1 ≤ D) →
        1 ≤ incoherenceCount Q → ∀ v : Fin n × Fin 2, ∀ a : Fin 2, ∀ b : ℝ,
        ∀ I : Set (Fin n → Fin 2 → ℝ), MeasurableSet I → I ⊆ univ.pi (fun i => linkBox (Q i)) →
        ∀ f : Fin m → Mom d → ℂ,
        (∀ a, Fourier.spatialNorm (40 * d) (40 * d) (f a) ≤ ENNReal.ofReal B) →
        ∀ ζ : Circle, ∀ A : Set (Mom d),
        Fourier.mixedRestrictionNorm η (30 * d) (30 * d) (vertexClockBox v a Q b) A
          (fun t k => P.sourceVertexClockKernel ζ v a L γ δ Q I f t k) ≤
            ENNReal.ofReal ((C₁ * δ) ^ n *
              L ^ (-(incoherenceExponent d γ - Real.sqrt η) * incoherenceCount Q)) := by
  obtain ⟨Cₗ, hCₗ, hb⟩ := exists_rawVertexClockKernel_fullRestriction_bound d hd
  obtain ⟨C₀, hC₀, hb⟩ := hb η hη hη₁
  let C₁ := maskedSourceExponentialCoefficient d (30 * d) (40 * d) (30 * d) B Cₗ * C₀
  have hC₁ : 0 < C₁ := mul_pos (maskedSourceExponentialCoefficient_pos _ _ _ _ _ _) hC₀
  refine ⟨C₁, hC₁, ?_⟩
  intro γ hγ hηγ δ hδ hδ₁ D hD
  obtain ⟨L₀, hL₀, hb⟩ := hb γ hγ hηγ δ hδ hδ₁ D hD
  refine ⟨L₀, hL₀, ?_⟩
  intro L hL n m w hm P Croot hinputs Q hspan hg v a b I hI hbox f hf ζ A
  have hn := one_le_linkCount_of_incoherent Q hg
  have hLone := hL₀.trans hL
  have hraw := hb L hL n m w (30 * d) (30 * d) (40 * d) (40 * d) P Croot hinputs Q hspan hg
    v a b I hI hbox f B (by omega) (by omega) hB hf ζ A
  apply hraw.trans
  apply (masked_source_ennreal_coefficient_le hn hm hB hCₗ.le hC₀.le hδ.le
    (Real.rpow_nonneg (zero_le_one.trans hLone) _)).trans
  apply ENNReal.ofReal_le_ofReal
  change (C₁ * δ) ^ n * L ^ (-(incoherenceExponent d γ - 100 * (d : ℝ) * η) * incoherenceCount Q) ≤ _
  exact mul_le_mul_of_nonneg_left (incoherence_rpow_le_sqrt_loss hLone hη.le hsmall)
    (pow_nonneg (mul_nonneg hC₁.le hδ.le) _)

end WaveTurbulence.Incoh
