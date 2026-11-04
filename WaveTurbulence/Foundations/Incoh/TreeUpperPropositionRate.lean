/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Incoh.FullRawTreeUpperRestrictionDecay
public import WaveTurbulence.Foundations.Incoh.TreeCoefficientAbsorption
public import WaveTurbulence.Foundations.Incoh.FinalExponentLoss

/-! # TARGET Proposition 5.1: the printed tree rate on actual upper boxes -/

public section
noncomputable section
open MeasureTheory Set
open scoped ENNReal ContDiff

namespace WaveTurbulence.Incoh

/-- The raw tree source has the printed `30d,0` spatial order and square-root eta loss.
The lone leaf requires no decay premise; its temporary input has been removed exactly. -/
theorem exists_rawTreeKernel_upperPropositionRate (d : ℕ) (hd : 3 ≤ d) (B : ℝ) (hB : 0 ≤ B) :
    ∃ C₁ : ℝ, 0 < C₁ ∧ ∀ l : ℕ, l ≤ 2 → ∀ η : ℝ, 0 < η → η ≤ 1 / 100 →
      (100 * (d : ℝ)) ^ 2 * η ≤ 1 →
      ∀ χ : ℝ → ℝ, ContDiff ℝ ∞ χ → HasCompactSupport χ →
      ∀ γ : ℝ, γ ∈ Ioo (0 : ℝ) 1 → η < incoherenceExponent d γ →
      ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∀ D : ℝ, 0 < D →
      ∃ L₀ : ℝ, 1 ≤ L₀ ∧ ∀ L ≥ L₀, ∀ n m w : ℕ, m + 1 ≤ 3 * n →
        ∀ P : MomentumTreeData n m w, ∀ Q : Fin n → LayerLink d,
        (∀ i, |((Q i).leftLayer : ℝ) - (Q i).rightLayer| + 1 ≤ D) →
        1 ≤ incoherenceCount Q → ∀ R : RootCoordinates n, ∀ T : TreeClockFibers l Q,
        R.rootVertex 0 = T.selection.coordinates.rootVertex 0 →
        R.rootVertex 1 = T.selection.coordinates.rootVertex (Fin.last (l + 1)) →
        (∀ v ∈ R.rootBox Q, ∀ j, χ (v j) = 1) →
        (∀ v ∈ T.selection.coordinates.rootBox Q, ∀ j, χ (v j) = 1) →
        ∀ f : Fin m → Mom d → ℂ,
        (∀ a, Fourier.spatialNorm (40 * d) (40 * d) (f a) ≤ ENNReal.ofReal B) →
        ∀ E : Set (Fin 2 → ℝ), (∀ t ∈ E, t 1 ≤ t 0) →
        (∀ t ∈ E, ∀ j, χ (t j) = 1) → ∀ ζ : Circle, ∀ A : Set (Mom d),
        Fourier.mixedRestrictionNorm η (30 * d) 0 E A
          (fun t k => P.sourceTreeKernel ζ R L γ δ Q T.timeDomain f t k) ≤
            ENNReal.ofReal ((C₁ * δ) ^ n *
              L ^ (-(incoherenceExponent d γ - Real.sqrt η) * incoherenceCount Q)) := by
  obtain ⟨Cₗ, hCₗ, C₀, hC₀, hb⟩ := exists_rawTreeKernel_upperRestriction_bound d hd
  let C₁ := treeSourceExponentialCoefficient d (30 * d) (40 * d) (40 * d) B Cₗ * C₀
  have hC₁ : 0 < C₁ := mul_pos (treeSourceExponentialCoefficient_pos _ _ _ _ _ _) hC₀
  refine ⟨C₁, hC₁, ?_⟩
  intro l hl η hη hη₁ hsmall χ hχ hcχ γ hγ hηγ δ hδ hδ₁ D hD
  obtain ⟨L₀, hL₀, hb⟩ := hb l hl η hη hη₁ χ hχ hcχ γ hγ hηγ δ hδ hδ₁ D hD
  refine ⟨L₀, hL₀, ?_⟩
  intro L hL n m w hm P Q hspan hg R T hfirst hlast hχroot hχsel f hf E hforward hχext ζ A
  have hn := one_le_linkCount_of_incoherent Q hg
  have hLone := hL₀.trans hL
  have hraw := hb L hL n m w (30 * d) (40 * d) (40 * d) P Q hspan hg R T hfirst hlast
    hχroot hχsel f B (by omega) (by omega) hB hf E hforward hχext ζ A
  apply hraw.trans
  apply (tree_source_ennreal_coefficient_le hn hm hCₗ.le hC₀.le hδ.le
    (Real.rpow_nonneg (zero_le_one.trans hLone) _)).trans
  apply ENNReal.ofReal_le_ofReal
  change (C₁ * δ) ^ n * L ^ (-(incoherenceExponent d γ - 100 * (d : ℝ) * η) * incoherenceCount Q) ≤ _
  exact mul_le_mul_of_nonneg_left (incoherence_rpow_le_sqrt_loss hLone hη.le hsmall)
    (pow_nonneg (mul_nonneg hC₁.le hδ.le) _)

end WaveTurbulence.Incoh
