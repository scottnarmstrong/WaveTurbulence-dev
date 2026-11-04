/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Incoh.RootDensityL1
public import WaveTurbulence.Foundations.Fourier.TimeIntegralBounds
public import WaveTurbulence.Foundations.Fourier.Norm00V

/-!
# Negative regularity of the actual causal tree extension

TARGET (incohproof25)–(incohproof26). The root marginal is formed from the
literal normalized product over its actual measurable time-order domain.
The momentum supremum stays inside the Fourier integral.
-/

public section
noncomputable section
open MeasureTheory Set
open scoped ENNReal ContDiff

namespace WaveTurbulence.Incoh

/-- The causal cutoff extension of the actual root/lone-parent marginal. -/
@[expose] def RootCoordinates.treeCausalExtension {d n : ℕ} (R : RootCoordinates n)
    (χ : ℝ → ℝ) (L γ δ : ℝ) (Q : Mom d → Fin n → LayerLink d)
    (I : Mom d → Set (Fin n → Fin 2 → ℝ)) : (Fin 2 → ℝ) → Mom d → ℂ :=
  Fourier.cutoffJ χ (fun t k => R.linkDensity L γ δ (Q k) (I k) t)

/-- TARGET (incohproof26), with the stronger bulk exponent `γ₁−2η`. -/
theorem exists_treeCausalExtension_negative_bound (d : ℕ) (hd : 3 ≤ d) :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ η : ℝ, 0 < η → η ≤ 1 / 3 →
      ∀ χ : ℝ → ℝ, ContDiff ℝ ∞ χ → HasCompactSupport χ →
      ∃ C : ℝ, 0 < C ∧ ∀ γ : ℝ, γ ∈ Ioo (0 : ℝ) 1 → η < incoherenceExponent d γ →
      ∀ δ : ℝ, 0 < δ → ∀ D : ℝ, 0 < D →
      ∃ L₀ : ℝ, 1 ≤ L₀ ∧ ∀ L ≥ L₀, ∀ n g : ℕ,
        ∀ Q : Mom d → Fin n → LayerLink d,
        (∀ k i, |((Q k i).leftLayer : ℝ) - (Q k i).rightLayer| + 1 ≤ D) →
        (∀ k, incoherenceCount (Q k) = g) →
        ∀ I : Mom d → Set (Fin n → Fin 2 → ℝ), (∀ k, MeasurableSet (I k)) →
        (∀ k, I k ⊆ univ.pi (fun i => linkBox (Q k i))) → ∀ R : RootCoordinates n,
        Fourier.mixedFourierNorm00 (-η) (R.treeCausalExtension χ L γ δ Q I) ≤
          ENNReal.ofReal C * ENNReal.ofReal ((C₀ * δ) ^ n *
            L ^ (-(incoherenceExponent d γ - 2 * η) * g)) := by
  obtain ⟨C₀, hC₀, hb⟩ := exists_rootDensity_L1_bound d hd
  refine ⟨C₀, hC₀, ?_⟩
  intro η hη hη₁ χ hχ hcχ
  obtain ⟨C, hC, _, ht⟩ := Fourier.exists_cutoff_timeIntegral_bounds hη hη₁ hχ hcχ
  refine ⟨C, hC, ?_⟩
  intro γ hγ hηg δ hδ D hD
  obtain ⟨L₀, hL₀, hb⟩ := hb γ hγ η hη hηg δ hδ D hD
  refine ⟨L₀, hL₀, ?_⟩
  intro L hL n g Q hspan hg I hI hbox R
  have hm : Fourier.uniformTimeL1 (fun t k => R.linkDensity L γ δ (Q k) (I k) t) ≤
      ENNReal.ofReal ((C₀ * δ) ^ n * L ^ (-(incoherenceExponent d γ - 2 * η) * g)) := by
    apply iSup_le
    intro k
    simpa only [hg k] using hb L hL n (Q k) (hspan k) (I k) (hI k) (hbox k) R
  rw [Fourier.mixedFourierNorm00_eq_mixedFourierNorm]
  exact (ht d _).trans (mul_le_mul' le_rfl hm)

end WaveTurbulence.Incoh
