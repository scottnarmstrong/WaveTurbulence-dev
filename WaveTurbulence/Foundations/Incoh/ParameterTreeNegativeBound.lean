/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Incoh.ParameterTreeExtension
public import WaveTurbulence.Foundations.Incoh.GeneralTriangleNegativeNorm

/-!
# Negative regularity of actual tree families on arbitrary carriers

The scalar physical root bound and the landed N3 pointwise triangle bound
are uniform in all centers, Fourier shifts and remaining vector parameters.
-/

public section
noncomputable section
open MeasureTheory Set
open scoped ContDiff ENNReal

namespace WaveTurbulence.Incoh

/-- TARGET (incohproof26) for arbitrary source parameter families. -/
theorem exists_parameterTreeCausalExtension_negative_bound (d : ℕ) (hd : 3 ≤ d) :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ η : ℝ, 0 < η → η ≤ 1 / 3 →
      ∀ χ : ℝ → ℝ, ContDiff ℝ ∞ χ → HasCompactSupport χ →
      ∃ C : ℝ, 0 < C ∧ ∀ γ : ℝ, γ ∈ Ioo (0 : ℝ) 1 → η < incoherenceExponent d γ →
      ∀ δ : ℝ, 0 < δ → ∀ D : ℝ, 0 < D →
      ∃ L₀ : ℝ, 1 ≤ L₀ ∧ ∀ L ≥ L₀, ∀ n g : ℕ, ∀ V : Type*,
        ∀ Q : V → Fin n → LayerLink d,
        (∀ v i, |((Q v i).leftLayer : ℝ) - (Q v i).rightLayer| + 1 ≤ D) →
        (∀ v, incoherenceCount (Q v) = g) →
        ∀ I : V → Set (Fin n → Fin 2 → ℝ), (∀ v, MeasurableSet (I v)) →
        (∀ v, I v ⊆ univ.pi (fun i => linkBox (Q v i))) → ∀ R : RootCoordinates n,
        Fourier.mixedFourierNorm00 (-η) (R.parameterTreeCausalExtension χ L γ δ Q I) ≤
          ENNReal.ofReal C * ENNReal.ofReal ((C₀ * δ) ^ n *
            L ^ (-(incoherenceExponent d γ - 2 * η) * g)) := by
  obtain ⟨C₀, hC₀, hb⟩ := exists_rootDensity_L1_bound d hd
  refine ⟨C₀, hC₀, ?_⟩
  intro η hη _ χ hχ hcχ
  obtain ⟨hc⟩ := Fourier.exists_cutoffControl hχ hcχ
  let A := ENNReal.ofReal (4 * Fourier.negativeFrequencyConstant η) *
    Fourier.orderedFourMomentFactor hc.radius hc.bound * ENNReal.ofReal (hc.bound ^ 2)
  have hA : A ≠ ⊤ := by
    have hm := Fourier.orderedFourMomentFactor_ne_top hc.radius hc.bound
    dsimp only [A]
    finiteness
  let C : ℝ := 1 + A.toReal
  have hC : 0 < C := by dsimp only [C]; positivity
  have hAC : A ≤ ENNReal.ofReal C := by
    rw [← ENNReal.ofReal_toReal hA]
    exact ENNReal.ofReal_le_ofReal (by dsimp only [C]; linarith)
  refine ⟨C, hC, ?_⟩
  intro γ hγ hηγ δ hδ D hD
  obtain ⟨L₀, hL₀, hb⟩ := hb γ hγ η hη hηγ δ hδ D hD
  refine ⟨L₀, hL₀, ?_⟩
  intro L hL n g V Q hspan hcount I hI hbox R
  have hLp : 0 < L := zero_lt_one.trans_le (hL₀.trans hL)
  have hr (v : V) : eLpNorm (R.linkDensity L γ δ (Q v) (I v)) 1 ≤
      ENNReal.ofReal ((C₀ * δ) ^ n * L ^ (-(incoherenceExponent d γ - 2 * η) * g)) := by
    simpa only [hcount v] using hb L hL n (Q v) (hspan v) (I v) (hI v) (hbox v) R
  exact (mixedFourierNorm00_cutoffTriangle_le hη hχ hcχ hc
    (fun t v => R.linkDensity L γ δ (Q v) (I v) t)
    (fun v => R.integrable_linkDensity hLp γ δ (Q v) (hI v) (hbox v)) hr).trans
    (mul_le_mul' hAC le_rfl)

end WaveTurbulence.Incoh
