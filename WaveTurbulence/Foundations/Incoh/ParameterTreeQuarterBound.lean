/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Incoh.ParameterTreeExtension
public import WaveTurbulence.Foundations.Incoh.CausalTreePhaseDecay

/-!
# Quarter regularity of the actual causal tree extension

The proved global phase identity transfers the literal mixture estimate
to the same source root marginal used by the negative-regularity bound.
-/

public section
noncomputable section
open MeasureTheory Set
open scoped ContDiff ENNReal

namespace WaveTurbulence.Incoh

/-- TARGET (incohproof28), for the actual common extension, with only two selected-link losses. -/
theorem exists_parameterTreeCausalExtension_quarter_bound (d : ℕ) (hd : 3 ≤ d) :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ m : ℕ, m ≤ 2 →
      ∀ χ : ℝ → ℝ, ContDiff ℝ ∞ χ → HasCompactSupport χ →
      ∃ C : ℝ, 0 < C ∧ ∀ γ : ℝ, γ ∈ Ioo (0 : ℝ) 1 →
      ∀ η : ℝ, 0 < η → η < incoherenceExponent d γ →
      ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∀ D : ℝ, 0 < D →
      ∃ L₀ : ℝ, 1 ≤ L₀ ∧ ∀ L ≥ L₀, ∀ n g : ℕ, ∀ V : Type*,
        ∀ Q : V → Fin n → LayerLink d,
        (∀ k i, |((Q k i).leftLayer : ℝ) - (Q k i).rightLayer| + 1 ≤ D) →
        (∀ k, incoherenceCount (Q k) = g) →
        ∀ T : (∀ k, TreeClockFibers m (Q k)), ∀ R : RootCoordinates n,
        ∀ J : Finset (Fin n), J.card ≤ 2 →
        (∀ k, R.rootVertex 0 = (T k).selection.coordinates.rootVertex 0) →
        (∀ k, R.rootVertex 1 = (T k).selection.coordinates.rootVertex (Fin.last (m + 1))) →
        (∀ k, (T k).selection.coordinates.rootLinks = J) →
        (∀ k v, v ∈ R.rootBox (Q k) → ∀ j, χ (v j) = 1) →
        (∀ k v, v ∈ (T k).selection.coordinates.rootBox (Q k) → ∀ j, χ (v j) = 1) →
        Fourier.mixedFourierNorm00 (1 / 4)
          (R.parameterTreeCausalExtension χ L γ δ Q (fun k => (T k).timeDomain)) ≤
          ENNReal.ofReal C * ENNReal.ofReal ((C₀ * δ) ^ n *
            L ^ (-(incoherenceExponent d γ - 2 * η) * g) * L ^ ((d : ℝ) * 2)) := by
  obtain ⟨C₀, hC₀, hb⟩ := exists_treeCausalPhaseExtension_quarter_bound d hd
  refine ⟨C₀, hC₀, ?_⟩
  intro m hm χ hχ hcχ
  obtain ⟨C, hC, hb⟩ := hb m χ hχ hcχ
  obtain ⟨hc⟩ := Fourier.exists_cutoffControl hχ hcχ
  refine ⟨C, hC, ?_⟩
  intro γ hγ η hη hηγ δ hδ hδ₁ D hD
  obtain ⟨L₀, hL₀, hb⟩ := hb γ hγ η hη hηγ δ hδ hδ₁ D hD
  refine ⟨L₀, hL₀, ?_⟩
  intro L hL n g V Q hspan hg T R J hj hfirst hlast hJ hχroot hχsel
  have he := parameterTreeCausalExtension_eq_phaseKernel R Q T hfirst hlast
    (zero_lt_one.trans_le (hL₀.trans hL)) γ δ hχ.continuous.measurable hc hχroot hχsel
  have hr : R.parameterTreeCausalExtension χ L γ δ Q (fun k => (T k).timeDomain) =
      treeCausalPhaseExtension m χ L γ δ Q J
        (fun k => (T k).mixtureDomain) (fun k => (T k).mixtureParameters L γ δ) := by
    rw [he]
    funext t k
    unfold TreeClockFibers.causalPhaseKernel treeCausalPhaseExtension
    rw [hJ k]
  rw [hr]
  exact hb L hL n g 2 V Q hspan hg J hj
    (fun k => (T k).mixtureDomain) (fun k => (T k).measurableSet_mixtureDomain)
    (fun k => (T k).mixtureParameters L γ δ) (fun k => (T k).measurable_mixtureParameters L γ δ)

end WaveTurbulence.Incoh
