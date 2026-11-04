/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Incoh.TreeRootSourceAgreement
public import WaveTurbulence.Foundations.Incoh.CoupleLinkCellLocalization
public import WaveTurbulence.Foundations.Fourier.Norm00VRestriction

/-!
# Incoherence decay for the literal raw source tree restriction

TARGET Proposition 5.1 at every available spatial order. The root-valued lone leaf
is retained by the actual root partition. The full spectral extension
agrees pointwise with the original unlocalized causal source kernel.
-/

public section
noncomputable section
open MeasureTheory Set
open scoped ContDiff ENNReal

namespace WaveTurbulence.Incoh

/-- Actual raw source tree restriction decay, including moving localization of the lone leaf. -/
theorem exists_rawTreeKernel_fullRestriction_bound (d : ℕ) (hd : 3 ≤ d) :
    ∃ Cₗ : ℝ, 0 < Cₗ ∧ ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ l : ℕ, l ≤ 2 →
      ∀ η : ℝ, 0 < η → η ≤ 1 / 100 →
      ∀ χ : ℝ → ℝ, ContDiff ℝ ∞ χ → HasCompactSupport χ →
      ∀ γ : ℝ, γ ∈ Ioo (0 : ℝ) 1 → η < incoherenceExponent d γ →
      ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∀ D : ℝ, 0 < D →
      ∃ L₀ : ℝ, 1 ≤ L₀ ∧ ∀ L ≥ L₀, ∀ n m w J K M : ℕ,
        ∀ P : MomentumTreeData n m w, ∀ Q : Fin n → LayerLink d,
        (∀ i, |((Q i).leftLayer : ℝ) - (Q i).rightLayer| + 1 ≤ D) →
        1 ≤ incoherenceCount Q → ∀ R : RootCoordinates n, ∀ T : TreeClockFibers l Q,
        R.rootVertex 0 = T.selection.coordinates.rootVertex 0 →
        R.rootVertex 1 = T.selection.coordinates.rootVertex (Fin.last (l + 1)) →
        (∀ v ∈ R.rootBox Q, ∀ j, χ (v j) = 1) →
        (∀ v ∈ T.selection.coordinates.rootBox Q, ∀ j, χ (v j) = 1) →
        ∀ f : Fin m → Mom d → ℂ, ∀ B : ℝ, d + 1 + J ≤ K → 2 * d ≤ M → 0 ≤ B →
        (∀ a, Fourier.spatialNorm K M (f a) ≤ ENNReal.ofReal B) →
        ∀ ζ : Circle, ∀ A : Set (Mom d),
        Fourier.mixedRestrictionNorm η J 0 (R.rootBox Q ∩ {t | t 1 < t 0}) A
          (fun t k => P.sourceTreeKernel ζ R L γ δ Q T.timeDomain f t k) ≤
          (ENNReal.ofReal (rootLocalOverlapConstant d) *
            (ENNReal.ofReal (treeRootAmplitudeDerivativeFactor d J) *
              ENNReal.ofReal (maskedSourceSpatialConstant d (m + 1) J 0) * ENNReal.ofReal (Cₗ ^ n) *
                (ENNReal.ofReal (leafMomentLocalizationConstant d J M * treeAugmentedInputBound d K M B) ^ (m + 1) *
                  ENNReal.ofReal (halfCellFourierConstant d) ^ (2 * n)))) *
          ENNReal.ofReal ((C₀ * δ) ^ n *
            L ^ (-(incoherenceExponent d γ - 100 * (d : ℝ) * η) * incoherenceCount Q)) := by
  obtain ⟨Cₗ, hCₗ, hloc⟩ := exists_uniform_couple_link_cell_localization d (by omega)
  obtain ⟨C₀, hC₀, hb⟩ := exists_rootPartitionSourceTreeExtension_bound d hd
  obtain ⟨Cᵣ, _, hr⟩ := exists_rootDensity_L1_bound d hd
  refine ⟨Cₗ, hCₗ, C₀, hC₀, ?_⟩
  intro l hl η hη hη₁ χ hχ hcχ γ hγ hηγ δ hδ hδ₁ D hD
  obtain ⟨hc⟩ := Fourier.exists_cutoffControl hχ hcχ
  obtain ⟨L₁, hL₁, hb⟩ := hb l hl η hη hη₁ χ hχ hcχ γ hγ hηγ δ hδ hδ₁ D hD
  obtain ⟨L₂, _, hr⟩ := hr γ hγ η hη hηγ δ hδ D hD
  refine ⟨max L₁ L₂, hL₁.trans (le_max_left _ _), ?_⟩
  intro L hL n m w J K M P Q hspan hg R T hfirst hlast hχroot hχsel f B hK hM hB hf ζ A
  have hLa := (le_max_left L₁ L₂).trans hL
  have hLr := (le_max_right L₁ L₂).trans hL
  have hLone : 1 ≤ L := hL₁.trans hLa
  choose S hScard hcover using (fun c => hloc n (m + 1) w P.withRootInput P.withRootInput_all_leaves c)
  have hroot (z : (Fin n × Fin 2) → Fin d → ℤ) (ξ : LocalizedCellIndex n (m + 1) → Fin d → ℝ) :
      eLpNorm (R.linkDensity L γ δ (P.withRootInput.spectralLinks Q z ξ) T.timeDomain) 1 ≤
      ENNReal.ofReal ((Cᵣ * δ) ^ n * L ^ (-(incoherenceExponent d γ - 2 * η) * incoherenceCount Q)) := by
    simpa only [P.withRootInput.incoherenceCount_spectralLinks] using
      hr L hLr n (P.withRootInput.spectralLinks Q z ξ) hspan T.timeDomain T.measurableSet_timeDomain
        T.timeDomain_subset_linkBoxes R
  have hagree (t : ↥(R.rootBox Q ∩ {t : Fin 2 → ℝ | t 1 < t 0})) (k : A) :
      P.rootPartitionSourceTreeExtension ζ R χ L γ δ Q T.timeDomain f S t k =
        P.sourceTreeKernel ζ R L γ δ Q T.timeDomain f t k :=
    P.rootPartitionSourceTreeExtension_agrees_raw ζ R hχ hc L γ δ Q T.timeDomain
      T.measurableSet_timeDomain T.timeDomain_subset_linkBoxes hχroot f S hcover hScard
      hLone (by omega) hM hf ENNReal.ofReal_lt_top hroot t t.property.1 t.property.2.le k
  apply (Fourier.mixedRestrictionNorm_le_extension
    (P.rootPartitionSourceTreeExtension ζ R χ L γ δ Q T.timeDomain f S) hagree).trans
  exact hb L hLa n m w J K M P Q hspan hg R T hfirst hlast hχroot hχsel f B hK hM hB hf S Cₗ hScard ζ

end WaveTurbulence.Incoh
