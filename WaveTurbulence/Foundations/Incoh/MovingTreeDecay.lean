/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Incoh.MovingTreeFamily
public import WaveTurbulence.Foundations.Incoh.ParameterTreeDecay
public import WaveTurbulence.Foundations.Incoh.SpectralTreeClocks
public import WaveTurbulence.Foundations.Incoh.UniformParameterMixture

/-!
# Actual source tree decay after moving-cell spectral recombination

The causal extension is one actual common kernel. The finite cell support
may move with root momentum; a uniform actual amplitude mass suffices.
-/

public section
noncomputable section
open MeasureTheory Set
open scoped ContDiff ENNReal

namespace WaveTurbulence.Incoh

/-- Actual causal source extension with the moving selection kept in the input amplitude. -/
@[expose] def MomentumTreeData.movingCellSourceTreeExtension {d n m w : ℕ}
    (P : MomentumTreeData n m w) (ζ : Circle) (R : RootCoordinates n) (χ : ℝ → ℝ)
    (L γ δ : ℝ) (Q : Fin n → LayerLink d) (I : Set (Fin n → Fin 2 → ℝ))
    (f : Fin m → Mom d → ℂ)
    (S : Mom d → (Fin m → Fin d → ℤ) → Finset ((Fin n × Fin 2) → Fin d → ℤ))
    (t : Fin 2 → ℝ) (k : Mom d) : ℂ :=
  ∫ u, P.movingCellAmplitude ζ f S k u * P.unrestrictedTreeKernel R χ L γ δ Q I t u
    ∂unrestrictedCellMeasure d n m

/-- TARGET (incohproof24), for the actual source spectral extension and moving finite covers. -/
theorem exists_movingCellSourceTreeExtension_bound (d : ℕ) (hd : 3 ≤ d) :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ l : ℕ, l ≤ 2 → ∀ η : ℝ, 0 < η → η ≤ 1 / 100 →
      ∀ χ : ℝ → ℝ, ContDiff ℝ ∞ χ → HasCompactSupport χ →
      ∀ γ : ℝ, γ ∈ Ioo (0 : ℝ) 1 → η < incoherenceExponent d γ →
      ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∀ D : ℝ, 0 < D →
      ∃ L₀ : ℝ, 1 ≤ L₀ ∧ ∀ L ≥ L₀, ∀ n m w K M : ℕ,
        ∀ P : MomentumTreeData n m w, ∀ Q : Fin n → LayerLink d,
        (∀ i, |((Q i).leftLayer : ℝ) - (Q i).rightLayer| + 1 ≤ D) →
        1 ≤ incoherenceCount Q → ∀ R : RootCoordinates n, ∀ T : TreeClockFibers l Q,
        R.rootVertex 0 = T.selection.coordinates.rootVertex 0 →
        R.rootVertex 1 = T.selection.coordinates.rootVertex (Fin.last (l + 1)) →
        (∀ v ∈ R.rootBox Q, ∀ j, χ (v j) = 1) →
        (∀ v ∈ T.selection.coordinates.rootBox Q, ∀ j, χ (v j) = 1) →
        ∀ f : Fin m → Mom d → ℂ, ∀ B : ℝ, d + 1 ≤ K → 2 * d ≤ M → 0 ≤ B →
        (∀ a, Fourier.spatialNorm K M (f a) ≤ ENNReal.ofReal B) →
        ∀ S : Mom d → (Fin m → Fin d → ℤ) → Finset ((Fin n × Fin 2) → Fin d → ℤ),
        ∀ C : ℝ, (∀ k c, ((S k c).card : ℝ) ≤ C ^ n) → ∀ ζ : Circle,
        Fourier.mixedFourierNorm00 η (P.movingCellSourceTreeExtension ζ R χ L γ δ Q T.timeDomain f S) ≤
          (ENNReal.ofReal (C ^ n) * (ENNReal.ofReal (leafLocalizationConstant d M * B) ^ m *
            ENNReal.ofReal (halfCellFourierConstant d) ^ (2 * n))) *
          ENNReal.ofReal ((C₀ * δ) ^ n *
            L ^ (-(incoherenceExponent d γ - 100 * (d : ℝ) * η) * incoherenceCount Q)) := by
  obtain ⟨C₀, hC₀, hb⟩ := exists_parameterTreeCausalExtension_decay d hd
  obtain ⟨Cᵣ, _, hr⟩ := exists_rootDensity_L1_bound d hd
  refine ⟨C₀, hC₀, ?_⟩
  intro l hl η hη hη₁ χ hχ hcχ
  obtain ⟨hc⟩ := Fourier.exists_cutoffControl hχ hcχ
  intro γ hγ hηγ δ hδ hδ₁ D hD
  obtain ⟨L₁, hL₁, hb⟩ := hb l hl η hη hη₁ χ hχ hcχ γ hγ hηγ δ hδ hδ₁ D hD
  obtain ⟨L₂, _, hr⟩ := hr γ hγ η hη hηγ δ hδ D hD
  refine ⟨max L₁ L₂, hL₁.trans (le_max_left _ _), ?_⟩
  intro L hL n m w K M P Q hspan hg R T hfirst hlast hχroot hχsel f B hK hM hB hf S C hS ζ
  have hLa := (le_max_left L₁ L₂).trans hL
  have hLr := (le_max_right L₁ L₂).trans hL
  have hLp : 0 < L := zero_lt_one.trans_le (hL₁.trans hLa)
  let U := UnrestrictedCellIndex d n m × (LocalizedCellIndex n m → Fin d → ℝ)
  let Q' := fun p : Mom d × U => P.spectralLinks Q p.2.1.2 p.2.2
  let T' := fun p : Mom d × U => P.spectralTreeClockFibers Q T p.2.1.2 p.2.2
  have hJ := T.selection.card_links_le_two (by omega : l + 2 ≤ 4)
  have hcore := hb L hLa n (incoherenceCount Q) hg (Mom d × U) Q'
    (fun _ => hspan) (fun _ => rfl) T' R T.selection.coordinates.rootLinks hJ
    (fun _ => hfirst) (fun _ => hlast) (fun _ => rfl) (fun _ => hχroot) (fun _ => hχsel)
  have hj (k : Mom d) := P.integrable_movingTreeMixture_of_uniformRootL1 ζ R hχ hc L γ δ Q T.timeDomain
    T.measurableSet_timeDomain T.timeDomain_subset_linkBoxes f S hS hLp hK hM hB hf
    (N := ENNReal.ofReal ((Cᵣ * δ) ^ n *
      L ^ (-(incoherenceExponent d γ - 2 * η) * incoherenceCount Q))) ENNReal.ofReal_lt_top
    (fun z ξ => by
      simpa only [P.incoherenceCount_spectralLinks] using
        hr L hLr n (P.spectralLinks Q z ξ) hspan T.timeDomain T.measurableSet_timeDomain
          T.timeDomain_subset_linkBoxes R) k
  have hbnd := mixedFourierNorm00_integral_uniform_mass_le (unrestrictedCellMeasure d n m) η
    (P.movingCellAmplitude ζ f S) (fun t (_ : Mom d) u => P.unrestrictedTreeKernel R χ L γ δ Q T.timeDomain t u)
    (P.stronglyMeasurable_movingCellAmplitude ζ f S hK hB hf)
    (fun _ u => integrable_cutoffTriangleIntegral hχ hc (R.integrable_linkDensity hLp γ δ
      (P.spectralLinks Q u.1.2 u.2) T.measurableSet_timeDomain T.timeDomain_subset_linkBoxes)) hj
    (P.lintegral_enorm_movingCellAmplitude_le ζ f S hS hK hM hB hf)
  exact hbnd.trans (mul_le_mul' le_rfl hcore)

end WaveTurbulence.Incoh
