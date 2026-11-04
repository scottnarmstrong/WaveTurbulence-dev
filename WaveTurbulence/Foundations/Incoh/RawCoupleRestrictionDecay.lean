/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Incoh.RawCoupleAgreement
public import WaveTurbulence.Foundations.Incoh.CoupleLinkCellLocalization
public import WaveTurbulence.Foundations.Fourier.Norm00VRestriction

/-!
# Incoherence decay for the literal raw source couple restriction

TARGET Proposition 5.1 at spatial order zero. Finite localization,
actual Fourier inversion, exact source reconstruction and all Fubini
conditions are proved from the structural carrier and input spatial norms.
-/

public section
noncomputable section
open MeasureTheory Set
open scoped ENNReal

namespace WaveTurbulence.Incoh

/-- Actual raw source couple restriction decay with its explicit dimensional localization cost. -/
theorem exists_rawCoupleKernel_restriction_bound (d : ℕ) (hd : 3 ≤ d) :
    ∃ Cₗ : ℝ, 0 < Cₗ ∧ ∀ η : ℝ, 0 < η → η ≤ 1 / 3 →
      ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ γ : ℝ, γ ∈ Ioo (0 : ℝ) 1 → η < incoherenceExponent d γ →
        ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∀ D : ℝ, 0 < D →
        ∃ L₀ : ℝ, 1 ≤ L₀ ∧ ∀ L ≥ L₀, ∀ n m w K M : ℕ,
          ∀ P : MomentumTreeData n m w,
          (∀ i p, p ∈ (P.tree i).leaves → P.leafInput i p ≠ none) →
          ∀ Q : Fin n → LayerLink d,
          (∀ i, |((Q i).leftLayer : ℝ) - (Q i).rightLayer| + 1 ≤ D) →
          1 ≤ incoherenceCount Q → ∀ R : RootCoordinates n,
          ∀ I : Set (Fin n → Fin 2 → ℝ), MeasurableSet I → I ⊆ univ.pi (fun i => linkBox (Q i)) →
          ∀ f : Fin m → Mom d → ℂ, ∀ B : ℝ, d + 1 ≤ K → 2 * d ≤ M → 0 ≤ B →
          (∀ a, Fourier.spatialNorm K M (f a) ≤ ENNReal.ofReal B) →
          ∀ ζ : Circle, ∀ A : Set (Mom d),
          Fourier.mixedRestrictionNorm00 η (R.rootBox Q) A
            (fun t k => P.sourceCoupleKernel ζ R L γ δ Q I f t k) ≤
            (ENNReal.ofReal (Cₗ ^ n) * (ENNReal.ofReal (leafLocalizationConstant d M * B) ^ m *
              ENNReal.ofReal (halfCellFourierConstant d) ^ (2 * n))) *
            ENNReal.ofReal ((C₀ * δ) ^ n *
              L ^ (-(incoherenceExponent d γ - 100 * (d : ℝ) * η) * incoherenceCount Q)) := by
  obtain ⟨Cₗ, hCₗ, hloc⟩ := exists_uniform_couple_link_cell_localization d (by omega)
  refine ⟨Cₗ, hCₗ, ?_⟩
  intro η hη hη₁
  obtain ⟨C₀, hC₀, hb⟩ := exists_allCellSourceCoupleExtension_bound d hd η hη hη₁
  obtain ⟨Cᵣ, _, hr⟩ := exists_rootDensity_L1_bound d hd
  refine ⟨C₀, hC₀, ?_⟩
  intro γ hγ hηγ δ hδ hδ₁ D hD
  obtain ⟨L₁, hL₁, hb⟩ := hb γ hγ hηγ δ hδ hδ₁ D hD
  obtain ⟨L₂, _, hr⟩ := hr γ hγ η hη hηγ δ hδ D hD
  refine ⟨max L₁ L₂, hL₁.trans (le_max_left _ _), ?_⟩
  intro L hL n m w K M P hinputs Q hspan hg R I hI hbox f B hK hM hB hf ζ A
  have hLa := (le_max_left L₁ L₂).trans hL
  have hLr := (le_max_right L₁ L₂).trans hL
  have hLone : 1 ≤ L := hL₁.trans hLa
  choose S hScard hcover using (fun c => hloc n m w P hinputs c)
  have hroot (z : (Fin n × Fin 2) → Fin d → ℤ) (ξ : LocalizedCellIndex n m → Fin d → ℝ) :
      eLpNorm (R.linkDensity L γ δ (P.spectralLinks Q z ξ) I) 1 ≤
      ENNReal.ofReal ((Cᵣ * δ) ^ n * L ^ (-(incoherenceExponent d γ - 2 * η) * incoherenceCount Q)) := by
    simpa only [P.incoherenceCount_spectralLinks] using
      hr L hLr n (P.spectralLinks Q z ξ) hspan I hI hbox R
  apply (Fourier.mixedRestrictionNorm00_le_extension
    (P.allCellSourceCoupleExtension ζ R L γ δ Q I f S) (fun t k =>
      P.allCellSourceCoupleExtension_agrees_raw ζ R L γ δ Q I hI hbox f S hcover hScard
        hLone hK hM hB hf ENNReal.ofReal_lt_top hroot t t.property k)).trans
  exact hb L hLa n m w K M P Q hspan hg R I hI hbox f B hK hM hB hf S Cₗ hScard ζ

end WaveTurbulence.Incoh
