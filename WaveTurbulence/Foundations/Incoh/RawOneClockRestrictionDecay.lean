/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Incoh.RawOneClockAgreement
public import WaveTurbulence.Foundations.Incoh.ParameterTimeTranslation
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
theorem exists_rawOneClockKernel_restriction_bound (d : ℕ) (hd : 3 ≤ d) :
    ∃ Cₗ : ℝ, 0 < Cₗ ∧ ∀ η : ℝ, 0 < η → η ≤ 1 / 3 →
      ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ γ : ℝ, γ ∈ Ioo (0 : ℝ) 1 → η < incoherenceExponent d γ →
        ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∀ D : ℝ, 0 < D →
        ∃ L₀ : ℝ, 1 ≤ L₀ ∧ ∀ L ≥ L₀, ∀ n m w K M : ℕ,
          ∀ P : MomentumTreeData n m w,
          (∀ i p, p ∈ (P.tree i).leaves → P.leafInput i p ≠ none) →
          ∀ Q : Fin n → LayerLink d,
          (∀ i, |((Q i).leftLayer : ℝ) - (Q i).rightLayer| + 1 ≤ D) →
          1 ≤ incoherenceCount Q → ∀ R : RootCoordinates n, ∀ a : Fin 2, ∀ b : ℝ,
          ∀ I : Set (Fin n → Fin 2 → ℝ), MeasurableSet I → I ⊆ univ.pi (fun i => linkBox (Q i)) →
          ∀ f : Fin m → Mom d → ℂ, ∀ B : ℝ, d + 1 ≤ K → 2 * d ≤ M → 0 ≤ B →
          (∀ a, Fourier.spatialNorm K M (f a) ≤ ENNReal.ofReal B) →
          ∀ ζ : Circle, ∀ A : Set (Mom d),
          Fourier.mixedRestrictionNorm00 η (R.oneClockBox a Q b) A
            (fun t k => P.sourceOneClockKernel ζ R a L γ δ Q I f t k) ≤
            (ENNReal.ofReal (Cₗ ^ n) * (ENNReal.ofReal (leafLocalizationConstant d M * B) ^ m *
              ENNReal.ofReal (halfCellFourierConstant d) ^ (2 * n))) *
            ENNReal.ofReal ((C₀ * δ) ^ n *
              L ^ (-(incoherenceExponent d γ - 100 * (d : ℝ) * η) * incoherenceCount Q)) := by
  obtain ⟨Cₗ, hCₗ, hloc⟩ := exists_uniform_couple_link_cell_localization d (by omega)
  refine ⟨Cₗ, hCₗ, ?_⟩
  intro η hη hη₁
  obtain ⟨C₀, hC₀, hb⟩ := exists_allCellSourceCutoffCoupleExtension_bound d hd η hη hη₁
    contDiff_wideRootCutoff hasCompactSupport_wideRootCutoff
  obtain ⟨Cᵣ, _, hr⟩ := exists_rootDensity_L1_bound d hd
  refine ⟨C₀, hC₀, ?_⟩
  intro γ hγ hηγ δ hδ hδ₁ D hD
  obtain ⟨L₁, hL₁, hb⟩ := hb γ hγ hηγ δ hδ hδ₁ D hD
  obtain ⟨L₂, _, hr⟩ := hr γ hγ η hη hηγ δ hδ D hD
  refine ⟨max L₁ L₂, hL₁.trans (le_max_left _ _), ?_⟩
  intro L hL n m w K M P hinputs Q hspan hg R a b I hI hbox f B hK hM hB hf ζ A
  have hLa := (le_max_left L₁ L₂).trans hL
  have hLr := (le_max_right L₁ L₂).trans hL
  have hLone : 1 ≤ L := hL₁.trans hLa
  choose S hScard hcover using (fun c => hloc n m w P hinputs c)
  have hroot (z : (Fin n × Fin 2) → Fin d → ℤ) (ξ : LocalizedCellIndex n m → Fin d → ℝ) :
      eLpNorm (R.linkDensity L γ δ (P.spectralLinks Q z ξ) I) 1 ≤
      ENNReal.ofReal ((Cᵣ * δ) ^ n * L ^ (-(incoherenceExponent d γ - 2 * η) * incoherenceCount Q)) := by
    simpa only [P.incoherenceCount_spectralLinks] using
      hr L hLr n (P.spectralLinks Q z ξ) hspan I hI hbox R
  let G := P.allCellSourceCutoffCoupleExtension wideRootCutoff ζ R L γ δ Q I f S
  have hG := hb L hLa n m w K M P Q hspan hg R I hI hbox f B hK hM hB hf S Cₗ hScard ζ
  have hiG (k : Mom d) : Integrable (fun t => G t k) :=
    Fourier.integrable_of_mixedFourierNorm00_lt_top (F := G)
      (hG.trans_lt (ENNReal.mul_lt_top (ENNReal.mul_lt_top ENNReal.ofReal_lt_top
        (ENNReal.mul_lt_top (ENNReal.pow_lt_top ENNReal.ofReal_lt_top)
          (ENNReal.pow_lt_top ENNReal.ofReal_lt_top))) ENNReal.ofReal_lt_top)) k
  have hagree (t : R.oneClockBox a Q b) (k : A) :
      G (t + R.oneClockShift a Q b) k = P.sourceOneClockKernel ζ R a L γ δ Q I f t k := by
    exact P.allCellSourceCutoffCoupleExtension_agrees_oneClock ζ R a b L γ δ Q I hI hbox
      f S hcover hScard hLone hK hM hB hf
      (N := ENNReal.ofReal ((Cᵣ * δ) ^ n *
        L ^ (-(incoherenceExponent d γ - 2 * η) * incoherenceCount Q)))
      ENNReal.ofReal_lt_top hroot t t.property k
  apply (Fourier.mixedRestrictionNorm00_le_extension
    (fun t k => G (t + R.oneClockShift a Q b) k) hagree).trans
  rw [mixedFourierNorm00_translate_of_integrable η G (R.oneClockShift a Q b) hiG]
  exact hG

end WaveTurbulence.Incoh
