/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.RegularAsymptotics.RA1Trees.TreeScalarProfile

/-! # A source scalar envelope implies the actual tree root-localized spatial bound -/

public section
noncomputable section
namespace WaveTurbulence.RegAsymp
open MeasureTheory Links Incoh IncohInst ClassJR
open scoped ENNReal

/-- Scalar NT/Wick envelopes are normalized by the actual single leaf moment, then
transported through the literal moving-root amplitudes. This is a transport helper,
not an assumed asymptotic or a substitute for the source scalar estimate. -/
theorem tree_root_scalar_profile_le {d K M J : ℕ} {G : Garden 1} {X : RegChain}
    (hX : X.DecodesTree G) {θ : ℝ} (hθ : 0 ≤ θ)
    (f : Fin (Fintype.card (TPlus G)) → Mom d → ℂ) {Binput Ccover P : ℝ}
    (hK : d+2+J ≤ K) (hM : 2*d ≤ M) (hBinput : 0 ≤ Binput) (hP : 0 ≤ P)
    (hf : ∀ a, Fourier.spatialNorm K M (f a) ≤ ENNReal.ofReal Binput)
    (S : (Fin (Fintype.card (TPlus G)+1) → Fin d → ℤ) →
      Finset ((Fin (X.treeLinks (G.sig 0)).length × Fin 2) → Fin d → ℤ))
    (hS : ∀ c, ((S c).card:ℝ) ≤ Ccover^(X.treeLinks (G.sig 0)).length)
    (R : (ℝ × ℝ) → (Fin (X.treeLinks (G.sig 0)).length → Mom d) →
      (Fin (X.treeLinks (G.sig 0)).length → Mom d) →
      ((Fin (X.treeLinks (G.sig 0)).length × Fin 2) → Fin d → ℤ) → ℂ)
    (hR : ∀ z, StronglyMeasurable (fun p : (ℝ × ℝ) ×
      ((Fin (X.treeLinks (G.sig 0)).length → Mom d) × (Fin (X.treeLinks (G.sig 0)).length → Mom d)) =>
        R p.1 p.2.1 p.2.2 z))
    (E : (ℝ × ℝ) → ℝ) (hmE : Measurable E) (hpE : ∀ lam, 0 ≤ E lam)
    (hfE : (∫⁻ lam, wL θ lam * ENNReal.ofReal (E lam)) < ⊤)
    (hbR : ∀ᵐ lam : ℝ × ℝ, ∀ z β γ, ‖R lam β γ z‖ ≤
      P*(1+((∑ j, ‖β j‖)+(∑ j, ‖γ j‖)))*E lam) :
    Fourier.mixedFourierNorm θ J 0
      (treeRootLeafMixture f S (fun t u => unitSquareCutoff t *
        pairedInverseProfile (fun lam => treeNormalizedScalar hX R S lam u) t)) ≤
      (ENNReal.ofReal (rootLocalOverlapConstant d) *
        (ENNReal.ofReal (treeRootLeafDerivativeConstant d J) *
          (ENNReal.ofReal (Ccover^(X.treeLinks (G.sig 0)).length) *
            ENNReal.ofReal (leafMomentLocalizationConstant d (J+1) M *
              treeAugmentedInputBound d K M Binput)^(Fintype.card (TPlus G)+1)))) *
        (ENNReal.ofReal (2^θ)*Fourier.timeFourierNorm θ unitSquareCutoff*
          (ENNReal.ofReal (P*treeSpectralFrequencyLoss X (G.sig 0)) *
            ∫⁻ lam, wL θ lam*ENNReal.ofReal (E lam))) := by
  let B := fun lam => ENNReal.ofReal (P*treeSpectralFrequencyLoss X (G.sig 0)) * ENNReal.ofReal (E lam)
  have hmB : Measurable B := measurable_const.mul (ENNReal.measurable_ofReal.comp hmE)
  have hbB (u : SourceCellIndex S × (Fin (Fintype.card (TPlus G)+1) → Fin d → ℝ)) :
      ∀ᵐ lam : ℝ × ℝ, ‖treeNormalizedScalar hX R S lam u‖ₑ ≤ B lam := by
    filter_upwards [hbR] with lam hlam
    rw [← ofReal_norm]
    have h := ENNReal.ofReal_le_ofReal
      (treeNormalizedScalar_norm_le hX R S hP (hpE lam) lam hlam u)
    simpa only [B, ENNReal.ofReal_mul (mul_nonneg hP
      (zero_le_one.trans (one_le_treeSpectralFrequencyLoss X (G.sig 0))))] using h
  have he : (∫⁻ lam, wL θ lam * B lam) =
      ENNReal.ofReal (P*treeSpectralFrequencyLoss X (G.sig 0)) *
        ∫⁻ lam, wL θ lam * ENNReal.ofReal (E lam) := by
    have hh (lam : ℝ × ℝ) : wL θ lam * B lam =
        ENNReal.ofReal (P*treeSpectralFrequencyLoss X (G.sig 0)) *
          (wL θ lam * ENNReal.ofReal (E lam)) := by dsimp only [B]; ring
    simp_rw [hh]
    exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
  have hfB : (∫⁻ lam, wL θ lam * B lam) < ⊤ := by
    rw [he]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hfE
  have h := mixedFourierNorm_treeRootPairedProfile_le hθ f hK hM hBinput hf S hS
    (treeNormalizedScalar hX R S) (stronglyMeasurable_treeNormalizedScalar hX R hR S) hmB hbB hfB
  rw [he] at h
  exact h

end WaveTurbulence.RegAsymp
