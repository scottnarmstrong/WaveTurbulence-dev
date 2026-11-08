/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.IncTop.Reg.AllCellAmplitudeL1
public import WaveTurbulence.Foundations.Flower.IncTop.Reg.SourceCoupleJointIntegrability

/-! Ported by source from C2-B-TOP `Cut2BReg.AllCellCoupleFubini` (sha256 in COPIED-SHA256SUMS); mechanical edits only.

R66 spatially modulated scratch copy. Original SHA256 recorded in REG-COPIES.json.

# Fubini on all actual couple localization cells

The countable localization coefficient is integrable. Uniform physical
root-marginal control therefore gives joint time/localization integrability.
-/

public section
noncomputable section
open MeasureTheory
open scoped ENNReal

namespace WaveTurbulence.Flower.IncTop
open WaveTurbulence.Incoh
open WaveTurbulence.Incoh.MomentumTreeData in
/-- Conditional Fubini helper over all actual cells, using their independently bounded mass. -/
theorem MomentumTreeData.integrable_allCellCoupleMixture_of_uniformRootL1Spatial {d n m w K M : ℕ}
    (P : MomentumTreeData n m w) (ζ : Circle) (R : RootCoordinates n)
    (L γ δ : ℝ) (Q : Fin n → LayerLink d) (I : Set (Fin n → Fin 2 → ℝ))
    (hI : MeasurableSet I) (hbox : I ⊆ Set.univ.pi (fun i => linkBox (Q i)))
    (f : Fin m → Mom d → ℂ)
    (S : (Fin m → Fin d → ℤ) → Finset ((Fin n × Fin 2) → Fin d → ℤ))
    {C : ℝ} (hS : ∀ c, ((S c).card : ℝ) ≤ C ^ n) {B : ℝ}
    (hL : 0 < L) (hK : d + 1 ≤ K) (hM : 2 * d ≤ M) (hB : 0 ≤ B)
    (h : ∀ a, Fourier.spatialNorm K M (f a) ≤ ENNReal.ofReal B)
    {N : ℝ≥0∞} (hN : N < ⊤)
    (hb : ∀ z : (Fin n × Fin 2) → Fin d → ℤ, ∀ ξ : LocalizedCellIndex n m → Fin d → ℝ,
      eLpNorm (R.linkDensity L γ δ ((MomentumTreeData.spectralLinksSpatial (P := P)) Q z ξ) I) 1 ≤ N) (k : Mom d) :
    Integrable (fun v : (Fin 2 → ℝ) ×
      (SourceCellIndex S × (LocalizedCellIndex n m → Fin d → ℝ)) =>
      (MomentumTreeData.allCellSpectralAmplitudeSpatial (P := P)) ζ f S k v.2 * (MomentumTreeData.allCellCoupleKernelSpatial (P := P)) R L γ δ Q I S v.1 v.2)
      (volume.prod (sourceCellMeasure S)) := by
  obtain ⟨hc⟩ := Fourier.exists_cutoffControl contDiff_rootCutoff hasCompactSupport_rootCutoff
  let A := Fourier.cutoffKernelL1Factor hc.radius hc.bound * Fourier.localTimeL1Factor 1 hc.radius hc.bound
  have hA : A < ⊤ := ENNReal.mul_lt_top (Fourier.cutoffKernelL1Factor_ne_top _ _).lt_top
    (Fourier.localTimeL1Factor_ne_top (le_refl (1 : ℝ)) _ _).lt_top
  apply integrable_amplitude_mul_family_of_uniformL1 (sourceCellMeasure S)
    ((MomentumTreeData.allCellSpectralAmplitudeSpatial (P := P)) ζ f S k)
    ((MomentumTreeData.stronglyMeasurable_allCellSpectralAmplitudeSpatial (P := P)) ζ f S hK hB h k)
    ((MomentumTreeData.integrable_allCellSpectralAmplitudeSpatial (P := P)) ζ f S hS hK hM hB h k)
    ((MomentumTreeData.allCellCoupleKernelSpatial (P := P)) R L γ δ Q I S)
    ((MomentumTreeData.stronglyMeasurable_allCellCoupleKernelSpatial (P := P)) R hL γ δ Q I hI S)
    (fun u => R.integrable_coupleExtension contDiff_rootCutoff hc hL γ δ
      ((MomentumTreeData.spectralLinksSpatial (P := P)) Q u.1.2.val u.2) hI hbox) (ENNReal.mul_lt_top hA hN)
  intro u
  exact (R.eLpNorm_coupleExtension_one_le contDiff_rootCutoff hc hL γ δ
    ((MomentumTreeData.spectralLinksSpatial (P := P)) Q u.1.2.val u.2) hI hbox).trans (mul_le_mul' le_rfl (hb _ _))

end WaveTurbulence.Flower.IncTop