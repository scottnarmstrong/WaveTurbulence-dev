/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Incoh.MovingCellAmplitude
public import WaveTurbulence.Foundations.Incoh.SpectralTreeMeasurability
public import WaveTurbulence.Foundations.Incoh.CutoffTriangleL1
public import WaveTurbulence.Foundations.Incoh.GeneralTriangleNegativeNorm
public import WaveTurbulence.Foundations.Incoh.UniformL1MixtureIntegrability

/-!
# Actual causal kernel family for moving tree localization

The fixed measure counts every integer cell. The kernel is the actual
spectral causal extension; the source amplitude retains its moving mask.
-/

public section
noncomputable section
open MeasureTheory
open scoped ContDiff ENNReal

namespace WaveTurbulence.Incoh

/-- Actual causal spectral link kernel on the fixed unrestricted cell measure. -/
@[expose] def MomentumTreeData.unrestrictedTreeKernel {d n m w : ℕ}
    (P : MomentumTreeData n m w) (R : RootCoordinates n) (χ : ℝ → ℝ) (L γ δ : ℝ)
    (Q : Fin n → LayerLink d) (I : Set (Fin n → Fin 2 → ℝ))
    (t : Fin 2 → ℝ) (u : UnrestrictedCellIndex d n m × (LocalizedCellIndex n m → Fin d → ℝ)) : ℂ :=
  Fourier.cutoffTriangleIntegral χ (R.linkDensity L γ δ (P.spectralLinks Q u.1.2 u.2) I) t

/-- Joint measurability of the actual tree spectral family over every integer cell pair. -/
theorem MomentumTreeData.stronglyMeasurable_unrestrictedTreeKernel {d n m w : ℕ}
    (P : MomentumTreeData n m w) (R : RootCoordinates n) {χ : ℝ → ℝ} (hχ : Measurable χ)
    {L : ℝ} (hL : 0 < L) (γ δ : ℝ) (Q : Fin n → LayerLink d)
    (I : Set (Fin n → Fin 2 → ℝ)) (hI : MeasurableSet I) :
    StronglyMeasurable (fun v : (Fin 2 → ℝ) ×
      (UnrestrictedCellIndex d n m × (LocalizedCellIndex n m → Fin d → ℝ)) =>
      P.unrestrictedTreeKernel R χ L γ δ Q I v.1 v.2) := by
  have hm : Measurable (fun v : UnrestrictedCellIndex d n m ×
      ((Fin 2 → ℝ) × (LocalizedCellIndex n m → Fin d → ℝ)) =>
      Fourier.cutoffTriangleIntegral χ (R.linkDensity L γ δ (P.spectralLinks Q v.1.2 v.2.2) I) v.2.1) := by
    apply measurable_from_prod_countable_right
    intro u
    exact (P.stronglyMeasurable_spectral_treeExtension R hL γ δ Q u.2 hI hχ).measurable
  have hg : Measurable (fun v : (Fin 2 → ℝ) ×
      (UnrestrictedCellIndex d n m × (LocalizedCellIndex n m → Fin d → ℝ)) =>
      (v.2.1, (v.1, v.2.2))) := by fun_prop
  exact (hm.comp hg).stronglyMeasurable

/-- Conditional spectral Fubini for the actual moving-cell tree family. -/
theorem MomentumTreeData.integrable_movingTreeMixture_of_uniformRootL1 {d n m w K M : ℕ}
    (P : MomentumTreeData n m w) (ζ : Circle) (R : RootCoordinates n)
    {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ) (hc : Fourier.CutoffControl χ)
    (L γ δ : ℝ) (Q : Fin n → LayerLink d) (I : Set (Fin n → Fin 2 → ℝ))
    (hI : MeasurableSet I) (hbox : I ⊆ Set.univ.pi (fun i => linkBox (Q i)))
    (f : Fin m → Mom d → ℂ)
    (S : Mom d → (Fin m → Fin d → ℤ) → Finset ((Fin n × Fin 2) → Fin d → ℤ))
    {C : ℝ} (hS : ∀ k c, ((S k c).card : ℝ) ≤ C ^ n) {B : ℝ}
    (hL : 0 < L) (hK : d + 1 ≤ K) (hM : 2 * d ≤ M) (hB : 0 ≤ B)
    (h : ∀ a, Fourier.spatialNorm K M (f a) ≤ ENNReal.ofReal B)
    {N : ℝ≥0∞} (hN : N < ⊤)
    (hb : ∀ z : (Fin n × Fin 2) → Fin d → ℤ, ∀ ξ : LocalizedCellIndex n m → Fin d → ℝ,
      eLpNorm (R.linkDensity L γ δ (P.spectralLinks Q z ξ) I) 1 ≤ N) (k : Mom d) :
    Integrable (fun v : (Fin 2 → ℝ) ×
      (UnrestrictedCellIndex d n m × (LocalizedCellIndex n m → Fin d → ℝ)) =>
      P.movingCellAmplitude ζ f S k v.2 * P.unrestrictedTreeKernel R χ L γ δ Q I v.1 v.2)
      (volume.prod (unrestrictedCellMeasure d n m)) := by
  let A := Fourier.cutoffKernelL1Factor hc.radius hc.bound * Fourier.localTimeL1Factor 1 hc.radius hc.bound
  have hA : A < ⊤ := ENNReal.mul_lt_top (Fourier.cutoffKernelL1Factor_ne_top _ _).lt_top
    (Fourier.localTimeL1Factor_ne_top (le_refl (1 : ℝ)) _ _).lt_top
  apply integrable_amplitude_mul_family_of_uniformL1 (unrestrictedCellMeasure d n m)
    (P.movingCellAmplitude ζ f S k)
    (P.stronglyMeasurable_movingCellAmplitude ζ f S hK hB h k)
    (P.integrable_movingCellAmplitude ζ f S hS hK hM hB h k)
    (fun t u => P.unrestrictedTreeKernel R χ L γ δ Q I t u)
    (P.stronglyMeasurable_unrestrictedTreeKernel R hχ.continuous.measurable hL γ δ Q I hI)
    (fun u => integrable_cutoffTriangleIntegral hχ hc
      (R.integrable_linkDensity hL γ δ (P.spectralLinks Q u.1.2 u.2) hI hbox))
    (ENNReal.mul_lt_top hA hN)
  intro u
  exact (eLpNorm_cutoffTriangleIntegral_one_le hχ hc
    (R.integrable_linkDensity hL γ δ (P.spectralLinks Q u.1.2 u.2) hI hbox)).trans
      (mul_le_mul' le_rfl (hb _ _))

end WaveTurbulence.Incoh
