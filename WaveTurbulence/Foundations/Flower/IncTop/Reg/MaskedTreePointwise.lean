/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.IncTop.Reg.AllCellTreeFamily
public import WaveTurbulence.Foundations.Flower.IncTop.Reg.MaskedCellFamily
public import WaveTurbulence.Foundations.Flower.IncTop.Reg.MovingTreeFamily
public import WaveTurbulence.Foundations.Flower.IncTop.Reg.SpectralTreeClocks
public import WaveTurbulence.Foundations.Incoh.CouplePointwiseL1
public import WaveTurbulence.Foundations.Incoh.PointwiseMixtureIntegrability
public import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure

/-! Ported by source from C2-B-TOP `Cut2BReg.MaskedTreePointwise` (sha256 in COPIED-SHA256SUMS); mechanical edits only.

R66 spatially modulated scratch copy. Original SHA256 recorded in REG-COPIES.json.
 # Pointwise countable recovery for the actual masked source extension -/

public section
noncomputable section
open MeasureTheory
open scoped ENNReal ContDiff

namespace WaveTurbulence.Flower.IncTop
open WaveTurbulence.Incoh
open WaveTurbulence.Incoh.MomentumTreeData in
/-- The actual masked tree extension on the fixed source-cell measure. -/
@[expose] def MomentumTreeData.allCellMaskedSourceTreeExtensionSpatial {d n m w : ℕ}
    (P : MomentumTreeData n m w) (χ : ℝ → ℝ) (ζ : Circle) (R : RootCoordinates n)
    (L γ δ : ℝ) (Q : Fin n → LayerLink d) (I : Set (Fin n → Fin 2 → ℝ))
    (f : Fin m → Mom d → ℂ)
    (S : (Fin m → Fin d → ℤ) → Finset ((Fin n × Fin 2) → Fin d → ℤ))
    (t : Fin 2 → ℝ) (k : Mom d) : ℂ :=
  ∫ u, (MomentumTreeData.allCellMaskedSpectralAmplitudeSpatial (P := P)) ζ f S k u *
    (MomentumTreeData.allCellTreeKernelSpatial (P := P)) R χ L γ δ Q I S t u ∂sourceCellMeasure S

open WaveTurbulence.Incoh.MomentumTreeData in
/-- Conditional pointwise Fubini typing from the independently proved root-marginal bound. -/
theorem MomentumTreeData.integrable_allCellMaskedTreeSlice_of_uniformRootL1Spatial {d n m w K M : ℕ}
    (P : MomentumTreeData n m w) {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (hc : Fourier.CutoffControl χ) (ζ : Circle) (R : RootCoordinates n)
    (L γ δ : ℝ) (Q : Fin n → LayerLink d) (I : Set (Fin n → Fin 2 → ℝ))
    (hI : MeasurableSet I) (hbox : I ⊆ Set.univ.pi (fun i => linkBox (Q i)))
    (f : Fin m → Mom d → ℂ)
    (S : (Fin m → Fin d → ℤ) → Finset ((Fin n × Fin 2) → Fin d → ℤ))
    {C : ℝ} (hS : ∀ c, ((S c).card : ℝ) ≤ C ^ n) {B : ℝ}
    (hL : 0 < L) (hK : d + 1 ≤ K) (hM : 2 * d ≤ M) (hB : 0 ≤ B)
    (h : ∀ a, Fourier.spatialNorm K M (f a) ≤ ENNReal.ofReal B)
    {N : ℝ≥0∞} (hN : N < ⊤)
    (hb : ∀ z : (Fin n × Fin 2) → Fin d → ℤ, ∀ ξ : LocalizedCellIndex n m → Fin d → ℝ,
      eLpNorm (R.linkDensity L γ δ ((MomentumTreeData.spectralLinksSpatial (P := P)) Q z ξ) I) 1 ≤ N)
    (t : Fin 2 → ℝ) (k : Mom d) :
    Integrable (fun u => (MomentumTreeData.allCellMaskedSpectralAmplitudeSpatial (P := P)) ζ f S k u *
      (MomentumTreeData.allCellTreeKernelSpatial (P := P)) R χ L γ δ Q I S t u) (sourceCellMeasure S) := by
  have hKs : StronglyMeasurable ((MomentumTreeData.allCellTreeKernelSpatial (P := P)) R χ L γ δ Q I S t) :=
    ((MomentumTreeData.stronglyMeasurable_allCellTreeKernelSpatial (P := P)) R hχ.continuous.measurable hL γ δ Q I hI S).comp_measurable
      (g := fun u => (t, u)) (measurable_const.prodMk measurable_id)
  apply integrable_mul_of_uniform_enorm_bound (sourceCellMeasure S)
    ((MomentumTreeData.allCellMaskedSpectralAmplitudeSpatial (P := P)) ζ f S k) ((MomentumTreeData.allCellTreeKernelSpatial (P := P)) R χ L γ δ Q I S t)
    ((MomentumTreeData.integrable_allCellMaskedSpectralAmplitudeSpatial (P := P)) ζ f S hS hK hM hB h k) hKs.aestronglyMeasurable
    (N := ENNReal.ofReal hc.bound ^ 4 * N) (ENNReal.mul_lt_top (by finiteness) hN)
  intro u
  exact (enorm_cutoffTriangleIntegral_le hχ hc
    (R.integrable_linkDensity hL γ δ ((MomentumTreeData.spectralLinksSpatial (P := P)) Q u.1.2.val u.2) hI hbox) t).trans (mul_le_mul' le_rfl (hb _ _))

open WaveTurbulence.Incoh.MomentumTreeData in
/-- The actual masked extension is the sum of its individual cell spectral integrals at every
external time, including the source boundary. -/
theorem MomentumTreeData.allCellMaskedSourceTreeExtension_eq_tsumSpatial {d n m w K M : ℕ}
    (P : MomentumTreeData n m w) {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (hc : Fourier.CutoffControl χ) (ζ : Circle) (R : RootCoordinates n)
    (L γ δ : ℝ) (Q : Fin n → LayerLink d) (I : Set (Fin n → Fin 2 → ℝ))
    (hI : MeasurableSet I) (hbox : I ⊆ Set.univ.pi (fun i => linkBox (Q i)))
    (f : Fin m → Mom d → ℂ)
    (S : (Fin m → Fin d → ℤ) → Finset ((Fin n × Fin 2) → Fin d → ℤ))
    {C : ℝ} (hS : ∀ c, ((S c).card : ℝ) ≤ C ^ n) {B : ℝ}
    (hL : 0 < L) (hK : d + 1 ≤ K) (hM : 2 * d ≤ M) (hB : 0 ≤ B)
    (h : ∀ a, Fourier.spatialNorm K M (f a) ≤ ENNReal.ofReal B)
    {N : ℝ≥0∞} (hN : N < ⊤)
    (hb : ∀ z : (Fin n × Fin 2) → Fin d → ℤ, ∀ ξ : LocalizedCellIndex n m → Fin d → ℝ,
      eLpNorm (R.linkDensity L γ δ ((MomentumTreeData.spectralLinksSpatial (P := P)) Q z ξ) I) 1 ≤ N)
    (t : Fin 2 → ℝ) (k : Mom d) :
    (MomentumTreeData.allCellMaskedSourceTreeExtensionSpatial (P := P)) χ ζ R L γ δ Q I f S t k =
      ∑' u : SourceCellIndex S, ∫ ξ : LocalizedCellIndex n m → Fin d → ℝ,
        (MomentumTreeData.maskedSourceSpectralAmplitudeSpatial (P := P)) ζ f u.1 u.2.val k ξ *
          Fourier.cutoffTriangleIntegral χ (R.linkDensity L γ δ ((MomentumTreeData.spectralLinksSpatial (P := P)) Q u.2.val ξ) I) t := by
  have hs := (MomentumTreeData.integrable_allCellMaskedTreeSlice_of_uniformRootL1Spatial (P := P)) hχ hc ζ R L γ δ Q I
    hI hbox f S hS hL hK hM hB h hN hb t k
  change Integrable (fun u => (MomentumTreeData.allCellMaskedSpectralAmplitudeSpatial (P := P)) ζ f S k u *
    (MomentumTreeData.allCellTreeKernelSpatial (P := P)) R χ L γ δ Q I S t u) (Measure.count.prod volume) at hs
  change (∫ u, (MomentumTreeData.allCellMaskedSpectralAmplitudeSpatial (P := P)) ζ f S k u *
    (MomentumTreeData.allCellTreeKernelSpatial (P := P)) R χ L γ δ Q I S t u ∂(Measure.count.prod volume)) = _
  rw [integral_prod _ hs, integral_countable hs.integral_prod_left]
  simp only [measureReal_def, Measure.count_singleton, ENNReal.toReal_one, one_smul]
  rfl

end WaveTurbulence.Flower.IncTop