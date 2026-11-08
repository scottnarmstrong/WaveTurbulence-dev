/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.IncTop.Reg.MovingTreeDecay
public import WaveTurbulence.Foundations.Incoh.CutoffPointwiseL1
public import WaveTurbulence.Foundations.Incoh.PointwiseMixtureIntegrability
public import WaveTurbulence.Foundations.Incoh.TreeCausalGlobalSource

/-! Ported by source from C2-B-TOP `Cut2BReg.MovingTreePointwise` (sha256 in COPIED-SHA256SUMS); mechanical edits only.

R66 spatially modulated scratch copy. Original SHA256 recorded in REG-COPIES.json.

# Pointwise integrability and source agreement for actual tree spectral kernels

The physical root envelope gives spectral integrability at every external
time. Forward-clock agreement retains the literal source causal cut.
-/

public section
noncomputable section
open MeasureTheory Set
open scoped ContDiff ENNReal

namespace WaveTurbulence.Flower.IncTop
open WaveTurbulence.Incoh
open WaveTurbulence.Incoh.MomentumTreeData in
/-- Conditional pointwise Fubini typing for the actual moving tree mixture. -/
theorem MomentumTreeData.integrable_movingTreeSlice_of_uniformRootL1Spatial {d n m w K M : ℕ}
    (P : MomentumTreeData n m w) (ζ : Circle) (R : RootCoordinates n)
    {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ) (hc : Fourier.CutoffControl χ)
    (L γ δ : ℝ) (Q : Fin n → LayerLink d) (I : Set (Fin n → Fin 2 → ℝ))
    (hI : MeasurableSet I) (hbox : I ⊆ univ.pi (fun i => linkBox (Q i)))
    (f : Fin m → Mom d → ℂ)
    (S : Mom d → (Fin m → Fin d → ℤ) → Finset ((Fin n × Fin 2) → Fin d → ℤ))
    {C : ℝ} (hS : ∀ k c, ((S k c).card : ℝ) ≤ C ^ n) {B : ℝ}
    (hL : 0 < L) (hK : d + 1 ≤ K) (hM : 2 * d ≤ M) (hB : 0 ≤ B)
    (h : ∀ a, Fourier.spatialNorm K M (f a) ≤ ENNReal.ofReal B)
    {N : ℝ≥0∞} (hN : N < ⊤)
    (hb : ∀ z : (Fin n × Fin 2) → Fin d → ℤ, ∀ ξ : LocalizedCellIndex n m → Fin d → ℝ,
      eLpNorm (R.linkDensity L γ δ ((MomentumTreeData.spectralLinksSpatial (P := P)) Q z ξ) I) 1 ≤ N)
    (t : Fin 2 → ℝ) (k : Mom d) :
    Integrable (fun u => (MomentumTreeData.movingCellAmplitudeSpatial (P := P)) ζ f S k u * (MomentumTreeData.unrestrictedTreeKernelSpatial (P := P)) R χ L γ δ Q I t u)
      (unrestrictedCellMeasure d n m) := by
  have hKs : StronglyMeasurable ((MomentumTreeData.unrestrictedTreeKernelSpatial (P := P)) R χ L γ δ Q I t) :=
    ((MomentumTreeData.stronglyMeasurable_unrestrictedTreeKernelSpatial (P := P)) R hχ.continuous.measurable hL γ δ Q I hI).comp_measurable
      (g := fun u => (t, u)) (measurable_const.prodMk measurable_id)
  apply integrable_mul_of_uniform_enorm_bound (unrestrictedCellMeasure d n m)
    ((MomentumTreeData.movingCellAmplitudeSpatial (P := P)) ζ f S k) ((MomentumTreeData.unrestrictedTreeKernelSpatial (P := P)) R χ L γ δ Q I t)
    ((MomentumTreeData.integrable_movingCellAmplitudeSpatial (P := P)) ζ f S hS hK hM hB h k) hKs.aestronglyMeasurable
    (N := ENNReal.ofReal hc.bound ^ 4 * N) (ENNReal.mul_lt_top (by finiteness) hN)
  intro u
  exact (enorm_cutoffTriangleIntegral_le hχ hc
    (R.integrable_linkDensity hL γ δ ((MomentumTreeData.spectralLinksSpatial (P := P)) Q u.1.2 u.2) hI hbox) t).trans
      (mul_le_mul' le_rfl (hb _ _))

open WaveTurbulence.Incoh.MomentumTreeData in
/-- The actual spectral tree kernel equals the literal normalized causal source product on
its external source box. Interior and exterior cutoff factors are exactly one there. -/
theorem MomentumTreeData.unrestrictedTreeKernel_agreesSpatial {d n m w : ℕ}
    (P : MomentumTreeData n m w) (R : RootCoordinates n) {χ : ℝ → ℝ}
    (L γ δ : ℝ) (Q : Fin n → LayerLink d) (I : Set (Fin n → Fin 2 → ℝ))
    (hI : MeasurableSet I) (hbox : I ⊆ univ.pi (fun i => linkBox (Q i)))
    (hχ : ∀ a ∈ R.rootBox Q, ∀ j, χ (a j) = 1) (hL : 0 < L)
    (t : Fin 2 → ℝ) (ht : t ∈ R.rootBox Q) (hord : t 1 ≤ t 0)
    (u : UnrestrictedCellIndex d n m × (LocalizedCellIndex n m → Fin d → ℝ)) :
    (MomentumTreeData.unrestrictedTreeKernelSpatial (P := P)) R χ L γ δ Q I t u =
      normalizedLinkIntegral L γ δ ((MomentumTreeData.spectralLinksSpatial (P := P)) Q u.1.2 u.2) (I ∩ R.causalRootCut t) := by
  have he := R.treeCausalExtension_eq_weighted_source hL γ δ
    (fun _ : Mom d => (MomentumTreeData.spectralLinksSpatial (P := P)) Q u.1.2 u.2) (fun _ => I) 0 hI hbox hχ hord
  change Fourier.cutoffTriangleIntegral χ (R.linkDensity L γ δ ((MomentumTreeData.spectralLinksSpatial (P := P)) Q u.1.2 u.2) I) t = _ at he
  change Fourier.cutoffTriangleIntegral χ (R.linkDensity L γ δ ((MomentumTreeData.spectralLinksSpatial (P := P)) Q u.1.2 u.2) I) t =
    R.causalKernel L γ δ ((MomentumTreeData.spectralLinksSpatial (P := P)) Q u.1.2 u.2) I t
  simpa only [hχ t ht 0, hχ t ht 1, Complex.ofReal_one, one_mul] using he

end WaveTurbulence.Flower.IncTop