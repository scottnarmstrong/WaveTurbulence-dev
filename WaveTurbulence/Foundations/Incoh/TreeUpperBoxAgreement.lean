/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Incoh.MovingTreeFamily
public import WaveTurbulence.Foundations.Incoh.ParameterTreeDecay
public import WaveTurbulence.Foundations.Incoh.SpectralTreeClocks
public import WaveTurbulence.Foundations.Incoh.CutoffPointwiseL1
public import WaveTurbulence.Foundations.Incoh.PointwiseMixtureIntegrability
public import WaveTurbulence.Foundations.Incoh.TreeCausalGlobalSource

/-!
# Pointwise integrability and source agreement for actual tree spectral kernels

The physical root envelope gives spectral integrability at every external
time. Forward-clock agreement retains the literal source causal cut.
-/

public section
noncomputable section
open MeasureTheory Set
open scoped ContDiff ENNReal

namespace WaveTurbulence.Incoh

/-- The actual spectral tree kernel equals the literal normalized causal source product on
its external source box. Interior and exterior cutoff factors are exactly one there. -/
theorem MomentumTreeData.unrestrictedTreeKernel_agrees_on_cutoff {d n m w : ℕ}
    (P : MomentumTreeData n m w) (R : RootCoordinates n) {χ : ℝ → ℝ}
    (L γ δ : ℝ) (Q : Fin n → LayerLink d) (I : Set (Fin n → Fin 2 → ℝ))
    (hI : MeasurableSet I) (hbox : I ⊆ univ.pi (fun i => linkBox (Q i)))
    (hχ : ∀ a ∈ R.rootBox Q, ∀ j, χ (a j) = 1) (hL : 0 < L)
    (t : Fin 2 → ℝ) (ht : ∀ j, χ (t j) = 1) (hord : t 1 ≤ t 0)
    (u : UnrestrictedCellIndex d n m × (LocalizedCellIndex n m → Fin d → ℝ)) :
    P.unrestrictedTreeKernel R χ L γ δ Q I t u =
      normalizedLinkIntegral L γ δ (P.spectralLinks Q u.1.2 u.2) (I ∩ R.causalRootCut t) := by
  have he := R.treeCausalExtension_eq_weighted_source hL γ δ
    (fun _ : Mom d => P.spectralLinks Q u.1.2 u.2) (fun _ => I) 0 hI hbox hχ hord
  change Fourier.cutoffTriangleIntegral χ (R.linkDensity L γ δ (P.spectralLinks Q u.1.2 u.2) I) t = _ at he
  change Fourier.cutoffTriangleIntegral χ (R.linkDensity L γ δ (P.spectralLinks Q u.1.2 u.2) I) t =
    R.causalKernel L γ δ (P.spectralLinks Q u.1.2 u.2) I t
  simpa only [ht 0, ht 1, Complex.ofReal_one, one_mul] using he

end WaveTurbulence.Incoh
