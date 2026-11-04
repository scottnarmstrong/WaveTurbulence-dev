/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.RegAsymp.TreeRootLeafEnvelope
public import WaveTurbulence.Foundations.Incoh.RootAmplitudeMixture

/-! # Spatial transport of the actual tree leaf-only spectral mixture

The locally finite moving-root partition carries the literal spatial derivatives.
The scalar time family retains its common Fourier supremum inside the integral.
-/

@[expose] public section
noncomputable section
namespace WaveTurbulence.RegAsymp
open MeasureTheory Incoh
open scoped ENNReal ContDiff

/-- The actual tree spectral mixture, with the root partition inside its amplitude. -/
def treeRootLeafMixture {r d n m : ℕ} (f : Fin m → Mom d → ℂ)
    (S : (Fin (m+1) → Fin d → ℤ) → Finset ((Fin n × Fin 2) → Fin d → ℤ))
    (G : (Fin r → ℝ) → (SourceCellIndex S × (Fin (m+1) → Fin d → ℝ)) → ℂ)
    (t : Fin r → ℝ) (k : Mom d) : ℂ :=
  ∫ u, rootAmplitudeSum (treeRootLeafAmplitude f S) k u * G t u ∂treeLeafCellMeasure S

/-- Actual source spatial norms imply a uniform derivative-mass bound for the tree
mixture. The scalar family's Fourier norm is kept intact, before any NT estimate. -/
theorem mixedFourierNorm_treeRootLeafMixture_le {r d n m K M J : ℕ}
    (θ : ℝ) (f : Fin m → Mom d → ℂ) {B C : ℝ}
    (hK : d+2+J ≤ K) (hM : 2*d ≤ M) (hB : 0 ≤ B)
    (hf : ∀ a, Fourier.spatialNorm K M (f a) ≤ ENNReal.ofReal B)
    (S : (Fin (m+1) → Fin d → ℤ) → Finset ((Fin n × Fin 2) → Fin d → ℤ))
    (hS : ∀ c, ((S c).card:ℝ) ≤ C^n)
    (G : (Fin r → ℝ) → (SourceCellIndex S × (Fin (m+1) → Fin d → ℝ)) → ℂ)
    (hG : StronglyMeasurable (fun z : (Fin r → ℝ) ×
      (SourceCellIndex S × (Fin (m+1) → Fin d → ℝ)) => G z.1 z.2))
    (hiG : ∀ u, Integrable (fun t => G t u))
    {H : ℝ≥0∞} (hH : H < ⊤) (hphys : ∀ u, eLpNorm (fun t => G t u) 1 ≤ H) :
    Fourier.mixedFourierNorm θ J 0 (treeRootLeafMixture f S G) ≤
      (ENNReal.ofReal (rootLocalOverlapConstant d) *
        (ENNReal.ofReal (treeRootLeafDerivativeConstant d J) * (ENNReal.ofReal (C^n) *
          ENNReal.ofReal (leafMomentLocalizationConstant d (J+1) M *
            treeAugmentedInputBound d K M B)^(m+1)))) * Fourier.mixedFourierNorm00 θ G := by
  exact mixedFourierNorm_rootAmplitudeMixture_le (N := J) (treeLeafCellMeasure S) θ
    (treeRootLeafAmplitude f S) (treeRootLeafEnvelope J f S)
    (treeRootLeafAmplitude_eq_zero f S)
    (fun q u => (contDiff_treeRootLeafAmplitude f S q u).of_le (by simp))
    (fun q j _ k => stronglyMeasurable_treeRootLeafAmplitude_derivative f (by omega) hf S q k j)
    (fun q => integrable_treeRootLeafEnvelope J f hK hM hB hf S hS q)
    (fun q => measurable_treeRootLeafEnvelope J f (by omega) hf S q)
    (treeRootLeafEnvelope_nonneg J f S)
    (fun q j hj k u => norm_iteratedFDeriv_treeRootLeafAmplitude_le f S q hj k u)
    (fun q => lintegral_treeRootLeafEnvelope_le J f hK hM hB hf S hS q)
    G hG hiG hH hphys

end WaveTurbulence.RegAsymp
