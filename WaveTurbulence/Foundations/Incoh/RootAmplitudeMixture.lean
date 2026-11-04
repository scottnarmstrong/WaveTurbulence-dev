/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Incoh.RootAmplitudeMass
public import WaveTurbulence.Foundations.Incoh.LocalModelUniformMassMixture
public import WaveTurbulence.Foundations.Incoh.UniformL1MixtureIntegrability

/-! # Full spatial mixed-norm transport for the tree's actual root partition -/

public section
noncomputable section
open MeasureTheory Filter
open scoped ContDiff ENNReal Topology

namespace WaveTurbulence.Incoh

/-- Conditional finite-root-model transport. Each single-root envelope is integrable with
uniform actual mass; the scalar family remains inside the required common Fourier supremum. -/
theorem mixedFourierNorm_rootAmplitudeMixture_le {r d N : ℕ} {U : Type*}
    [MeasurableSpace U] (μ : Measure U) [SFinite μ] (θ : ℝ)
    (B : (Fin d → ℤ) → Mom d → U → ℂ) (v : (Fin d → ℤ) → U → ℝ)
    (hz : ∀ q k u, treeRootCutoff q k = 0 → B q k u = 0)
    (hB : ∀ q u, ContDiff ℝ N (fun k => B q k u))
    (hm : ∀ q j, j ≤ N → ∀ k, StronglyMeasurable
      (fun u => iteratedFDeriv ℝ j (fun k => B q k u) k))
    (hv : ∀ q, Integrable (v q) μ) (hvm : ∀ q, Measurable (v q)) (hvn : ∀ q u, 0 ≤ v q u)
    (hb : ∀ q j, j ≤ N → ∀ k u, ‖iteratedFDeriv ℝ j (fun k => B q k u) k‖ ≤ v q u)
    {V : ℝ≥0∞} (hmass : ∀ q, (∫⁻ u, ENNReal.ofReal (v q u) ∂μ) ≤ V)
    (K : (Fin r → ℝ) → U → ℂ)
    (hK : StronglyMeasurable (fun z : (Fin r → ℝ) × U => K z.1 z.2))
    (hiK : ∀ u, Integrable (fun t => K t u))
    {H : ℝ≥0∞} (hH : H < ⊤) (hphys : ∀ u, eLpNorm (fun t => K t u) 1 ≤ H) :
    Fourier.mixedFourierNorm θ N 0
      (fun t k => ∫ u, rootAmplitudeSum B k u * K t u ∂μ) ≤
        (ENNReal.ofReal (rootLocalOverlapConstant d) * V) * Fourier.mixedFourierNorm00 θ K := by
  have hloc := rootAmplitudeSum_eventuallyEq_model B hz
  have hm0 (q : Fin d → ℤ) (k : Mom d) : StronglyMeasurable (B q k) := by
    have h := (continuousMultilinearCurryFin0 ℝ (Mom d) ℂ).continuous.comp_stronglyMeasurable
      (hm q 0 (by omega) k)
    simpa only [iteratedFDeriv_zero_eq_comp, Function.comp_apply, LinearIsometryEquiv.apply_symm_apply] using h
  have hmk (k : Mom d) : StronglyMeasurable (rootAmplitudeSum B k) := by
    have he (u : U) : rootAmplitudeSum B k u = rootAmplitudeModel B k k u := (hloc k).self_of_nhds u
    change StronglyMeasurable (fun u => rootAmplitudeSum B k u)
    simp_rw [he]
    exact Finset.stronglyMeasurable_fun_sum (rootLocalCover k) (fun q _ => hm0 q k)
  have hint (k : Mom d) : Integrable (rootAmplitudeSum B k) μ := by
    have henv := integrable_rootAmplitudeModelEnvelope μ v hv k 0
    apply henv.mono' (hmk k).aestronglyMeasurable
    apply ae_of_all
    intro u
    have hh := norm_iteratedFDeriv_rootAmplitudeModel_le B v hB hb (show 0 ≤ N by omega) k k u
    rw [← iteratedFDeriv_rootAmplitudeSum_eq_model B hz] at hh
    simpa only [norm_iteratedFDeriv_zero] using hh
  have hjoint (k : Mom d) := integrable_amplitude_mul_family_of_uniformL1 μ
    (rootAmplitudeSum B k) (hmk k) (hint k) K hK hiK hH hphys
  exact mixedFourierNorm_localModel_uniformMass_le (N := N) μ θ
    (rootAmplitudeSum B) (rootAmplitudeModel B) (rootAmplitudeModelEnvelope v) hloc
    (contDiff_rootAmplitudeModel B hB)
    (fun p j hj k => stronglyMeasurable_rootAmplitudeModel_derivative B hB hm hj p k)
    (fun p j _ => integrable_rootAmplitudeModelEnvelope μ v hv p j)
    (fun p j hj k u => norm_iteratedFDeriv_rootAmplitudeModel_le B v hB hb hj p k u)
    K hK hiK hjoint hH hphys
    (fun j hj k => lintegral_enorm_rootAmplitudeSum_derivative_le μ B v hz hB hb hvm hvn hmass hj k)

end WaveTurbulence.Incoh
