/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.RegAsymp.TreeRootLeafMixture
public import WaveTurbulence.Foundations.RegAsymp.PairedProfileRestriction
public import WaveTurbulence.Foundations.ClassJR.MCCase1

/-! # Common inverse-profile envelopes in the actual tree spatial mixture -/

@[expose] public section
noncomputable section
namespace WaveTurbulence.RegAsymp
open MeasureTheory Incoh ClassJR
open scoped ENNReal

/-- Joint measurability of the original two-time inverse profile with arbitrary measurable
spectral parameters. This is typing data for the genuine spatial-mixture integral. -/
theorem stronglyMeasurable_treePairedProfile {U : Type*} [MeasurableSpace U]
    (A : (ℝ × ℝ) → U → ℂ)
    (hA : StronglyMeasurable (Function.uncurry A)) :
    StronglyMeasurable (fun p : (Fin 2 → ℝ) × U =>
      unitSquareCutoff p.1 * pairedInverseProfile (fun lam => A lam p.2) p.1) := by
  have he : StronglyMeasurable (fun p : ((Fin 2 → ℝ) × U) × (ℝ × ℝ) =>
      e2 p.2 (p.1.1 0) (p.1.1 1)) := by
    have hm : Measurable (fun p : ((Fin 2 → ℝ) × U) × (ℝ × ℝ) =>
        (p.2,(p.1.1 0,p.1.1 1))) := by fun_prop
    exact (continuous_e2.measurable.comp hm).stronglyMeasurable
  have hc : StronglyMeasurable (fun p : ((Fin 2 → ℝ) × U) × (ℝ × ℝ) => A p.2 p.1.2) :=
    hA.comp_measurable (measurable_snd.prodMk measurable_fst.snd)
  have hi : StronglyMeasurable (fun p : (Fin 2 → ℝ) × U =>
      pairedInverseProfile (fun lam => A lam p.2) p.1) := (hc.mul he).integral_prod_right' 
  exact ((contDiff_unitSquareCutoff.continuous.stronglyMeasurable).comp_measurable measurable_fst).mul hi

/-- A common frequency envelope gives the physical L1 bound required by the locally
finite tree root model, with the actual compact extension cutoff. -/
theorem eLpNorm_treePairedProfile_one_le {A : (ℝ × ℝ) → ℂ} (hA : Integrable A)
    {B : (ℝ × ℝ) → ℝ≥0∞} (hbound : ∀ᵐ lam : ℝ × ℝ, ‖A lam‖ₑ ≤ B lam) :
    eLpNorm (fun t => unitSquareCutoff t * pairedInverseProfile A t) 1 ≤
      (∫⁻ t, ‖unitSquareCutoff t‖ₑ) * ∫⁻ lam, B lam := by
  rw [eLpNorm_one_eq_lintegral_enorm
    (integrable_mul_pairedInverseProfile integrable_unitSquareCutoff hA).aestronglyMeasurable]
  have hp (t : Fin 2 → ℝ) : ‖pairedInverseProfile A t‖ₑ ≤ ∫⁻ lam, B lam := by
    apply (enorm_integral_le_lintegral_enorm _).trans
    apply lintegral_mono_ae
    filter_upwards [hbound] with lam hlam
    rw [enorm_mul]
    have he : ‖e2 lam (t 0) (t 1)‖ₑ = 1 := by rw [← ofReal_norm, norm_e2]; norm_num
    simpa only [he,mul_one] using hlam
  calc
    _ ≤ ∫⁻ t, ‖unitSquareCutoff t‖ₑ * ∫⁻ lam, B lam := lintegral_mono (fun t => by
      rw [enorm_mul]; exact mul_le_mul' le_rfl (hp t))
    _ = _ := lintegral_mul_const _ contDiff_unitSquareCutoff.continuous.measurable.enorm

/-- The common original-frequency envelope gives the full tree spatial norm.
The envelope is a scalar profile bound, before any source NT/Wick application. -/
theorem mixedFourierNorm_treeRootPairedProfile_le {d n m K M J : ℕ} {θ : ℝ}
    (hθ : 0 ≤ θ) (f : Fin m → Mom d → ℂ) {Binput C : ℝ}
    (hK : d+2+J ≤ K) (hM : 2*d ≤ M) (hBinput : 0 ≤ Binput)
    (hf : ∀ a, Fourier.spatialNorm K M (f a) ≤ ENNReal.ofReal Binput)
    (S : (Fin (m+1) → Fin d → ℤ) → Finset ((Fin n × Fin 2) → Fin d → ℤ))
    (hS : ∀ c, ((S c).card:ℝ) ≤ C^n)
    (A : (ℝ × ℝ) → (SourceCellIndex S × (Fin (m+1) → Fin d → ℝ)) → ℂ)
    (hA : StronglyMeasurable (Function.uncurry A))
    {B : (ℝ × ℝ) → ℝ≥0∞} (hB : Measurable B)
    (hbound : ∀ u, ∀ᵐ lam : ℝ × ℝ, ‖A lam u‖ₑ ≤ B lam)
    (hfinite : (∫⁻ lam, wL θ lam * B lam) < ⊤) :
    Fourier.mixedFourierNorm θ J 0
      (treeRootLeafMixture f S (fun t u => unitSquareCutoff t * pairedInverseProfile (fun lam => A lam u) t)) ≤
      (ENNReal.ofReal (rootLocalOverlapConstant d) *
        (ENNReal.ofReal (treeRootLeafDerivativeConstant d J) * (ENNReal.ofReal (C^n) *
          ENNReal.ofReal (leafMomentLocalizationConstant d (J+1) M *
            treeAugmentedInputBound d K M Binput)^(m+1)))) *
        (ENNReal.ofReal (2^θ)*Fourier.timeFourierNorm θ unitSquareCutoff*
          (∫⁻ lam, wL θ lam*B lam)) := by
  have hiA (u : SourceCellIndex S × (Fin (m+1) → Fin d → ℝ)) : Integrable (fun lam => A lam u) :=
    integrable_of_wL_envelope hθ
      (hA.comp_measurable (measurable_id.prodMk measurable_const)).aestronglyMeasurable (hbound u) hfinite
  have hmass : (∫⁻ lam, B lam) < ⊤ := lt_of_le_of_lt (lintegral_mono fun lam =>
    le_mul_of_one_le_left bot_le (one_le_wL hθ lam)) hfinite
  have hH : ((∫⁻ t, ‖unitSquareCutoff t‖ₑ) * ∫⁻ lam, B lam) < ⊤ :=
    ENNReal.mul_lt_top (hasFiniteIntegral_iff_enorm.mp integrable_unitSquareCutoff.2) hmass
  apply (mixedFourierNorm_treeRootLeafMixture_le θ f hK hM hBinput hf S hS
    (fun t u => unitSquareCutoff t * pairedInverseProfile (fun lam => A lam u) t)
    (stronglyMeasurable_treePairedProfile A hA)
    (fun u => integrable_mul_pairedInverseProfile integrable_unitSquareCutoff (hiA u)) hH
    (fun u => eLpNorm_treePairedProfile_one_le (hiA u) (hbound u))).trans
  exact mul_le_mul' le_rfl (mixedFourierNorm00_pairedProfile_le hθ integrable_unitSquareCutoff hiA hB hbound)

end WaveTurbulence.RegAsymp
