/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Spine.RA1LW.LeafSpectralCoefficient
public import WaveTurbulence.Foundations.Spine.RA1LW.LeafLocalDensity
public import WaveTurbulence.Foundations.RegularAsymptotics.RegAsympDraft.HalfCellFourierMixture

/-! # Actual first modulation moment integrability for each leaf-cell coefficient -/

public section
noncomputable section
namespace WaveTurbulence.RA1Leafwise
open WaveTurbulence.RegAsymp
open MeasureTheory Links Incoh WithLp
open scoped ENNReal

/-- The original finite input norm supplies the weighted L1 coefficient
needed by the joint half-cell Fourier/Fubini theorem. -/
theorem integrable_leafCell_modulation_weight {G : Garden 2} {Q : RegCpl}
    (hQ : Q.Decodes G) (hG : IsCouple G) {d K M : ℕ}
    {F : Fin (2*Q.links.length+1) → Mom d → ℂ} {B : ℝ} (hK : d+2 ≤ K) (hM : 2*d ≤ M) (hB : 0 ≤ B)
    (hF : (∀ a, Fourier.spatialNorm K M (F a) ≤ ENNReal.ofReal B))
    (c : Fin (2*Q.links.length+1) → Fin d → ℤ) :
    Integrable (fun α : Fin (2*Q.links.length+1) → Fin d → ℝ =>
      ‖leafSpectrumCoefficient F c α‖*
        (1+((∑ j, ‖(leafModulations hQ hG α).1 j‖)+(∑ j, ‖(leafModulations hQ hG α).2 j‖)))) := by
  have hcoef : StronglyMeasurable (fun α : Fin (2*Q.links.length+1) → Fin d → ℝ =>
      leafSpectrumCoefficient F c α) :=
    (stronglyMeasurable_leafSpectrumCoefficient (by omega) hB hF).comp_measurable
      (g := fun α : Fin (2*Q.links.length+1) → Fin d → ℝ => (c,α))
      (measurable_const.prodMk measurable_id)
  have hweight : Continuous (fun α : Fin (2*Q.links.length+1) → Fin d → ℝ =>
      1+((∑ j, ‖(leafModulations hQ hG α).1 j‖)+(∑ j, ‖(leafModulations hQ hG α).2 j‖))) := by
    have hc := continuous_leafModulations hQ hG d
    exact continuous_const.add
      ((continuous_finsetSum _ (fun j _ => ((continuous_apply j).comp hc.fst).norm)).add
        (continuous_finsetSum _ (fun j _ => ((continuous_apply j).comp hc.snd).norm)))
  refine ⟨(hcoef.norm.mul hweight.stronglyMeasurable).aestronglyMeasurable,?_⟩
  rw [hasFiniteIntegral_iff_enorm]
  have hmass := tsum_leaf_modulation_firstMoment_le hQ hG hK hM hB hF
  have hcell : (∫⁻ α : Fin (2*Q.links.length+1) → Fin d → ℝ,
      ENNReal.ofReal (1+((∑ j, ‖(leafModulations hQ hG α).1 j‖)+
        (∑ j, ‖(leafModulations hQ hG α).2 j‖))) * ‖leafSpectrumCoefficient F c α‖ₑ) ≤
      ENNReal.ofReal (spectralFrequencyLoss Q)*
        ENNReal.ofReal (leafFirstMomentConstant d M*B)^(2*Q.links.length+1) := by
    apply le_trans _ hmass
    simpa only [leafModulations,enorm_leafSpectrumCoefficient] using
      (ENNReal.le_tsum (f := fun c : Fin (2*Q.links.length+1) → Fin d → ℤ =>
        ∫⁻ α : Fin (2*Q.links.length+1) → Fin d → ℝ,
          ENNReal.ofReal (1+((∑ j, ‖sourceFrequencyPullback hQ hG (fun a => toLp 2 (α a)) (some (j,0))‖)+
            (∑ j, ‖sourceFrequencyPullback hQ hG (fun a => toLp 2 (α a)) (some (j,1))‖))) *
            ∏ a, ‖Fourier.timeFourier (fun y : Fin d → ℝ => leafCell (F a) (c a) (toLp 2 y)) (α a)‖ₑ) c)
  apply lt_of_le_of_lt _ (hcell.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (by finiteness)))
  apply lintegral_mono
  intro α
  dsimp only
  rw [Real.enorm_eq_ofReal (by positivity),ENNReal.ofReal_mul (norm_nonneg _),ofReal_norm]
  exact le_of_eq (mul_comm _ _)

/-- Absolute coefficient masses are summable over all actual leaf centers,
using the original input norm and only one source modulation moment. -/
theorem summable_leafCell_modulation_integral {G : Garden 2} {Q : RegCpl}
    (hQ : Q.Decodes G) (hG : IsCouple G) {d K M : ℕ}
    {F : Fin (2*Q.links.length+1) → Mom d → ℂ} {B : ℝ} (hK : d+2 ≤ K) (hM : 2*d ≤ M) (hB : 0 ≤ B)
    (hF : (∀ a, Fourier.spatialNorm K M (F a) ≤ ENNReal.ofReal B)) :
    Summable (fun c : Fin (2*Q.links.length+1) → Fin d → ℤ =>
      ∫ α : Fin (2*Q.links.length+1) → Fin d → ℝ,
        ‖leafSpectrumCoefficient F c α‖*
          (1+((∑ j, ‖(leafModulations hQ hG α).1 j‖)+(∑ j, ‖(leafModulations hQ hG α).2 j‖)))) := by
  let f := fun (c : Fin (2*Q.links.length+1) → Fin d → ℤ)
      (α : Fin (2*Q.links.length+1) → Fin d → ℝ) =>
    ‖leafSpectrumCoefficient F c α‖*
      (1+((∑ j, ‖(leafModulations hQ hG α).1 j‖)+(∑ j, ‖(leafModulations hQ hG α).2 j‖)))
  let g := fun c : Fin (2*Q.links.length+1) → Fin d → ℤ =>
    ∫⁻ α : Fin (2*Q.links.length+1) → Fin d → ℝ,
      ENNReal.ofReal (1+((∑ j, ‖(leafModulations hQ hG α).1 j‖)+
        (∑ j, ‖(leafModulations hQ hG α).2 j‖))) * ‖leafSpectrumCoefficient F c α‖ₑ
  have hmass : ∑' c, g c ≤ ENNReal.ofReal (spectralFrequencyLoss Q)*
      ENNReal.ofReal (leafFirstMomentConstant d M*B)^(2*Q.links.length+1) := by
    simpa only [g,leafModulations,enorm_leafSpectrumCoefficient] using
      tsum_leaf_modulation_firstMoment_le hQ hG hK hM hB hF
  have hs := ENNReal.summable_toReal (hmass.trans_lt
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (by finiteness))).ne
  have he (c : Fin (2*Q.links.length+1) → Fin d → ℤ) :
      (g c).toReal = ∫ α, f c α := by
    have hg : g c = ∫⁻ α, ‖f c α‖ₑ := by
      apply lintegral_congr
      intro α
      dsimp only [f]
      rw [Real.enorm_eq_ofReal (by positivity),ENNReal.ofReal_mul (norm_nonneg _),ofReal_norm]
      exact mul_comm _ _
    rw [hg,← integral_norm_eq_lintegral_enorm
      (integrable_leafCell_modulation_weight hQ hG hK hM hB hF c).aestronglyMeasurable]
    apply integral_congr_ae
    apply ae_of_all
    intro α
    dsimp only [f]
    exact Real.norm_of_nonneg (by positivity)
  exact hs.congr he

/-- The actual independent leaf Fourier coefficient and actual modulated
half-cell Fourier coefficient form an absolutely integrable joint density. -/
theorem integrable_leafCell_halfCellFourier {G : Garden 2} {Q : RegCpl}
    (hQ : Q.Decodes G) (hG : IsCouple G) {d K M : ℕ} (hn : 0 < Q.links.length)
    {F : Fin (2*Q.links.length+1) → Mom d → ℂ} {B : ℝ} (hK : d+2 ≤ K) (hM : 2*d ≤ M) (hB : 0 ≤ B)
    (hF : (∀ a, Fourier.spatialNorm K M (F a) ≤ ENNReal.ofReal B))
    (c : Fin (2*Q.links.length+1) → Fin d → ℤ)
    (z : (Fin Q.links.length × Fin 2) → Fin d → ℤ) :
    Integrable (fun p : (Fin (2*Q.links.length+1) → Fin d → ℝ) ×
        ((Fin Q.links.length → Mom d) × (Fin Q.links.length → Mom d)) =>
      leafSpectrumCoefficient F c p.1 *
        ApproxNT.fourierW (halfCellAmplitude z (leafModulations hQ hG p.1).1
          (leafModulations hQ hG p.1).2) p.2.1 p.2.2) := by
  have hcoef : StronglyMeasurable (fun α : Fin (2*Q.links.length+1) → Fin d → ℝ =>
      leafSpectrumCoefficient F c α) :=
    (stronglyMeasurable_leafSpectrumCoefficient (by omega) hB hF).comp_measurable
      (g := fun α : Fin (2*Q.links.length+1) → Fin d → ℝ => (c,α))
      (measurable_const.prodMk measurable_id)
  have hβ : Measurable (fun α : Fin (2*Q.links.length+1) → Fin d → ℝ =>
      (leafModulations hQ hG α).1) := (continuous_leafModulations hQ hG d).fst.measurable
  have hγ : Measurable (fun α : Fin (2*Q.links.length+1) → Fin d → ℝ =>
      (leafModulations hQ hG α).2) := (continuous_leafModulations hQ hG d).snd.measurable
  have hh := (halfCellFourierMixture_integrable_mass volume hn z _ _ hβ hγ _ hcoef
    (integrable_leafCell_modulation_weight hQ hG hK hM hB hF c)).1
  exact hh

end WaveTurbulence.RA1Leafwise
