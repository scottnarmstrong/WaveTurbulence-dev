/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.RegularAsymptotics.RegAsympDraft.LeafScalarProfile
public import WaveTurbulence.Foundations.RegularAsymptotics.RegAsympDraft.WickCorrectionSourceEnvelope
public import WaveTurbulence.Foundations.RegularAsymptotics.RegAsympDraft.CoefficientMassBudget

/-! # The actual source coefficient bounds control the spatial Wick correction

This is the full spatial estimate for the literal squared-Wick correction,
before its identification with the corresponding term in the source kernel.
-/

public section
noncomputable section
namespace WaveTurbulence.RegAsymp
open MeasureTheory Links Incoh WithLp ClassJR WaveTurbulence.Fourier ApproxNT
open scoped ENNReal

/-- DH23 (remainderbd): explicit source-rate estimate for the actual Wick
correction, uniformly for every fixed logarithmic order range.
The assumptions on C are precisely J3's SRep fields. -/
theorem source_spatial_wick_estimate {d : ℕ} (hd : 3 ≤ d) {γ η : ℝ}
    (hγ : γ ∈ Set.Ioo (0:ℝ) 1) (hη0 : 0 < η) (hη : η ≤ 1/20)
    (hηγ : η ≤ ((d:ℝ)-1)*(1-γ)) (hηγ' : η ≤ γ) :
    ∀ Agev : ℝ, 0 ≤ Agev → ∃ Knt : ℝ, 0 < Knt ∧ ∀ Aorder : ℝ, ∃ L₀ : ℝ, ∀ L : ℝ, L₀ ≤ L →
      ∀ δ : ℝ, L^(-(η/2)) ≤ δ → δ ≤ 1 →
      ∀ (G : Garden 2) (Q : RegCpl) (hQ : Q.Decodes G) (hG : IsCouple G),
      (Q.links.length:ℝ) ≤ Real.log L^Aorder →
      ∀ (J : Finset (Fin Q.links.length))
        (C : ({j : Fin Q.links.length // j ∉ J} → ℝ) → ℝ × ℝ → ℂ),
      ∀ N : ℝ, SRep (1-η/8) (η/4) (1-η/2) Agev N C →
      ∀ Nsp W K M : ℕ, d+2+Nsp ≤ K → W+2*d ≤ M → ∀ Binput Ccover : ℝ, 0 ≤ Binput →
      ∀ F : Mom d → ℂ, Fourier.spatialNorm K M F ≤ ENNReal.ofReal Binput →
      ∀ S : (Fin (2*Q.links.length+1) → Fin d → ℤ) → Finset ((Fin Q.links.length × Fin 2) → Fin d → ℤ),
      (∀ c, ((S c).card:ℝ) ≤ Ccover^Q.links.length) →
      ∀ T : Set (Fin 2 → ℝ), (∀ t ∈ T, ∀ i, t i ∈ Set.Icc (0:ℝ) 1) →
      mixedRestrictionNorm η Nsp W T (Set.univ : Set (Mom d))
        (fun t k => pairedInverseProfile (fun lam => ∫ p,
          maskedLeafScalarDensity hQ hG
            (fun lam β γ' z => normalizedWickCorrection L δ γ z β γ' J C lam) F S (lam,p) k.val
            ∂leafSpatialMeasure d Q.links.length (2*Q.links.length+1)) t.val) ≤
        ENNReal.ofReal (2^η)*timeFourierNorm η unitSquareCutoff *
          (ENNReal.ofReal (maskedSourceSpatialConstant d (2*Q.links.length+1) Nsp W *
            ((1+2*Real.pi)*(Knt*δ)^Q.links.length*spectralFrequencyLoss Q)) *
            ((4:ℝ≥0∞)^Q.links.length*ENNReal.ofReal (L^(-gamma1 d γ))*
              ((ENNReal.ofReal N*∑' k : ℕ,
                ENNReal.ofReal ((4*Agev)^k*((2*k).factorial:ℝ)/(4*k).factorial)) +
                (∫⁻ lam, wL η lam*ENNReal.ofReal (frequencyGaussian lam)))) *
            (ENNReal.ofReal (Ccover^Q.links.length)*
              ENNReal.ofReal (leafWeightedMomentLocalizationConstant d (Nsp+1) M W*Binput)^(2*Q.links.length+1))) := by
  intro Agev hAgev
  obtain ⟨Knt,hKnt,hEnv⟩ := wick_correction_scalar_envelope hd hγ hη0 hη hηγ hηγ' Agev hAgev
  refine ⟨Knt,hKnt,fun Aorder => ?_⟩
  obtain ⟨L₀,hL₀⟩ := hEnv Aorder
  refine ⟨max L₀ 2,?_⟩
  intro L hL δ hδ hδ1 G Q hQ hG hnlog J C N hS Nsp W K M hK hM Binput Ccover hBinput F hF S hcard T hT
  have hmain (k : ℕ) : ∫⁻ α, ∫⁻ lam, wL η lam*dnorm k C α lam ≤ gev N Agev k := by
    apply le_trans _ (hS.norm k)
    apply lintegral_mono
    intro α
    apply lintegral_mono
    intro lam
    exact mul_le_mul' (temporalWeight_mono (by linarith : η ≤ 1-η/8) lam) le_rfl
  obtain ⟨B,hmB,hpB,hfB,hbB,hgood⟩ := hL₀ L ((le_max_left _ _).trans hL) δ hδ hδ1
    Q.links.length hnlog J C hS.reg N hS.nonneg hmain
  have hLpos : 0 < L := lt_of_lt_of_le (by norm_num : (0:ℝ)<2) ((le_max_right _ _).trans hL)
  have hδpos : 0 < δ := (Real.rpow_pos_of_pos hLpos _).trans_le hδ
  have hr : 0 ≤ (Knt*δ)^Q.links.length := by positivity
  have hh := leafScalar_profile_of_local_envelope hQ hG
    (fun lam β γ' z => normalizedWickCorrection L δ γ z β γ' J C lam)
    (fun z => stronglyMeasurable_normalizedWickCorrection_joint hLpos δ γ z J hS.reg.meas)
    hK hM hBinput hF S hcard hη0.le hT hr hmB hpB hfB hgood
  apply hh.trans
  apply mul_le_mul' le_rfl
  apply mul_le_mul' _ le_rfl
  exact mul_le_mul' le_rfl hbB

end WaveTurbulence.RegAsymp
