/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Spine.RA1LW.PhysicalErrorEnvelope
public import WaveTurbulence.Foundations.Spine.RA1LW.PhysicalErrorRegularity
public import WaveTurbulence.Foundations.Spine.RA1LW.LeafScalarProfile
public import WaveTurbulence.Foundations.Spine.RA1LW.SourceScalarProfile

/-! # Full landed mixed restriction estimate of the combined physical error -/

public section
noncomputable section
namespace WaveTurbulence.RA1Leafwise
open WaveTurbulence.RegAsymp
open MeasureTheory Links Incoh ClassJR ApproxNT WaveTurbulence.Fourier
open scoped ENNReal

/-- The literal combined physical error has the full source-rate mixed
restriction estimate, with constants chosen before the order exponent. -/
theorem physical_error_spatial_estimate {d : ℕ} (hd : 3 ≤ d) {γ η : ℝ}
    (hγ : γ ∈ Set.Ioo (0:ℝ) 1) (hη0 : 0 < η) (hη : η ≤ 1/20)
    (hηγ : η ≤ ((d:ℝ)-1)*(1-γ)) (hηγ' : η ≤ γ)
    {Agev Cbase : ℝ} (hAgev : 0 ≤ Agev) (hCbase : 1 ≤ Cbase) :
    ∃ Kr Cm : ℝ, 0 < Kr ∧ 1 ≤ Cm ∧
      ∀ Aorder : ℝ, ∃ L₀ : ℝ, ∀ L : ℝ, L₀ ≤ L →
      ∀ δ : ℝ, L^(-(η/2)) ≤ 2*δ → 2*δ ≤ 1 →
      ∀ (G : Garden 2) (Q : RegCpl) (hQ : Q.Decodes G) (hG : IsCouple G),
      0 < Q.links.length → (Q.links.length:ℝ) ≤ Real.log L^Aorder →
      ∀ C : (Z : (chosenSet Q.links).powerset) →
        ({j : Fin Q.links.length // j ∉ markedLinkIndices Q Z.val} → ℝ) → ℝ × ℝ → ℂ,
      (∀ Z, SRep (1-η/8) (η/4) (1-η/2) Agev (Cbase^(4*Q.links.length+1)) (C Z)) →
      ∀ ζ : ℂ, ‖ζ‖ ≤ 1 →
      ∀ Nsp W K M : ℕ, d+2+Nsp ≤ K → W+2*d ≤ M → ∀ Binput Ccover : ℝ, 0 ≤ Binput →
      ∀ F : Fin (2*Q.links.length+1) → Mom d → ℂ, (∀ a, spatialNorm K M (F a) ≤ ENNReal.ofReal Binput) →
      ∀ S : (Fin (2*Q.links.length+1) → Fin d → ℤ) → Finset ((Fin Q.links.length × Fin 2) → Fin d → ℤ),
      (∀ c, ((S c).card:ℝ) ≤ Ccover^Q.links.length) →
      ∀ T : Set (Fin 2 → ℝ), (∀ t ∈ T, ∀ i, t i ∈ Set.Icc (0:ℝ) 1) →
      mixedRestrictionNorm η Nsp W T Set.univ
        (fun t k => sourceScalarProfile hQ hG (physicalErrorScalar L δ γ Q ζ C) F S t.val k.val) ≤
        ENNReal.ofReal (2^η)*timeFourierNorm η unitSquareCutoff *
          (ENNReal.ofReal (maskedSourceSpatialConstant d (2*Q.links.length+1) Nsp W *
            ((1+2*Real.pi)*(Kr*δ)^Q.links.length*spectralFrequencyLoss Q)) *
            (ENNReal.ofReal (L^(-gamma1 d γ+2*η))*ENNReal.ofReal Cm^Q.links.length) *
            (ENNReal.ofReal (Ccover^Q.links.length)*
              ENNReal.ofReal (leafWeightedMomentLocalizationConstant d (Nsp+1) M W*Binput)^(2*Q.links.length+1))) := by
  obtain ⟨Kr,Cm,hKr,hCm,henv⟩ := physical_error_scalar_envelope hd hγ hη0 hη hηγ hηγ' hAgev hCbase
  refine ⟨Kr,Cm,hKr,hCm,?_⟩
  intro Aorder
  obtain ⟨L₀,henv⟩ := henv Aorder
  refine ⟨max 2 L₀,?_⟩
  intro L hL δ hδ hδ1 G Q hQ hG hn hnlog C hC ζ hζ Nsp W K M hK hM Binput Ccover hBi F hF S hcard T hT
  have hLpos : 0 < L := lt_of_lt_of_le (by norm_num : (0:ℝ)<2) ((le_max_left _ _).trans hL)
  have hδpos : 0 < δ := by
    have hh := (Real.rpow_pos_of_pos hLpos (-(η/2))).trans_le hδ
    linarith only [hh]
  obtain ⟨B,hmB,hpB,hfB,hbB,hgood⟩ := henv L ((le_max_right _ _).trans hL) δ hδ hδ1 Q hn hnlog C hC ζ hζ
  have hh := leafScalar_profile_of_local_envelope hQ hG (physicalErrorScalar L δ γ Q ζ C)
    (stronglyMeasurable_physicalErrorScalar_joint hd Q hn hLpos δ γ ζ C (fun Z => (hC Z).reg.meas))
    hK hM hBi hF S hcard hη0.le hT (by positivity : 0 ≤ (Kr*δ)^Q.links.length)
    hmB hpB hfB hgood
  apply hh.trans
  apply mul_le_mul' le_rfl
  apply mul_le_mul' _ le_rfl
  exact mul_le_mul' le_rfl hbB

end WaveTurbulence.RA1Leafwise
