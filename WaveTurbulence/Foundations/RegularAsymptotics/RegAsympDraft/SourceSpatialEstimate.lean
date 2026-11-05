/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.RegularAsymptotics.RegAsympDraft.MaskedSpatialProfile
public import WaveTurbulence.Foundations.RegularAsymptotics.RegAsympDraft.LocalSymbolEnvelope
public import WaveTurbulence.Foundations.RegularAsymptotics.RegAsympDraft.CoefficientMassBudget

/-! # The actual source coefficient bounds control the summed spectral remainder

This is the large-order, full spatial estimate before identifying the
spectral sum with the literal kernel and treating the Wick exceptional set.
-/

public section
noncomputable section
namespace WaveTurbulence.RegAsymp
open MeasureTheory Links Incoh WithLp ClassJR WaveTurbulence.Fourier ApproxNT
open scoped ENNReal

/-- DH23 (remainderbd): explicit source-rate estimate for the actual summed
leaf-only spectral remainder, uniformly for every fixed logarithmic order range.
The assumptions on C are precisely J3's SRep fields. -/
theorem source_spatial_remainder_estimate {d : ℕ} (hd : 3 ≤ d) {γ η : ℝ}
    (hγ : γ ∈ Set.Ioo (0:ℝ) 1) (hη0 : 0 < η) (hη : η ≤ 1/20)
    (hηγ : η ≤ ((d:ℝ)-1)*(1-γ)) (hηγ' : η ≤ γ) :
    ∃ Knt : ℝ, 0 < Knt ∧ ∀ Aorder : ℝ, ∃ L₀ : ℝ, ∀ L : ℝ, L₀ ≤ L →
      ∀ δ : ℝ, L^(-(η/2)) ≤ δ → δ ≤ 1 →
      ∀ (G : Garden 2) (Q : RegCpl) (hQ : Q.Decodes G) (hG : IsCouple G),
      0 < Q.links.length → (Q.links.length:ℝ) ≤ Real.log L^Aorder →
      ∀ (J : Finset (Fin Q.links.length))
        (C : ({j : Fin Q.links.length // j ∉ J} → ℝ) → ℝ × ℝ → ℂ),
      ∀ N Agev : ℝ, 0 ≤ Agev → SRep (1-η/8) (η/4) (1-η/2) Agev N C →
      ∀ Nsp W K M : ℕ, d+2+Nsp ≤ K → W+2*d ≤ M → ∀ Binput Ccover : ℝ, 0 ≤ Binput →
      ∀ F : Mom d → ℂ, Fourier.spatialNorm K M F ≤ ENNReal.ofReal Binput →
      ∀ S : (Fin (2*Q.links.length+1) → Fin d → ℤ) → Finset ((Fin Q.links.length × Fin 2) → Fin d → ℤ),
      (∀ c, ((S c).card:ℝ) ≤ Ccover^Q.links.length) →
      ∀ T : Set (Fin 2 → ℝ), (∀ t ∈ T, ∀ i, t i ∈ Set.Icc (0:ℝ) 1) →
      mixedRestrictionNorm η Nsp W T (Set.univ : Set (Mom d))
        (fun t k => pairedInverseProfile (fun lam => ∫ p,
          maskedLeafSpatialRemainderDensity hQ hG L δ γ J C F S lam p k.val
            ∂leafSpatialMeasure d Q.links.length (2*Q.links.length+1)) t.val) ≤
        ENNReal.ofReal (2^η)*timeFourierNorm η unitSquareCutoff *
          (ENNReal.ofReal (maskedSourceSpatialConstant d (2*Q.links.length+1) Nsp W *
            ((1+2*Real.pi)*(Knt*δ/4)^Q.links.length*spectralFrequencyLoss Q)) *
            (ENNReal.ofReal (L^(-gamma1 d γ+2*η))*localCoefficientMass J η N Agev) *
            (ENNReal.ofReal (Ccover^Q.links.length)*
              ENNReal.ofReal (leafWeightedMomentLocalizationConstant d (Nsp+1) M W*Binput)^(2*Q.links.length+1))) := by
  obtain ⟨Knt,hKnt,hEnv⟩ := local_symbol_remainder_envelope hd hγ hη0 hη hηγ hηγ'
  refine ⟨Knt,hKnt,fun Aorder => ?_⟩
  obtain ⟨L₀,hL₀⟩ := hEnv Aorder
  refine ⟨max L₀ 2,?_⟩
  intro L hL δ hδ hδ1 G Q hQ hG hn hnlog J C N Agev hAgev hS Nsp W K M hK hM Binput Ccover hBinput F hF S hcard T hT
  obtain ⟨B,hmB,hpB,hfB,hbB,hgood⟩ := hL₀ L ((le_max_left _ _).trans hL) δ hδ hδ1
    Q.links.length hn hnlog J C hS.reg N Agev hS.nonneg hAgev hS.norm hS.wnorm
  have hLpos : 0 < L := lt_of_lt_of_le (by norm_num : (0:ℝ)<2) ((le_max_right _ _).trans hL)
  have hδpos : 0 < δ := (Real.rpow_pos_of_pos hLpos _).trans_le hδ
  have hR : 0 ≤ (Knt*δ/4)^Q.links.length := by positivity
  have hb : ∀ᵐ lam : ℝ × ℝ, ∀ (z : (Fin Q.links.length × Fin 2) → Fin d → ℤ)
      (β γ' : Fin Q.links.length → Mom d), ‖localRemainder L δ γ J C β γ' lam z‖ ≤
      ((1+2*Real.pi)*(1+((∑ j, ‖β j‖)+(∑ j, ‖γ' j‖)))*(Knt*δ/4)^Q.links.length)*B lam := hgood
  have hh := maskedSpatial_profile_of_local_envelope hQ hG hd hn L δ γ J hS.reg hK hM
    hBinput hF S hcard hη0.le hT hR hmB hpB hfB hb
  apply hh.trans
  apply mul_le_mul' le_rfl
  apply mul_le_mul' _ le_rfl
  exact mul_le_mul' le_rfl hbB

end WaveTurbulence.RegAsymp
