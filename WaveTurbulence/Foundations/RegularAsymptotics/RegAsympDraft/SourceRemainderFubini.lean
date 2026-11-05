/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.RegularAsymptotics.RegAsympDraft.LeafScalarFubini
public import WaveTurbulence.Foundations.RegularAsymptotics.RegAsympDraft.SourceSpatialEstimate
public import WaveTurbulence.Foundations.RegularAsymptotics.RegAsympDraft.WickSpatialEstimate

/-! # Actual NT and Wick source premises imply global joint spectral integrability -/

public section
noncomputable section
namespace WaveTurbulence.RegAsymp
open MeasureTheory Links Incoh ClassJR WaveTurbulence.Fourier ApproxNT

/-- Original SRep coefficient fields and original input norms supply
actual joint-L1 NT/Wick densities in every fixed logarithmic order range.
No source remainder identity or integrability witness is assumed. -/
theorem source_remainders_joint_integrable {d : ℕ} (hd : 3 ≤ d) {γ η : ℝ}
    (hγ : γ ∈ Set.Ioo (0:ℝ) 1) (hη0 : 0 < η) (hη : η ≤ 1/20)
    (hηγ : η ≤ ((d:ℝ)-1)*(1-γ)) (hηγ' : η ≤ γ)
    (Agev : ℝ) (hAgev : 0 ≤ Agev) :
    ∀ Aorder : ℝ, ∃ L₀ : ℝ, ∀ L : ℝ, L₀ ≤ L →
      ∀ δ : ℝ, L^(-(η/2)) ≤ δ → δ ≤ 1 →
      ∀ (G : Garden 2) (Q : RegCpl) (hQ : Q.Decodes G) (hG : IsCouple G),
      0 < Q.links.length → (Q.links.length:ℝ) ≤ Real.log L^Aorder →
      ∀ (J : Finset (Fin Q.links.length))
        (C : ({j : Fin Q.links.length // j ∉ J} → ℝ) → ℝ × ℝ → ℂ),
      ∀ N : ℝ, SRep (1-η/8) (η/4) (1-η/2) Agev N C →
      ∀ K M : ℕ, d+2 ≤ K → 2*d ≤ M → ∀ Binput Ccover : ℝ, 0 ≤ Binput →
      ∀ F : Mom d → ℂ, spatialNorm K M F ≤ ENNReal.ofReal Binput →
      ∀ S : (Fin (2*Q.links.length+1) → Fin d → ℤ) →
        Finset ((Fin Q.links.length × Fin 2) → Fin d → ℤ),
      (∀ c, ((S c).card:ℝ) ≤ Ccover^Q.links.length) → ∀ k : Mom d,
      Integrable (fun q => maskedLeafScalarDensity hQ hG
        (fun lam β γ' z => localRemainder L δ γ J C β γ' lam z) F S q k)
        (volume.prod (leafSpatialMeasure d Q.links.length (2*Q.links.length+1))) ∧
      Integrable (fun q => maskedLeafScalarDensity hQ hG
        (fun lam β γ' z => normalizedWickCorrection L δ γ z β γ' J C lam) F S q k)
        (volume.prod (leafSpatialMeasure d Q.links.length (2*Q.links.length+1))) := by
  obtain ⟨KN,hKN,hNT⟩ := local_symbol_remainder_envelope hd hγ hη0 hη hηγ hηγ'
  obtain ⟨KW,hKW,hWK⟩ := wick_correction_scalar_envelope hd hγ hη0 hη hηγ hηγ' Agev hAgev
  intro Aorder
  obtain ⟨LN,hN⟩ := hNT Aorder
  obtain ⟨LW,hW⟩ := hWK Aorder
  refine ⟨max 2 (max LN LW),?_⟩
  intro L hL δ hδ hδ1 G Q hQ hG hn hnlog J C N hS K M hK hM Binput Ccover hBi F hF S hcard k
  have hL2 : 2 ≤ L := (le_max_left _ _).trans hL
  have hLN : LN ≤ L := (le_max_left _ _).trans ((le_max_right _ _).trans hL)
  have hLW : LW ≤ L := (le_max_right _ _).trans ((le_max_right _ _).trans hL)
  have hLpos : 0 < L := lt_of_lt_of_le (by norm_num : (0:ℝ)<2) hL2
  have hδpos : 0 < δ := (Real.rpow_pos_of_pos hLpos _).trans_le hδ
  obtain ⟨BN,hmN,hpN,hfN,_,hgN⟩ := hN L hLN δ hδ hδ1 Q.links.length hn hnlog J C hS.reg
    N Agev hS.nonneg hAgev hS.norm hS.wnorm
  have hmain (j : ℕ) : ∫⁻ α, ∫⁻ lam, wL η lam*dnorm j C α lam ≤ gev N Agev j := by
    apply le_trans _ (hS.norm j)
    apply lintegral_mono
    intro α
    apply lintegral_mono
    intro lam
    exact mul_le_mul' (temporalWeight_mono (by linarith : η ≤ 1-η/8) lam) le_rfl
  obtain ⟨BW,hmW,hpW,hfW,_,hgW⟩ := hW L hLW δ hδ hδ1 Q.links.length hnlog J C hS.reg N hS.nonneg hmain
  have hrN : 0 ≤ (KN*δ/4)^Q.links.length := by positivity
  have hrW : 0 ≤ (KW*δ)^Q.links.length := by positivity
  have hiN := leafScalar_joint_integrable_and_profile_swap_of_envelope hQ hG
    (fun lam β γ' z => localRemainder L δ γ J C β γ' lam z)
    (fun z => stronglyMeasurable_localRemainder_joint hd hn L δ γ J hS.reg.meas z)
    hK hM hBi hF S hcard hη0.le hrN hmN hpN hfN hgN
  have hiW := leafScalar_joint_integrable_and_profile_swap_of_envelope hQ hG
    (fun lam β γ' z => normalizedWickCorrection L δ γ z β γ' J C lam)
    (fun z => stronglyMeasurable_normalizedWickCorrection_joint hLpos δ γ z J hS.reg.meas)
    hK hM hBi hF S hcard hη0.le hrW hmW hpW hfW hgW
  exact ⟨hiN.1 k,hiW.1 k⟩

end WaveTurbulence.RegAsymp
