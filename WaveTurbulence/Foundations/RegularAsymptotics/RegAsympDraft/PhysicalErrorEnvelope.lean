/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.RegularAsymptotics.RegAsympDraft.PhysicalErrorScalarBound
public import WaveTurbulence.Foundations.RegularAsymptotics.RegAsympDraft.ScalarEnvelopeSum
public import WaveTurbulence.Foundations.RegularAsymptotics.RegAsympDraft.ExpansionCardinality

/-! # Original source premises give one geometric physical error envelope -/

public section
noncomputable section
namespace WaveTurbulence.RegAsymp
open MeasureTheory Links Incoh ClassJR ApproxNT
open scoped ENNReal

/-- The combined original physical scalar error admits a common envelope
whose rate and constants are uniform before the logarithmic order exponent. -/
theorem physical_error_scalar_envelope {d : ℕ} (hd : 3 ≤ d) {γ η : ℝ}
    (hγ : γ ∈ Set.Ioo (0:ℝ) 1) (hη0 : 0 < η) (hη : η ≤ 1/20)
    (hηγ : η ≤ ((d:ℝ)-1)*(1-γ)) (hηγ' : η ≤ γ)
    {Agev Cbase : ℝ} (hAgev : 0 ≤ Agev) (hCbase : 1 ≤ Cbase) :
    ∃ Kr Cm : ℝ, 0 < Kr ∧ 1 ≤ Cm ∧
      ∀ Aorder : ℝ, ∃ L₀ : ℝ, ∀ L : ℝ, L₀ ≤ L →
      ∀ δ : ℝ, L^(-(η/2)) ≤ 2*δ → 2*δ ≤ 1 →
      ∀ Q : RegCpl, 0 < Q.links.length → (Q.links.length:ℝ) ≤ Real.log L^Aorder →
      ∀ C : (Z : (chosenSet Q.links).powerset) →
        ({j : Fin Q.links.length // j ∉ markedLinkIndices Q Z.val} → ℝ) → ℝ × ℝ → ℂ,
      (∀ Z, SRep (1-η/8) (η/4) (1-η/2) Agev (Cbase^(4*Q.links.length+1)) (C Z)) →
      ∀ ζ : ℂ, ‖ζ‖ ≤ 1 →
      ∃ B : (ℝ × ℝ) → ℝ, Measurable B ∧ (∀ lam, 0 ≤ B lam) ∧
        (∫⁻ lam, wL η lam*ENNReal.ofReal (B lam)) < ⊤ ∧
        (∫⁻ lam, wL η lam*ENNReal.ofReal (B lam)) ≤
          ENNReal.ofReal (L^(-gamma1 d γ+2*η))*ENNReal.ofReal Cm^Q.links.length ∧
        ∀ᵐ lam : ℝ × ℝ, ∀ (z : (Fin Q.links.length × Fin 2) → Fin d → ℤ) (β γ' : Fin Q.links.length → Mom d),
          ‖physicalErrorScalar L δ γ Q ζ C lam β γ' z‖ ≤
            ((1+2*Real.pi)*(1+((∑ j, ‖β j‖)+(∑ j, ‖γ' j‖)))*(Kr*δ)^Q.links.length)*B lam := by
  classical
  obtain ⟨KN,hKN,hNT⟩ := local_symbol_remainder_envelope hd hγ hη0 hη hηγ hηγ'
  obtain ⟨KW,hKW,hWK⟩ := wick_correction_scalar_envelope hd hγ hη0 hη hηγ hηγ' Agev hAgev
  obtain ⟨Cm,hCm,hMass⟩ := exists_common_errorCoefficientMass_bound hη0.le (by linarith) hAgev hCbase
  refine ⟨max KN (2*KW),4*Cm,lt_of_lt_of_le hKN (le_max_left _ _),by linarith,?_⟩
  intro Aorder
  obtain ⟨LN,hNT⟩ := hNT Aorder
  obtain ⟨LW,hWK⟩ := hWK Aorder
  refine ⟨max 2 (max LN LW),?_⟩
  intro L hL δ hδ hδ1 Q hn hnlog C hC ζ hζ
  have hLN : LN ≤ L := (le_max_left _ _).trans ((le_max_right _ _).trans hL)
  have hLW : LW ≤ L := (le_max_right _ _).trans ((le_max_right _ _).trans hL)
  have hL2 : 2 ≤ L := (le_max_left _ _).trans hL
  have hLpos : 0 < L := lt_of_lt_of_le (by norm_num : (0:ℝ)<2) hL2
  have hδpos : 0 < δ := by
    have hh := (Real.rpow_pos_of_pos hLpos (-(η/2))).trans_le hδ
    linarith only [hh]
  have hrate : ENNReal.ofReal (L^(-gamma1 d γ)) ≤ ENNReal.ofReal (L^(-gamma1 d γ+2*η)) :=
    ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow_of_exponent_le (by linarith : 1 ≤ L) (by linarith))
  have hex (Z : (chosenSet Q.links).powerset) :
      ∃ BN BW : (ℝ × ℝ) → ℝ,
        Measurable BN ∧ Measurable BW ∧ (∀ lam, 0 ≤ BN lam) ∧ (∀ lam, 0 ≤ BW lam) ∧
        (∫⁻ lam, wL η lam*ENNReal.ofReal (BN lam)) ≤
          ENNReal.ofReal (L^(-gamma1 d γ+2*η))*ENNReal.ofReal Cm^Q.links.length ∧
        (∫⁻ lam, wL η lam*ENNReal.ofReal (BW lam)) ≤
          ENNReal.ofReal (L^(-gamma1 d γ+2*η))*ENNReal.ofReal Cm^Q.links.length ∧
        (∀ᵐ lam : ℝ × ℝ, ∀ (z : (Fin Q.links.length × Fin 2) → Fin d → ℤ)
          (β γ' : Fin Q.links.length → Mom d),
          ‖localRemainder L (2*δ) γ (markedLinkIndices Q Z.val) (C Z) β γ' lam z‖ ≤
            ((1+2*Real.pi)*(1+((∑ j, ‖β j‖)+(∑ j, ‖γ' j‖)))*(KN*(2*δ)/4)^Q.links.length)*BN lam) ∧
        (∀ᵐ lam : ℝ × ℝ, ∀ (z : (Fin Q.links.length × Fin 2) → Fin d → ℤ)
          (β γ' : Fin Q.links.length → Mom d),
          ‖normalizedWickCorrection L (2*δ) γ z β γ' (markedLinkIndices Q Z.val) (C Z) lam‖ ≤
            ((1+2*Real.pi)*(1+((∑ j, ‖β j‖)+(∑ j, ‖γ' j‖)))*(KW*(2*δ))^Q.links.length)*BW lam) := by
    have hS := hC Z
    obtain ⟨BN,hmN,hpN,_hfN,hbN,hgN⟩ := hNT L hLN (2*δ) hδ hδ1 Q.links.length hn hnlog
      (markedLinkIndices Q Z.val) (C Z) hS.reg _ Agev hS.nonneg hAgev hS.norm hS.wnorm
    have hmain (j : ℕ) : ∫⁻ α, ∫⁻ lam, wL η lam*dnorm j (C Z) α lam ≤
        gev (Cbase^(4*Q.links.length+1)) Agev j := by
      apply le_trans _ (hS.norm j)
      apply lintegral_mono
      intro α
      apply lintegral_mono
      intro lam
      exact mul_le_mul' (temporalWeight_mono (by linarith : η ≤ 1-η/8) lam) le_rfl
    obtain ⟨BW,hmW,hpW,_hfW,hbW,hgW⟩ := hWK L hLW (2*δ) hδ hδ1 Q.links.length hnlog
      (markedLinkIndices Q Z.val) (C Z) hS.reg _ hS.nonneg hmain
    have hbN' : (∫⁻ lam, wL η lam*ENNReal.ofReal (BN lam)) ≤
        ENNReal.ofReal (L^(-gamma1 d γ+2*η))*ENNReal.ofReal Cm^Q.links.length := by
      apply hbN.trans
      exact mul_le_mul' le_rfl (hMass Q.links.length hn (markedLinkIndices Q Z.val)).1
    have hbW' : (∫⁻ lam, wL η lam*ENNReal.ofReal (BW lam)) ≤
        ENNReal.ofReal (L^(-gamma1 d γ+2*η))*ENNReal.ofReal Cm^Q.links.length := by
      apply hbW.trans
      calc
        _ = ENNReal.ofReal (L^(-gamma1 d γ))*((4:ℝ≥0∞)^Q.links.length*
            ((ENNReal.ofReal (Cbase^(4*Q.links.length+1))*∑' j : ℕ,
              ENNReal.ofReal ((4*Agev)^j*((2*j).factorial:ℝ)/(4*j).factorial)) +
              (∫⁻ lam, wL η lam*ENNReal.ofReal (frequencyGaussian lam)))) := by ring
        _ ≤ _ := mul_le_mul' hrate (hMass Q.links.length hn (markedLinkIndices Q Z.val)).2
    exact ⟨BN,BW,hmN,hmW,hpN,hpW,hbN',hbW',hgN,hgW⟩
  choose BN BW hmN hmW hpN hpW hbN hbW hgN hgW using hex
  let B := fun lam => ∑ Z : (chosenSet Q.links).powerset, (BN Z lam+BW Z lam)
  have hmB : Measurable B := Finset.measurable_sum _ (fun Z _ => (hmN Z).add (hmW Z))
  have hpB (lam : ℝ × ℝ) : 0 ≤ B lam := Finset.sum_nonneg (fun Z _ => add_nonneg (hpN Z lam) (hpW Z lam))
  have hsize : Q.size = 2*Q.links.length := by
    have hh := couple_linksAt_length Q ((0:Fin 2),[]) (1,[])
    simpa only [RegCpl.links,Nat.mul_comm] using hh.symm
  have hcard : Fintype.card ((chosenSet Q.links).powerset) = 2^Q.links.length := by
    rw [Fintype.card_coe,coefficient_index_card hsize]
  have hbB : (∫⁻ lam, wL η lam*ENNReal.ofReal (B lam)) ≤
      ENNReal.ofReal (L^(-gamma1 d γ+2*η))*ENNReal.ofReal (4*Cm)^Q.links.length := by
    apply (weighted_scalar_envelope_sum_le η BN BW hmN hmW hpN hpW hbN hbW).trans
    rw [hcard,Nat.cast_pow,Nat.cast_ofNat]
    exact powerset_error_mass_le hn _
  refine ⟨B,hmB,hpB,hbB.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (by finiteness)),hbB,?_⟩
  have haN : ∀ᵐ lam, ∀ Z : (chosenSet Q.links).powerset, ∀ (z : (Fin Q.links.length × Fin 2) → Fin d → ℤ) (β γ' : Fin Q.links.length → Mom d),
      ‖localRemainder L (2*δ) γ (markedLinkIndices Q Z.val) (C Z) β γ' lam z‖ ≤
        ((1+2*Real.pi)*(1+((∑ j, ‖β j‖)+(∑ j, ‖γ' j‖)))*(KN*(2*δ)/4)^Q.links.length)*BN Z lam :=
    ae_all_iff.mpr hgN
  have haW : ∀ᵐ lam, ∀ Z : (chosenSet Q.links).powerset, ∀ (z : (Fin Q.links.length × Fin 2) → Fin d → ℤ) (β γ' : Fin Q.links.length → Mom d),
      ‖normalizedWickCorrection L (2*δ) γ z β γ' (markedLinkIndices Q Z.val) (C Z) lam‖ ≤
        ((1+2*Real.pi)*(1+((∑ j, ‖β j‖)+(∑ j, ‖γ' j‖)))*(KW*(2*δ))^Q.links.length)*BW Z lam :=
    ae_all_iff.mpr hgW
  filter_upwards [haN,haW] with lam hN hW
  intro z β γ'
  apply norm_physicalErrorScalar_le L δ γ Q ζ hζ C lam β γ' z
    (pow_le_pow_left₀ (by positivity) ?_ Q.links.length)
    (pow_le_pow_left₀ (by positivity) ?_ Q.links.length)
    (fun Z => BN Z lam) (fun Z => BW Z lam) (fun Z => hpN Z lam) (fun Z => hpW Z lam)
    (fun Z => hN Z z β γ') (fun Z => hW Z z β γ')
  · have hh := mul_le_mul_of_nonneg_right (le_max_left KN (2*KW)) hδpos.le
    linarith only [hh,mul_pos hKN hδpos]
  · have hh := mul_le_mul_of_nonneg_right (le_max_right KN (2*KW)) hδpos.le
    linarith only [hh]

end WaveTurbulence.RegAsymp
