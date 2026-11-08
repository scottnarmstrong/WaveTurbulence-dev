/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.FiltCoh.CoupleEnvelope
public import WaveTurbulence.Foundations.Flower.FiltCoh.WickUniform

/-! # FILT-COH (b): envelope of the whole physical scalar, uniform in the modulations

`physical_scalar_envelope_theta` (milestone (a)) with the uniform sum and Wick envelopes of `WickUniform`: the
factor `(1+2π)(1+∑‖β‖+∑‖γ'‖)` is replaced by `2`, so the bound survives any shift of the modulations (the star
characters of o82 (10.5)). -/

public section
noncomputable section
namespace WaveTurbulence.Flower.FiltCoh
open WaveTurbulence.RegAsymp MeasureTheory ClassJR ApproxNT Finset WithLp Links Incoh
open scoped ENNReal

variable {d : ℕ}

/-- **The whole physical scalar at weight `θ`, uniformly in the modulations.** -/
theorem physical_scalar_envelope_theta_u (hd : 3 ≤ d) {γ η : ℝ}
    (hγ : γ ∈ Set.Ioo (0:ℝ) 1) (hη0 : 0 < η) (hη : η ≤ 1/20)
    (hηγ : η ≤ ((d:ℝ)-1)*(1-γ))
    {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ : θ ≤ 1-η/8)
    {Agev Cbase : ℝ} (hAgev : 0 ≤ Agev) (hCbase : 1 ≤ Cbase) :
    ∃ Kr Cm : ℝ, 0 < Kr ∧ 1 ≤ Cm ∧
      ∀ Aorder : ℝ, ∃ L₀ : ℝ, ∀ L : ℝ, L₀ ≤ L →
      ∀ δ : ℝ, L^(-(η/2)) ≤ 2*δ → 2*δ ≤ 1 →
      ∀ Q : RegCpl, 0 < Q.links.length → (Q.links.length:ℝ) ≤ Real.log L^Aorder →
      ∀ C : (Z : (chosenSet Q.links).powerset) →
        ({j : Fin Q.links.length // j ∉ RA1Leafwise.markedLinkIndices Q Z.val} → ℝ) → ℝ × ℝ → ℂ,
      (∀ Z, SRep (1-η/8) (η/4) (1-η/2) Agev (Cbase^(4*Q.links.length+1)) (C Z)) →
      ∀ ζ : ℂ, ‖ζ‖ ≤ 1 →
      ∃ B : (ℝ × ℝ) → ℝ, Measurable B ∧ (∀ lam, 0 ≤ B lam) ∧
        (∫⁻ lam, wL θ lam*ENNReal.ofReal (B lam)) ≤ ENNReal.ofReal Cm^Q.links.length ∧
        ∀ᵐ lam : ℝ × ℝ, ∀ (z : (Fin Q.links.length × Fin 2) → Fin d → ℤ)
          (β γ' : Fin Q.links.length → Mom d),
          ‖physicalScalar L δ γ Q ζ C lam β γ' z‖ ≤
            (2*(Kr*δ)^Q.links.length)*B lam := by
  classical
  have hθ1 : θ ≤ 1 := by linarith
  obtain ⟨Ks,hKs,hS⟩ := physical_sum_envelope_theta_u hd hγ hη0 hη hηγ
  obtain ⟨Kw,hKw,hW⟩ := wick_correction_envelope_theta_u hd hγ hη0 hη hηγ Agev hAgev
  set Cw : ℝ := 4*(3*(1+2*coefficientGevreyMass (4*Agev)+gaussianWeightedMass θ)*Cbase^5) with hCwdef
  have hU := coefficientGevreyMass_nonneg (by positivity : 0 ≤ 4*Agev)
  have hV := gaussianWeightedMass_nonneg θ
  have hCw : 0 ≤ Cw := by
    rw [hCwdef]
    have := pow_nonneg (zero_le_one.trans hCbase) 5
    have : 0 ≤ 1+2*coefficientGevreyMass (4*Agev)+gaussianWeightedMass θ := by linarith
    positivity
  refine ⟨max Ks Kw, max 1 (4*Cw), lt_of_lt_of_le hKs (le_max_left _ _), le_max_left _ _, ?_⟩
  intro Aorder
  obtain ⟨LS,hS⟩ := hS Aorder
  obtain ⟨LW,hW⟩ := hW Aorder
  refine ⟨max 2 (max LS LW),?_⟩
  intro L hL δ hδ hδ1 Q hn hnlog C hC ζ hζ
  set n := Q.links.length with hndef
  have hL2 : 2 ≤ L := (le_max_left _ _).trans hL
  have hLS : LS ≤ L := (le_max_left _ _).trans ((le_max_right _ _).trans hL)
  have hLW : LW ≤ L := (le_max_right _ _).trans ((le_max_right _ _).trans hL)
  have hL1 : (1:ℝ) ≤ L := by linarith
  have hδpos : 0 < δ := by
    have hh := (Real.rpow_pos_of_pos (by linarith : (0:ℝ) < L) (-(η/2))).trans_le hδ
    linarith only [hh]
  have hmainθ (Z : (chosenSet Q.links).powerset) (j : ℕ) :
      ∫⁻ α, ∫⁻ lam, wL θ lam*dnorm j (C Z) α lam ≤ gev (Cbase^(4*n+1)) Agev j := by
    apply le_trans _ ((hC Z).norm j)
    apply lintegral_mono
    intro α
    apply lintegral_mono
    intro lam
    exact mul_le_mul' (temporalWeight_mono hθ lam) le_rfl
  have hwick := wickCoefficientMass_le_geometric hn hθ1 hAgev hCbase
  have hrate : ENNReal.ofReal (L^(-gamma1 d γ)) ≤ 1 := by
    rw [← ENNReal.ofReal_one]
    apply ENNReal.ofReal_le_ofReal
    apply Real.rpow_le_one_of_one_le_of_nonpos hL1
    have : 0 ≤ gamma1 d γ := by
      unfold gamma1
      have h1 : 0 ≤ 2*γ := by linarith [hγ.1]
      have h2 : (0:ℝ) ≤ 2*((d:ℝ)-1)*(1-γ) := by
        have h3 : (0:ℝ) ≤ (d:ℝ)-1 := by
          have : (3:ℝ) ≤ d := by exact_mod_cast hd
          linarith
        have h4 : 0 ≤ 1-γ := by linarith [hγ.2]
        have := mul_nonneg h3 h4
        linarith
      exact le_min h1 (le_min zero_le_one h2)
    linarith
  have hex (Z : (chosenSet Q.links).powerset) :
      ∃ BN BW : (ℝ × ℝ) → ℝ,
        Measurable BN ∧ Measurable BW ∧ (∀ lam, 0 ≤ BN lam) ∧ (∀ lam, 0 ≤ BW lam) ∧
        (∫⁻ lam, wL θ lam*ENNReal.ofReal (BN lam)) ≤ ENNReal.ofReal Cw^n ∧
        (∫⁻ lam, wL θ lam*ENNReal.ofReal (BW lam)) ≤ ENNReal.ofReal Cw^n ∧
        (∀ᵐ lam : ℝ × ℝ, ∀ (z : (Fin n × Fin 2) → Fin d → ℤ) (β γ' : Fin n → Mom d),
          ‖(((δ/(2*L^((d:ℝ)-γ)))^(2*n):ℝ):ℂ) *
            approxSum L (L^(2*γ)*(2*δ)) (halfCellAmplitude z β γ')
              (resProfile (RA1Leafwise.markedLinkIndices Q Z.val) (fun Ω => C Z (ofLp Ω) lam))‖ ≤
            2*(Ks*δ)^n*BN lam) ∧
        (∀ᵐ lam : ℝ × ℝ, ∀ (z : (Fin n × Fin 2) → Fin d → ℤ) (β γ' : Fin n → Mom d),
          ‖normalizedWickCorrection L (2*δ) γ z β γ' (RA1Leafwise.markedLinkIndices Q Z.val) (C Z) lam‖ ≤
            2*(Kw*(2*δ))^n*BW lam) := by
    have hSZ := hC Z
    obtain ⟨BN,hmN,hpN,hbN,hgN⟩ := hS L hLS δ hδ hδ1 n hnlog (RA1Leafwise.markedLinkIndices Q Z.val) (C Z)
      hSZ.reg θ _ Agev hθ0 hθ1 hSZ.nonneg hAgev (hmainθ Z)
    obtain ⟨BW,hmW,hpW,hbW,hgW⟩ := hW L hLW (2*δ) hδ hδ1 n hnlog (RA1Leafwise.markedLinkIndices Q Z.val)
      (C Z) hSZ.reg θ _ hθ0 hθ1 hSZ.nonneg (hmainθ Z)
    refine ⟨BN,BW,hmN,hmW,hpN,hpW,?_,?_,hgN,hgW⟩
    · exact hbN.trans ((sum_mass_le_wick_mass n hSZ.nonneg hAgev _).trans hwick)
    · refine hbW.trans (le_trans ?_ hwick)
      calc (4:ℝ≥0∞)^n*ENNReal.ofReal (L^(-gamma1 d γ))*_
          ≤ (4:ℝ≥0∞)^n*1*_ := by gcongr
        _ = _ := by rw [mul_one]
  choose BN BW hmN hmW hpN hpW hbN hbW hgN hgW using hex
  let B := fun lam => ∑ Z : (chosenSet Q.links).powerset, (BN Z lam+BW Z lam)
  have hmB : Measurable B := Finset.measurable_sum _ (fun Z _ => (hmN Z).add (hmW Z))
  have hpB (lam : ℝ × ℝ) : 0 ≤ B lam :=
    Finset.sum_nonneg (fun Z _ => add_nonneg (hpN Z lam) (hpW Z lam))
  have hsize : Q.size = 2*n := by
    rw [hndef]
    have hh := couple_linksAt_length Q ((0:Fin 2),[]) (1,[])
    simpa only [RegCpl.links,Nat.mul_comm] using hh.symm
  have hcard : Fintype.card ((chosenSet Q.links).powerset) = 2^n := by
    rw [Fintype.card_coe,coefficient_index_card hsize]
  have hbB : (∫⁻ lam, wL θ lam*ENNReal.ofReal (B lam)) ≤ ENNReal.ofReal (max 1 (4*Cw))^n := by
    apply (weighted_scalar_envelope_sum_le θ BN BW hmN hmW hpN hpW hbN hbW).trans
    rw [hcard,Nat.cast_pow,Nat.cast_ofNat]
    have hh := powerset_error_mass_le hn (C := Cw) 1
    simp only [one_mul] at hh
    exact hh.trans (pow_le_pow_left₀ zero_le (ENNReal.ofReal_le_ofReal (le_max_right _ _)) n)
  refine ⟨B,hmB,hpB,hbB,?_⟩
  have haN := ae_all_iff.mpr hgN
  have haW := ae_all_iff.mpr hgW
  filter_upwards [haN,haW] with lam hN hW
  intro z β γ'
  have hH : (0:ℝ) ≤ 2 := by norm_num
  set K := max Ks Kw
  have hKs : (Ks*δ)^n ≤ (K*δ)^n :=
    pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_right (le_max_left _ _) hδpos.le) n
  have hKw : ((4:ℝ)^n)⁻¹*(Kw*(2*δ))^n ≤ (K*δ)^n := by
    rw [← inv_pow, ← mul_pow]
    apply pow_le_pow_left₀ (by positivity)
    have : Kw ≤ K := le_max_right _ _
    nlinarith [hKw.le, hδpos.le]
  have hZ (Z : (chosenSet Q.links).powerset) :
      ‖physicalWeightedCellSymbol L δ γ z β γ' (RA1Leafwise.markedLinkIndices Q Z.val) (C Z) lam‖ ≤
        2*(K*δ)^n*(BN Z lam+BW Z lam) := by
    rw [physicalWeightedCellSymbol_eq_sum_add_wick (by linarith : (0:ℝ) < L)]
    refine (norm_add_le _ _).trans ?_
    have hw' : ∀ w : ℂ, ‖((4:ℂ)^n)⁻¹ * w‖ = ((4:ℝ)^n)⁻¹ * ‖w‖ := fun w => by
      rw [norm_mul, norm_inv, norm_pow]; norm_num
    rw [hw']
    have h1 := hN Z z β γ'
    have h2 := hW Z z β γ'
    have hw : ((4:ℝ)^n)⁻¹*‖normalizedWickCorrection L (2*δ) γ z β γ'
        (RA1Leafwise.markedLinkIndices Q Z.val) (C Z) lam‖ ≤ 2*(K*δ)^n*BW Z lam := by
      calc _ ≤ ((4:ℝ)^n)⁻¹*(2*(Kw*(2*δ))^n*BW Z lam) :=
            mul_le_mul_of_nonneg_left h2 (by positivity)
        _ = 2*(((4:ℝ)^n)⁻¹*(Kw*(2*δ))^n)*BW Z lam := by ring
        _ ≤ 2*(K*δ)^n*BW Z lam :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hKw hH) (hpW Z lam)
    have hs : ‖(((δ/(2*L^((d:ℝ)-γ)))^(2*n):ℝ):ℂ) *
        approxSum L (L^(2*γ)*(2*δ)) (halfCellAmplitude z β γ')
          (resProfile (RA1Leafwise.markedLinkIndices Q Z.val) (fun Ω => C Z (ofLp Ω) lam))‖ ≤
        2*(K*δ)^n*BN Z lam :=
      h1.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hKs hH) (hpN Z lam))
    calc _ ≤ 2*(K*δ)^n*BN Z lam + 2*(K*δ)^n*BW Z lam := add_le_add hs hw
      _ = _ := by ring
  unfold physicalScalar
  rw [norm_mul]
  apply (mul_le_mul_of_nonneg_right hζ (norm_nonneg _)).trans
  rw [one_mul]
  apply (norm_sum_le _ _).trans
  have hB : ((2*(K*δ)^n))*B lam = ∑ Z : (chosenSet Q.links).powerset, 2*(K*δ)^n*(BN Z lam+BW Z lam) := by
    simp only [B, Finset.mul_sum]
  rw [hB]
  apply Finset.sum_le_sum
  intro Z _
  rw [norm_mul]
  calc _ ≤ 1*‖physicalWeightedCellSymbol L δ γ z β γ' (RA1Leafwise.markedLinkIndices Q Z.val) (C Z) lam‖ :=
        mul_le_mul_of_nonneg_right (RA1Leafwise.norm_original_source_weight_le_one Z.val) (norm_nonneg _)
    _ ≤ _ := by rw [one_mul]; exact hZ Z

end WaveTurbulence.Flower.FiltCoh
