/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.FiltCoh.CoupleEnvelopeU
public import WaveTurbulence.Foundations.Spine.RA1LW.LeafScalarProfile

/-! # FILT-COH (b): one physical cell symbol, uniformly in the modulations; integrable leaf densities

* `physical_symbol_envelope_u`: the per-coefficient part of `physical_scalar_envelope_theta_u`.
* `integrable_density_of_env`: an envelope `‖R λ β γ' z‖ ≤ r B λ` (uniform in the modulations) makes the masked
  leaf density jointly integrable (main's leaf mass lemmas). -/

public section
noncomputable section
namespace WaveTurbulence.Flower.FiltCoh
open WaveTurbulence.RegAsymp MeasureTheory ClassJR ApproxNT Finset WithLp Links Incoh
open scoped ENNReal

variable {d : ℕ}

/-- **One physical cell symbol at weight `θ`, uniformly in the modulations.** -/
theorem physical_symbol_envelope_u (hd : 3 ≤ d) {γ η : ℝ}
    (hγ : γ ∈ Set.Ioo (0:ℝ) 1) (hη0 : 0 < η) (hη : η ≤ 1/20)
    (hηγ : η ≤ ((d:ℝ)-1)*(1-γ))
    {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ : θ ≤ 1-η/8)
    {Agev Cbase : ℝ} (hAgev : 0 ≤ Agev) (hCbase : 1 ≤ Cbase) :
    ∃ K Cm : ℝ, 0 < K ∧ 1 ≤ Cm ∧
      ∀ Aorder : ℝ, ∃ L₀ : ℝ, ∀ L : ℝ, L₀ ≤ L →
      ∀ δ : ℝ, L^(-(η/2)) ≤ 2*δ → 2*δ ≤ 1 →
      ∀ n : ℕ, 0 < n → (n:ℝ) ≤ Real.log L^Aorder →
      ∀ (J : Finset (Fin n)) (C : ({j : Fin n // j ∉ J} → ℝ) → ℝ × ℝ → ℂ),
      SRep (1-η/8) (η/4) (1-η/2) Agev (Cbase^(4*n+1)) C →
      ∃ B : (ℝ × ℝ) → ℝ, Measurable B ∧ (∀ lam, 0 ≤ B lam) ∧
        (∫⁻ lam, wL θ lam*ENNReal.ofReal (B lam)) ≤ ENNReal.ofReal Cm^n ∧
        ∀ᵐ lam : ℝ × ℝ, ∀ (z : (Fin n × Fin 2) → Fin d → ℤ) (β γ' : Fin n → Mom d),
          ‖physicalWeightedCellSymbol L δ γ z β γ' J C lam‖ ≤ 2*(K*δ)^n*B lam := by
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
  refine ⟨max Ks Kw, max 1 (2*Cw), lt_of_lt_of_le hKs (le_max_left _ _), le_max_left _ _, ?_⟩
  intro Aorder
  obtain ⟨LS,hS⟩ := hS Aorder
  obtain ⟨LW,hW⟩ := hW Aorder
  refine ⟨max 2 (max LS LW),?_⟩
  intro L hL δ hδ hδ1 n hn hnlog J C hC
  have hLS : LS ≤ L := (le_max_left _ _).trans ((le_max_right _ _).trans hL)
  have hLW : LW ≤ L := (le_max_right _ _).trans ((le_max_right _ _).trans hL)
  have hL1 : (1:ℝ) ≤ L := by linarith [(le_max_left 2 (max LS LW)).trans hL]
  have hδpos : 0 < δ := by
    have hh := (Real.rpow_pos_of_pos (by linarith : (0:ℝ) < L) (-(η/2))).trans_le hδ
    linarith only [hh]
  have hmainθ (j : ℕ) :
      ∫⁻ α, ∫⁻ lam, wL θ lam*dnorm j C α lam ≤ gev (Cbase^(4*n+1)) Agev j := by
    apply le_trans _ (hC.norm j)
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
  obtain ⟨BN,hmN,hpN,hbN,hgN⟩ := hS L hLS δ hδ hδ1 n hnlog J C hC.reg θ _ Agev hθ0 hθ1 hC.nonneg hAgev hmainθ
  obtain ⟨BW,hmW,hpW,hbW,hgW⟩ := hW L hLW (2*δ) hδ hδ1 n hnlog J C hC.reg θ _ hθ0 hθ1 hC.nonneg hmainθ
  have hbN' : (∫⁻ lam, wL θ lam*ENNReal.ofReal (BN lam)) ≤ ENNReal.ofReal Cw^n :=
    hbN.trans ((sum_mass_le_wick_mass n hC.nonneg hAgev _).trans hwick)
  have hbW' : (∫⁻ lam, wL θ lam*ENNReal.ofReal (BW lam)) ≤ ENNReal.ofReal Cw^n := by
    refine hbW.trans (le_trans ?_ hwick)
    calc (4:ℝ≥0∞)^n*ENNReal.ofReal (L^(-gamma1 d γ))*_
        ≤ (4:ℝ≥0∞)^n*1*_ := by gcongr
      _ = _ := by rw [mul_one]
  refine ⟨fun lam => BN lam + BW lam, hmN.add hmW, fun lam => add_nonneg (hpN lam) (hpW lam), ?_, ?_⟩
  · have hsplit : (∫⁻ lam, wL θ lam*ENNReal.ofReal (BN lam + BW lam)) =
        (∫⁻ lam, wL θ lam*ENNReal.ofReal (BN lam)) + ∫⁻ lam, wL θ lam*ENNReal.ofReal (BW lam) := by
      have hm1 : Measurable (fun lam => wL θ lam * ENNReal.ofReal (BN lam)) :=
        (measurable_wL θ).mul (ENNReal.measurable_ofReal.comp hmN)
      rw [← lintegral_add_left hm1]
      refine lintegral_congr fun lam => ?_
      rw [ENNReal.ofReal_add (hpN lam) (hpW lam), mul_add]
    rw [hsplit]
    calc _ ≤ ENNReal.ofReal Cw^n + ENNReal.ofReal Cw^n := add_le_add hbN' hbW'
      _ ≤ ENNReal.ofReal (max 1 (2*Cw))^n := by
        have h2 : (2:ℝ≥0∞) ≤ 2^n := by
          calc (2:ℝ≥0∞) = 2^1 := by norm_num
            _ ≤ 2^n := pow_le_pow_right₀ (by norm_num) hn
        calc ENNReal.ofReal Cw^n + ENNReal.ofReal Cw^n = 2*ENNReal.ofReal Cw^n := by ring
          _ ≤ 2^n*ENNReal.ofReal Cw^n := by gcongr
          _ = ENNReal.ofReal (2*Cw)^n := by
              rw [ENNReal.ofReal_mul (q := Cw) (by norm_num : (0:ℝ) ≤ 2), mul_pow, ENNReal.ofReal_ofNat]
          _ ≤ _ := pow_le_pow_left₀ zero_le (ENNReal.ofReal_le_ofReal (le_max_right _ _)) n
  · filter_upwards [hgN,hgW] with lam hN hW
    intro z β γ'
    set K := max Ks Kw
    have hKs : (Ks*δ)^n ≤ (K*δ)^n :=
      pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_right (le_max_left _ _) hδpos.le) n
    have hKw : ((4:ℝ)^n)⁻¹*(Kw*(2*δ))^n ≤ (K*δ)^n := by
      rw [← inv_pow, ← mul_pow]
      apply pow_le_pow_left₀ (by positivity)
      have : Kw ≤ K := le_max_right _ _
      nlinarith [hKw.le, hδpos.le]
    rw [physicalWeightedCellSymbol_eq_sum_add_wick (by linarith : (0:ℝ) < L)]
    refine (norm_add_le _ _).trans ?_
    have hw' : ∀ w : ℂ, ‖((4:ℂ)^n)⁻¹ * w‖ = ((4:ℝ)^n)⁻¹ * ‖w‖ := fun w => by
      rw [norm_mul, norm_inv, norm_pow]; norm_num
    rw [hw']
    have h1 := hN z β γ'
    have h2 := hW z β γ'
    have hw : ((4:ℝ)^n)⁻¹*‖normalizedWickCorrection L (2*δ) γ z β γ' J C lam‖ ≤ 2*(K*δ)^n*BW lam := by
      calc _ ≤ ((4:ℝ)^n)⁻¹*(2*(Kw*(2*δ))^n*BW lam) :=
            mul_le_mul_of_nonneg_left h2 (by positivity)
        _ = 2*(((4:ℝ)^n)⁻¹*(Kw*(2*δ))^n)*BW lam := by ring
        _ ≤ 2*(K*δ)^n*BW lam :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hKw (by norm_num)) (hpW lam)
    have hs := h1.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hKs (by norm_num)) (hpN lam))
    calc _ ≤ 2*(K*δ)^n*BN lam + 2*(K*δ)^n*BW lam := add_le_add hs hw
      _ = _ := by ring

/-- **Integrable leaf densities** from an envelope uniform in the modulations. -/
theorem integrable_density_of_env {G : Garden 2} {Q : RegCpl} (hQ : Q.Decodes G) (hG : IsCouple G)
    {K M : ℕ} (R : (ℝ × ℝ) → (Fin Q.links.length → Mom d) →
      (Fin Q.links.length → Mom d) → ((Fin Q.links.length × Fin 2) → Fin d → ℤ) → ℂ)
    (hR : ∀ z, StronglyMeasurable (fun p : (ℝ × ℝ) ×
      ((Fin Q.links.length → Mom d) × (Fin Q.links.length → Mom d)) => R p.1 p.2.1 p.2.2 z))
    {F : Fin (2*Q.links.length+1) → Mom d → ℂ} {Binput Ccover : ℝ} (hK : d+2 ≤ K) (hM : 2*d ≤ M)
    (hBi : 0 ≤ Binput) (hF : ∀ a, Fourier.spatialNorm K M (F a) ≤ ENNReal.ofReal Binput)
    (S : (Fin (2*Q.links.length+1) → Fin d → ℤ) → Finset ((Fin Q.links.length × Fin 2) → Fin d → ℤ))
    (hcard : ∀ c, ((S c).card:ℝ) ≤ Ccover^Q.links.length)
    {θ : ℝ} (hθ : 0 ≤ θ) {r : ℝ} (hr : 0 ≤ r) {B : (ℝ × ℝ) → ℝ} (hB : Measurable B)
    (hBn : ∀ lam, 0 ≤ B lam) (hBfin : (∫⁻ lam, wL θ lam * ENNReal.ofReal (B lam)) < ⊤)
    (hb : ∀ᵐ lam : ℝ × ℝ, ∀ z β γ', ‖R lam β γ' z‖ ≤ r*B lam) (k : Mom d) :
    Integrable (fun q => RA1Leafwise.maskedLeafScalarDensity hQ hG R F S q k)
      (volume.prod (RA1Leafwise.leafSpatialMeasure d Q.links.length (2*Q.links.length+1))) := by
  let μ := RA1Leafwise.leafSpatialMeasure d Q.links.length (2*Q.links.length+1)
  let : SFinite μ := by
    unfold μ RA1Leafwise.leafSpatialMeasure
    infer_instance
  have hb' : ∀ᵐ lam : ℝ × ℝ, ∀ z β γ', ‖R lam β γ' z‖ ≤
      ((1+2*Real.pi)*(1+((∑ i, ‖β i‖)+(∑ i, ‖γ' i‖)))*r)*B lam := by
    filter_upwards [hb] with lam h z β γ'
    refine (h z β γ').trans (mul_le_mul_of_nonneg_right ?_ (hBn lam))
    have h1 : 1 ≤ (1+2*Real.pi)*(1+((∑ i, ‖β i‖)+(∑ i, ‖γ' i‖))) := by
      have : 0 ≤ (∑ i, ‖β i‖)+(∑ i, ‖γ' i‖) := by positivity
      nlinarith [Real.pi_pos]
    nlinarith
  let v := RA1Leafwise.leafScalarDerivativeEnvelope hQ hG 0 0 R F S
  have hvm : Measurable v :=
    RA1Leafwise.measurable_leafScalarDerivativeEnvelope hQ hG 0 0 R F S hR (by omega) hBi hF
  have hvn : ∀ q, 0 ≤ v q := RA1Leafwise.leafScalarDerivativeEnvelope_nonneg hQ hG 0 0 R F S
  have hmass := RA1Leafwise.weighted_mass_leafScalarDerivativeEnvelope_le hQ hG 0 0 R F S
    hR (by omega) hBi hF θ hr B hB hBn hb'
  have hleaf := RA1Leafwise.lintegral_leafSpatialHigherEnvelope_le (0+1) 0 (by omega) (by omega) hBi hF S hcard
  have hfin : (∫⁻ q, wL θ q.1 * ENNReal.ofReal (v q) ∂volume.prod μ) < ⊤ :=
    hmass.trans_lt (ENNReal.mul_lt_top
      (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hBfin)
      (hleaf.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (by finiteness))))
  have hv : Integrable v (volume.prod μ) := integrable_of_weighted_lintegral_lt_top μ hθ v hvm hvn hfin
  have ha : StronglyMeasurable (RA1Leafwise.leafScalarAmplitude hQ hG R F S) :=
    RA1Leafwise.stronglyMeasurable_leafScalarAmplitude hQ hG R hR (by omega) hBi hF S
  have hc : Measurable (fun q : (ℝ × ℝ) ×
      RA1Leafwise.LeafSpatialSample d Q.links.length (2*Q.links.length+1) => q.2.1.1) :=
    measurable_snd.fst.fst
  have hvfreq : StronglyMeasurable (fun q : (ℝ × ℝ) ×
      RA1Leafwise.LeafSpatialSample d Q.links.length (2*Q.links.length+1) => ∑ a, toLp 2 (q.2.2 a)) := by
    have hc' : Continuous (fun α : Fin (2*Q.links.length+1) → Fin d → ℝ => ∑ a, toLp 2 (α a)) := by fun_prop
    exact hc'.stronglyMeasurable.comp_measurable measurable_snd.snd
  have hsm : StronglyMeasurable (fun q : (ℝ × ℝ) ×
      RA1Leafwise.LeafSpatialSample d Q.links.length (2*Q.links.length+1) =>
      RA1Leafwise.maskedLeafScalarDensity hQ hG R F S q k) := by
    have hmask : Measurable (fun c : Fin (2*Q.links.length+1) → Fin d → ℤ => sourceRootMask c k) :=
      measurable_of_countable _
    have hchar : Continuous (fun v : Mom d => (Real.fourierChar (inner ℝ v k):ℂ)) := by fun_prop
    exact (hmask.stronglyMeasurable.comp_measurable hc).mul
      (ha.mul (hchar.stronglyMeasurable.comp_measurable hvfreq.measurable))
  refine hv.mono' hsm.aestronglyMeasurable (ae_of_all _ fun q => ?_)
  have h0 := RA1Leafwise.weighted_derivative_maskedLeafScalarDensity_le hQ hG 0 0 R F S
    (j := 0) le_rfl q k
  rw [pow_zero, one_mul, norm_iteratedFDeriv_zero] at h0
  exact h0

end WaveTurbulence.Flower.FiltCoh
