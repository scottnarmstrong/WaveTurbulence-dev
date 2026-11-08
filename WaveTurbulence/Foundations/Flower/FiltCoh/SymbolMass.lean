/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.FiltCoh.CoupleEnvelope
public import WaveTurbulence.Foundations.Spine.RA1LW.TreeWickRemainderIdentity

/-! # FILT-COH: one physical cell symbol at weight `θ`, and its tree form

`physical_symbol_envelope_theta` is the single-coefficient envelope (geometric mass, no `L` loss). The tree kernel
identity of main (`RA1Leafwise.KTstar_classified_leaf_profile_mixtures`) carries the symbol as
`N(δ) · treeProfileArrayScalar` (`physicalWeightedCellSymbol_eq_tree`). -/

public section
noncomputable section
namespace WaveTurbulence.Flower.FiltCoh
open WaveTurbulence.RegAsymp MeasureTheory ClassJR ApproxNT Finset WithLp Links Incoh
open scoped ENNReal

variable {d : ℕ}

/-- The tree scalar with the physical normalization is the physical cell symbol. -/
theorem physicalWeightedCellSymbol_eq_tree {n : ℕ} {L : ℝ} (hL : 0 < L) (δ γ : ℝ)
    (J : Finset (Fin n)) (C : ({j : Fin n // j ∉ J} → ℝ) → ℝ × ℝ → ℂ)
    (z : (Fin n × Fin 2) → Fin d → ℤ) (β γ' : Fin n → Mom d) (lam : ℝ × ℝ) :
    physicalWeightedCellSymbol L δ γ z β γ' J C lam =
      (((δ/(2*L^((d:ℝ)-γ)))^(2*n):ℝ):ℂ) *
        treeProfileArrayScalar L (2*δ*L^(2*γ)) RA1Leafwise.treeWickArrayWeight z β γ' J C lam := by
  have hs := RA1Leafwise.tree_normalized_profile_eq_remainders_add_leading hL (2*δ) γ J C z β γ' lam
  have harg : L^(2*γ)*(2*δ) = 2*δ*L^(2*γ) := by ring
  rw [harg, doubled_coupling_prefactor] at hs
  rw [physicalWeightedCellSymbol_decomposition hL]
  unfold localRemainder at hs ⊢
  rw [doubled_coupling_prefactor] at hs ⊢
  have h4 : (4:ℂ)^n ≠ 0 := pow_ne_zero _ (by norm_num)
  have hq : (((δ/(2*L^((d:ℝ)-γ)))^(2*n):ℝ):ℂ) *
      treeProfileArrayScalar L (2*δ*L^(2*γ)) RA1Leafwise.treeWickArrayWeight z β γ' J C lam =
      ((4:ℂ)^n)⁻¹ * ((4:ℂ)^n * (((δ/(2*L^((d:ℝ)-γ)))^(2*n):ℝ):ℂ) *
        treeProfileArrayScalar L (2*δ*L^(2*γ)) RA1Leafwise.treeWickArrayWeight z β γ' J C lam) := by
    field_simp
  rw [hq, hs]
  field_simp
  ring

/-- **One physical cell symbol at weight `θ ≤ 1 - η/8`**: an envelope of mass at most `2 Cw^n`. -/
theorem physical_symbol_envelope_theta (hd : 3 ≤ d) {γ η : ℝ}
    (hγ : γ ∈ Set.Ioo (0:ℝ) 1) (hη0 : 0 < η) (hη : η ≤ 1/20)
    (hηγ : η ≤ ((d:ℝ)-1)*(1-γ)) (hηγ' : η ≤ γ)
    {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ : θ ≤ 1-η/8)
    {Agev Cbase : ℝ} (hAgev : 0 ≤ Agev) (hCbase : 1 ≤ Cbase) :
    ∃ Kr Cw : ℝ, 0 < Kr ∧ 0 ≤ Cw ∧
      ∀ Aorder : ℝ, ∃ L₀ : ℝ, ∀ L : ℝ, L₀ ≤ L →
      ∀ δ : ℝ, L^(-(η/2)) ≤ 2*δ → 2*δ ≤ 1 →
      ∀ n : ℕ, 0 < n → (n:ℝ) ≤ Real.log L^Aorder →
      ∀ (J : Finset (Fin n)) (C : ({j : Fin n // j ∉ J} → ℝ) → ℝ × ℝ → ℂ),
      SRep (1-η/8) (η/4) (1-η/2) Agev (Cbase^(4*n+1)) C →
      ∃ B : (ℝ × ℝ) → ℝ, Measurable B ∧ (∀ lam, 0 ≤ B lam) ∧
        (∫⁻ lam, wL θ lam*ENNReal.ofReal (B lam)) ≤ 2*ENNReal.ofReal Cw^n ∧
        ∀ᵐ lam : ℝ × ℝ, ∀ (z : (Fin n × Fin 2) → Fin d → ℤ) (β γ' : Fin n → Mom d),
          ‖physicalWeightedCellSymbol L δ γ z β γ' J C lam‖ ≤
            (1+2*Real.pi)*(1+((∑ j, ‖β j‖)+(∑ j, ‖γ' j‖)))*(Kr*δ)^n*B lam := by
  classical
  have hθ1 : θ ≤ 1 := by linarith
  obtain ⟨Ks,hKs,hS⟩ := physical_sum_envelope_theta hd hγ hη0 hη hηγ hηγ'
  obtain ⟨Kw,hKw,hW⟩ := wick_correction_envelope_theta hd hγ hη0 hη hηγ hηγ' Agev hAgev
  set Cw : ℝ := 4*(3*(1+2*coefficientGevreyMass (4*Agev)+gaussianWeightedMass θ)*Cbase^5) with hCwdef
  have hU := coefficientGevreyMass_nonneg (by positivity : 0 ≤ 4*Agev)
  have hV := gaussianWeightedMass_nonneg θ
  have hCw : 0 ≤ Cw := by
    rw [hCwdef]
    have := pow_nonneg (zero_le_one.trans hCbase) 5
    have : 0 ≤ 1+2*coefficientGevreyMass (4*Agev)+gaussianWeightedMass θ := by linarith
    positivity
  refine ⟨max Ks Kw, Cw, lt_of_lt_of_le hKs (le_max_left _ _), hCw, ?_⟩
  intro Aorder
  obtain ⟨LS,hS⟩ := hS Aorder
  obtain ⟨LW,hW⟩ := hW Aorder
  refine ⟨max 2 (max LS LW),?_⟩
  intro L hL δ hδ hδ1 n hn hnlog J C hC
  have hL2 : 2 ≤ L := (le_max_left _ _).trans hL
  have hLS : LS ≤ L := (le_max_left _ _).trans ((le_max_right _ _).trans hL)
  have hLW : LW ≤ L := (le_max_right _ _).trans ((le_max_right _ _).trans hL)
  have hL1 : (1:ℝ) ≤ L := by linarith
  have hδpos : 0 < δ := by
    have hh := (Real.rpow_pos_of_pos (by linarith : (0:ℝ) < L) (-(η/2))).trans_le hδ
    linarith only [hh]
  have hmainθ (j : ℕ) : ∫⁻ α, ∫⁻ lam, wL θ lam*dnorm j C α lam ≤ gev (Cbase^(4*n+1)) Agev j := by
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
  · have he : (fun lam => wL θ lam*ENNReal.ofReal (BN lam + BW lam)) =
        fun lam => wL θ lam*ENNReal.ofReal (BN lam) + wL θ lam*ENNReal.ofReal (BW lam) := by
      funext lam
      rw [ENNReal.ofReal_add (hpN lam) (hpW lam), mul_add]
    rw [he, lintegral_add_left (f := fun lam => wL θ lam*ENNReal.ofReal (BN lam))
      ((measurable_wL θ).mul (ENNReal.measurable_ofReal.comp hmN)), two_mul]
    exact add_le_add hbN' hbW'
  · filter_upwards [hgN, hgW] with lam hN hW
    intro z β γ'
    set H := (1+2*Real.pi)*(1+((∑ j, ‖β j‖)+(∑ j, ‖γ' j‖))) with hHdef
    have hH : 0 ≤ H := by positivity
    set K := max Ks Kw
    have hKs : (Ks*δ)^n ≤ (K*δ)^n :=
      pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_right (le_max_left _ _) hδpos.le) n
    have hKw' : ((4:ℝ)^n)⁻¹*(Kw*(2*δ))^n ≤ (K*δ)^n := by
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
    have hw : ((4:ℝ)^n)⁻¹*‖normalizedWickCorrection L (2*δ) γ z β γ' J C lam‖ ≤ H*(K*δ)^n*BW lam := by
      calc _ ≤ ((4:ℝ)^n)⁻¹*(H*(Kw*(2*δ))^n*BW lam) :=
            mul_le_mul_of_nonneg_left h2 (by positivity)
        _ = H*(((4:ℝ)^n)⁻¹*(Kw*(2*δ))^n)*BW lam := by ring
        _ ≤ H*(K*δ)^n*BW lam :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hKw' hH) (hpW lam)
    have hs : ‖(((δ/(2*L^((d:ℝ)-γ)))^(2*n):ℝ):ℂ) *
        approxSum L (L^(2*γ)*(2*δ)) (halfCellAmplitude z β γ')
          (resProfile J (fun Ω => C (ofLp Ω) lam))‖ ≤ H*(K*δ)^n*BN lam :=
      h1.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hKs hH) (hpN lam))
    calc _ ≤ H*(K*δ)^n*BN lam + H*(K*δ)^n*BW lam := add_le_add hs hw
      _ = _ := by ring

end WaveTurbulence.Flower.FiltCoh
