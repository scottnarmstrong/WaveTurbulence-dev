/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.RegularAsymptotics.RegAsympDraft.WickCorrectionSourceEnvelope
public import WaveTurbulence.Foundations.RegularAsymptotics.RegAsympDraft.PhysicalLocalSymbol
public import WaveTurbulence.Foundations.RegularAsymptotics.RegAsympDraft.HalfCellCrudeSumAllOrders
public import WaveTurbulence.Foundations.RegularAsymptotics.RegAsympDraft.ErrorCoefficientBudget
public import WaveTurbulence.Foundations.RegAsymp.DerivativeCoefficientNormalizer
public import WaveTurbulence.Foundations.RegAsymp.SymbolLinearity
public import WaveTurbulence.Foundations.RegAsymp.RemainderMeasurability

/-! # FILT-COH: the actual physical cell symbol at an arbitrary time weight

Bound-only counterpart of main's error envelope (`RA1Leafwise.physical_error_scalar_envelope`, weight `η`): the
full physical cell symbol of DH23 (the local NT lattice sum with the squared Wick factors, at energy `2δ`) is
bounded at any time weight `θ ≤ 1` by

* the crude NT sum `halfCell_crude_normalized_sum_all_orders` (no moment premise) with the derivative-only
  normalizer `derivative_coefficient_NT_normalizer` (o82 Thm 10.1 (10.5), Lemma 16.1 coherent case); and
* the Wick correction, through main's `wick_slice_scalar_envelope`, which is already generic in the weight.

No principal value and no small error estimate is used. -/

public section
noncomputable section
namespace WaveTurbulence.Flower.FiltCoh
open WaveTurbulence.RegAsymp MeasureTheory ClassJR ApproxNT Finset WithLp
open scoped ENNReal

variable {d : ℕ}

/-- Main's `wick_correction_scalar_envelope` with the time weight `θ` separated from the NT parameter `η`
(main's proof, weight occurrences only replaced; source sha256 722fc3ce… in COPIED-SHA256SUMS). -/
theorem wick_correction_envelope_theta (hd : 3 ≤ d) {γ η : ℝ}
    (hγ : γ ∈ Set.Ioo (0:ℝ) 1) (hη0 : 0 < η) (hη : η ≤ 1/20)
    (hηγ : η ≤ ((d:ℝ)-1)*(1-γ)) (hηγ' : η ≤ γ) :
    ∀ Agev : ℝ, 0 ≤ Agev → ∃ Knt : ℝ, 0 < Knt ∧
      ∀ Aorder : ℝ, ∃ L₀ : ℝ, ∀ L : ℝ, L₀ ≤ L →
      ∀ δ : ℝ, L^(-(η/2)) ≤ δ → δ ≤ 1 →
      ∀ n : ℕ, (n:ℝ) ≤ Real.log L^Aorder → ∀ J : Finset (Fin n),
      ∀ C : ({j : Fin n // j ∉ J} → ℝ) → ℝ × ℝ → ℂ, SymReg C →
      ∀ θ N : ℝ, 0 ≤ θ → θ ≤ 1 → 0 ≤ N →
      (∀ k, ∫⁻ α, ∫⁻ lam, wL θ lam*dnorm k C α lam ≤ gev N Agev k) →
      ∃ B : (ℝ × ℝ) → ℝ, Measurable B ∧ (∀ lam, 0 ≤ B lam) ∧
        (∫⁻ lam, wL θ lam*ENNReal.ofReal (B lam)) ≤
          (4:ℝ≥0∞)^n*ENNReal.ofReal (L^(-gamma1 d γ))*
            ((ENNReal.ofReal N*∑' k : ℕ,
              ENNReal.ofReal ((4*Agev)^k*((2*k).factorial:ℝ)/(4*k).factorial)) +
              (∫⁻ lam, wL θ lam*ENNReal.ofReal (frequencyGaussian lam))) ∧
        ∀ᵐ lam : ℝ × ℝ, ∀ z : (Fin n × Fin 2) → Fin d → ℤ, ∀ β γ' : Fin n → Mom d,
          ‖normalizedWickCorrection L δ γ z β γ' J C lam‖ ≤
            (1+2*Real.pi)*(1+((∑ j, ‖β j‖)+(∑ j, ‖γ' j‖)))*(Knt*δ)^n*B lam := by
  classical
  intro Agev hAgev
  obtain ⟨Knt,hKnt,hNT⟩ := wick_slice_scalar_envelope hd hγ hη0 hη hηγ hηγ'
  refine ⟨Knt,hKnt,fun Aorder => ?_⟩
  obtain ⟨Lnt,hLnt⟩ := hNT Aorder
  obtain ⟨Ltrace,hLtrace⟩ := exists_wick_block_trace_threshold
    (C := 4*max 1 (4*Agev)) (ε := 1/4) (by positivity) (by norm_num) Aorder
  refine ⟨max Lnt (max Ltrace 2),?_⟩
  intro L hL δ hδ hδ1 n hn J C hC θ N hθ0 hθ1 hN hmain
  have hL1 : 1 ≤ L := by
    linarith [(le_trans (le_max_right Ltrace 2) (le_max_right Lnt (max Ltrace 2))).trans hL]
  have hL0 : 0 < L := zero_lt_one.trans_le hL1
  have hLT : Ltrace ≤ L := ((le_max_left Ltrace 2).trans (le_max_right Lnt _)).trans hL
  have hLN : Lnt ≤ L := (le_max_left Lnt _).trans hL
  have hex (σ : {σ // σ ∈ wickAdmissiblePatterns J}) :=
    hLnt L hLN δ hδ hδ1 n hn σ.val ((mem_erase.mp (mem_filter.mp σ.property).1).1) J
      (mem_filter.mp σ.property).2 C hC θ N Agev hθ0 hθ1 hN hAgev hmain
  choose g hgm _hgi hgp _hgf hmass hgood using hex
  let B := scaledWickEnvelope d L γ J g
  have hmB : Measurable B := measurable_scaledWickEnvelope d L γ J g hgm
  have hnB : ∀ lam, 0 ≤ B lam :=
    scaledWickEnvelope_nonneg d hL0.le γ J g (fun σ lam => (hgp σ lam).le)
  have hcost (σ : {σ // σ ∈ wickAdmissiblePatterns J}) :
      (4*max 1 (4*Agev))^(wickTracedLinks σ.val).card*
        ((wickTracedLinks σ.val).card:ℝ)^(wickTracedLinks σ.val).card*
          ((2*(wickTracedLinks σ.val).card).factorial:ℝ) ≤
        L^(((wickTracedLinks σ.val).card:ℝ)/4) := by
    have hr : (wickTracedLinks σ.val).card ≤ n := by
      simpa only [card_univ,Fintype.card_fin] using card_le_card (subset_univ (wickTracedLinks σ.val))
    convert (hLtrace L hLT).2 n hn (wickTracedLinks σ.val).card hr using 1
    congr 1
    ring
  have hbB := lintegral_scaledWickEnvelope_le hd hL1 hγ θ J g hgm (fun σ lam => (hgp σ lam).le)
    (fun σ => (4*max 1 (4*Agev))^(wickTracedLinks σ.val).card*
      ((wickTracedLinks σ.val).card:ℝ)^(wickTracedLinks σ.val).card*
      ((2*(wickTracedLinks σ.val).card).factorial:ℝ))
    (ENNReal.ofReal N*∑' k : ℕ, ENNReal.ofReal ((4*Agev)^k*((2*k).factorial:ℝ)/(4*k).factorial))
    (∫⁻ lam, wL θ lam*ENNReal.ofReal (frequencyGaussian lam)) hcost hmass
  refine ⟨B,hmB,hnB,hbB,?_⟩
  have hgoodAll := (ae_all_iff).mpr hgood
  filter_upwards [hgoodAll] with lam hlam
  intro z β γ'
  apply (norm_normalizedWickCorrection_le_sum hL0 δ γ z β γ' J C lam).trans
  calc
    _ ≤ ∑ σ : {σ // σ ∈ wickAdmissiblePatterns J},
        (1+2*Real.pi)*(1+((∑ j, ‖β j‖)+(∑ j, ‖γ' j‖)))*(Knt*δ)^n*
          ((L^(-((d:ℝ)-2*γ)))^(wickTracedLinks σ.val).card*g σ lam) :=
      sum_le_sum (fun σ _ => hlam σ z β γ')
    _ = _ := by dsimp only [B,scaledWickEnvelope]; rw [Finset.mul_sum]

/-- The physical cell symbol is the normalized NT sum at energy `2δ` plus the normalized Wick correction
(main's exact decomposition, with its leading term cancelled against the remainder's). -/
theorem physicalWeightedCellSymbol_eq_sum_add_wick {n : ℕ} {L : ℝ} (hL : 0 < L)
    (δ γ : ℝ) (z : (Fin n × Fin 2) → Fin d → ℤ) (β γ' : Fin n → Mom d)
    (J : Finset (Fin n)) (C : ({j : Fin n // j ∉ J} → ℝ) → ℝ × ℝ → ℂ) (lam : ℝ × ℝ) :
    physicalWeightedCellSymbol L δ γ z β γ' J C lam =
      (((δ/(2*L^((d:ℝ)-γ)))^(2*n):ℝ):ℂ) *
        approxSum L (L^(2*γ)*(2*δ)) (halfCellAmplitude z β γ') (resProfile J (fun Ω => C (ofLp Ω) lam)) +
      ((4:ℂ)^n)⁻¹ * normalizedWickCorrection L (2*δ) γ z β γ' J C lam := by
  rw [physicalWeightedCellSymbol_decomposition hL]
  unfold localRemainder
  rw [doubled_coupling_prefactor]
  have h4 : (4:ℂ)^n ≠ 0 := pow_ne_zero _ (by norm_num)
  field_simp
  ring

/-- **The crude NT sum at any weight `θ ≤ 1`**: the normalized lattice sum at energy `2δ`, with the actual
half-cell amplitude and a classified coefficient, is bounded by a positive normalizer of weighted mass at most
the derivative budget. -/
theorem physical_sum_envelope_theta (hd : 3 ≤ d) {γ η : ℝ}
    (hγ : γ ∈ Set.Ioo (0:ℝ) 1) (hη0 : 0 < η) (hη : η ≤ 1/20)
    (hηγ : η ≤ ((d:ℝ)-1)*(1-γ)) (hηγ' : η ≤ γ) :
    ∃ Knt : ℝ, 0 < Knt ∧ ∀ Aorder : ℝ, ∃ L₀ : ℝ, ∀ L : ℝ, L₀ ≤ L →
      ∀ δ : ℝ, L^(-(η/2)) ≤ 2*δ → 2*δ ≤ 1 →
      ∀ n : ℕ, (n:ℝ) ≤ Real.log L^Aorder → ∀ (J : Finset (Fin n))
        (C : ({j : Fin n // j ∉ J} → ℝ) → ℝ × ℝ → ℂ), SymReg C →
      ∀ θ N A : ℝ, 0 ≤ θ → θ ≤ 1 → 0 ≤ N → 0 ≤ A →
      (∀ k, ∫⁻ α, ∫⁻ lam, wL θ lam*dnorm k C α lam ≤ gev N A k) →
      ∃ g : (ℝ × ℝ) → ℝ, Measurable g ∧ (∀ lam, 0 ≤ g lam) ∧
        (∫⁻ lam, wL θ lam*ENNReal.ofReal (g lam)) ≤
          ENNReal.ofReal N*(∑' k : ℕ, ENNReal.ofReal (A^k*((2*k).factorial:ℝ)/(4*k).factorial)) +
            ∫⁻ lam, wL θ lam*ENNReal.ofReal (frequencyGaussian lam) ∧
        ∀ᵐ lam : ℝ × ℝ, ∀ z : (Fin n × Fin 2) → Fin d → ℤ, ∀ β γ' : Fin n → Mom d,
          ‖(((δ/(2*L^((d:ℝ)-γ)))^(2*n):ℝ):ℂ) *
            approxSum L (L^(2*γ)*(2*δ)) (halfCellAmplitude z β γ')
              (resProfile J (fun Ω => C (ofLp Ω) lam))‖ ≤
            (1+2*Real.pi)*(1+((∑ j, ‖β j‖)+(∑ j, ‖γ' j‖)))*(Knt*δ)^n*g lam := by
  obtain ⟨K,hK,hNT⟩ := halfCell_crude_normalized_sum_all_orders hd hγ hη0 hη hηγ hηγ'
  refine ⟨K,hK,fun Aorder => ?_⟩
  obtain ⟨L₀,hL₀⟩ := hNT Aorder
  refine ⟨max L₀ 2,?_⟩
  intro L hL δ hδ hδ1 n hn J C hC θ N A hθ0 hθ1 hN hA hmain
  have hL2 : 2 ≤ L := (le_max_right _ _).trans hL
  have hδ0 : 0 < δ := by
    have := Real.rpow_pos_of_pos (by linarith : (0:ℝ) < L) (-(η/2))
    linarith
  obtain ⟨g,hgm,_hgi,hgp,_hgf,hgmass,hgood⟩ :=
    derivative_coefficient_NT_normalizer hC hθ0 hθ1 hN hA hmain
  refine ⟨g,hgm,fun lam => (hgp lam).le,hgmass,?_⟩
  filter_upwards [hgood] with lam hlam
  intro z β γ'
  let Ψ := fun x : EuclideanSpace ℝ {j : Fin n // j ∉ J} => (g lam)⁻¹ • C (ofLp x) lam
  have hh := hL₀ L ((le_max_left _ _).trans hL) (2*δ) hδ hδ1 n hn z β γ' J Ψ hlam.1 hlam.2
  have he : (fun Ω : EuclideanSpace ℝ {j : Fin n // j ∉ J} => C (ofLp Ω) lam) =
      fun Ω => g lam • Ψ Ω := by
    funext Ω
    simp only [Ψ,smul_smul,mul_inv_cancel₀ (hgp lam).ne',one_smul]
  rw [he,approxSum_const_smul_symbol,mul_smul_comm,norm_smul,Real.norm_eq_abs,abs_of_pos (hgp lam)]
  set H := (1+2*Real.pi)*(1+((∑ j, ‖β j‖)+(∑ j, ‖γ' j‖))) with hHdef
  have hH : 0 ≤ H := by positivity
  set X := (((δ/(2*L^((d:ℝ)-γ)))^(2*n):ℝ):ℂ) *
    approxSum L (L^(2*γ)*(2*δ)) (halfCellAmplitude z β γ') (resProfile J Ψ) with hXdef
  have hX : (4:ℝ)^n*‖X‖ ≤ H*(K*(2*δ)/4)^n := by
    rw [doubled_coupling_prefactor, mul_assoc, norm_mul, norm_pow] at hh
    simpa only [hXdef, show ‖(4:ℂ)‖ = 4 by norm_num] using hh
  have hle : (K*(2*δ)/4)^n ≤ (4:ℝ)^n*(K*δ)^n := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by positivity) (by nlinarith [hK.le, hδ0.le]) n
  have hX' : ‖X‖ ≤ H*(K*δ)^n := by
    have h4 : (0:ℝ) < 4^n := by positivity
    refine le_of_mul_le_mul_left ?_ h4
    calc (4:ℝ)^n*‖X‖ ≤ H*(K*(2*δ)/4)^n := hX
      _ ≤ H*((4:ℝ)^n*(K*δ)^n) := mul_le_mul_of_nonneg_left hle hH
      _ = (4:ℝ)^n*(H*(K*δ)^n) := by ring
  calc g lam*‖X‖ ≤ g lam*(H*(K*δ)^n) := mul_le_mul_of_nonneg_left hX' (hgp lam).le
    _ = H*(K*δ)^n*g lam := by ring

end WaveTurbulence.Flower.FiltCoh
