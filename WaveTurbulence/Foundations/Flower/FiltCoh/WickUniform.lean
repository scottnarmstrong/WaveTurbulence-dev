/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.FiltCoh.CrudeSum
public import WaveTurbulence.Foundations.Flower.FiltCoh.SymbolEnvelope
public import WaveTurbulence.Foundations.RegularAsymptotics.RegAsympDraft.WickSliceEnvelope

/-! # FILT-COH (b): the physical cell symbol, uniformly in the modulations

Main's traced, slice and correction envelopes (`traced_halfCell_sum_envelope`, `wick_slice_scalar_envelope`,
FiltCoh's `wick_correction_envelope_theta`) and the sum envelope `physical_sum_envelope_theta`, with the crude sum
`halfCell_crude_uniform_res` in place of main's `halfCell_crude_normalized_sum_all_orders`: the first-moment
factor `(1+2π)(1+∑‖β‖+∑‖γ'‖)` becomes the constant `2`. The traced links are bounded by counting, as in main
(sha256 of the adapted sources in COPIED-SHA256SUMS). -/

public section
noncomputable section
namespace WaveTurbulence.Flower.FiltCoh
open WaveTurbulence.RegAsymp MeasureTheory ClassJR ApproxNT Finset WithLp
open scoped ENNReal ContDiff

variable {d : ℕ}

/-- Main's `traced_halfCell_sum_envelope`, uniform in the modulations. -/
theorem traced_halfCell_sum_envelope_u (hd : 3 ≤ d) {γ η : ℝ}
    (hγ : γ ∈ Set.Ioo (0:ℝ) 1) (hη0 : 0 < η) (hη : η ≤ 1/20)
    (hηγ : η ≤ ((d:ℝ)-1)*(1-γ)) :
    ∃ Knt : ℝ, 0 < Knt ∧ ∀ Aorder : ℝ, ∃ L₀ : ℝ, ∀ L : ℝ, L₀ ≤ L →
      ∀ δ : ℝ, L^(-(η/2)) ≤ δ → δ ≤ 1 →
      ∀ n : ℕ, (n:ℝ) ≤ Real.log L^Aorder →
      ∀ (T J : Finset (Fin n)) (hTJ : Disjoint T J), T.Nonempty →
      ∀ (C : ({j : Fin n // j ∉ J} → ℝ) → ℝ × ℝ → ℂ), SymReg C →
      ∀ θ N Agev : ℝ, 0 ≤ θ → θ ≤ 1 → 0 ≤ N → 0 ≤ Agev →
      (∀ k, ∫⁻ α, ∫⁻ lam, wL θ lam*dnorm k C α lam ≤ gev N Agev k) →
      ∃ g : (ℝ × ℝ) → ℝ, Measurable g ∧ Integrable g ∧ (∀ lam, 0 < g lam) ∧
        (∫⁻ lam, wL θ lam*ENNReal.ofReal (g lam)) < ⊤ ∧
        (∫⁻ lam, wL θ lam*ENNReal.ofReal (g lam)) ≤
          ENNReal.ofReal ((4*max 1 (4*Agev))^T.card*(T.card:ℝ)^T.card*((2*T.card).factorial:ℝ))*
            (ENNReal.ofReal N * ∑' k : ℕ,
              ENNReal.ofReal ((4*Agev)^k*((2*k).factorial:ℝ)/(4*k).factorial)) +
            (∫⁻ lam, wL θ lam*ENNReal.ofReal (frequencyGaussian lam)) ∧
        ∀ᵐ lam : ℝ × ℝ,
          ∀ z : (Fin (Fintype.card {j : Fin n // j ∉ T}) × Fin 2) → Fin d → ℤ,
          ∀ β γ' : Fin (Fintype.card {j : Fin n // j ∉ T}) → Mom d,
          ‖(((δ/(2*L^((d:ℝ)-γ)))^(2*Fintype.card {j : Fin n // j ∉ T}):ℝ):ℂ) *
            approxSum L (L^(2*γ)*δ) (halfCellAmplitude z β γ')
              (resProfile (survivingSpecial T J)
                (fun Ω => survivingTraceCoefficient T J hTJ C (ofLp Ω) lam))‖ ≤
            g lam*(2*(Knt*δ/4)^Fintype.card {j : Fin n // j ∉ T}) := by
  obtain ⟨Knt,hKnt,hNT⟩ := halfCell_crude_uniform_res hd hγ hη0 hη hηγ (le_refl (1:ℝ))
  refine ⟨Knt,hKnt,fun Aorder => ?_⟩
  obtain ⟨L₀,hL₀⟩ := hNT Aorder
  refine ⟨max L₀ 1,?_⟩
  intro L hL δ hδ hδ1 n hn T J hTJ hT C hC θ N Agev hθ0 hθ1 hN hAgev hmain
  have hL0 : 0 < L := by linarith [le_max_right L₀ 1]
  have hδ0 : 0 < δ := (Real.rpow_pos_of_pos hL0 _).trans_le hδ
  obtain ⟨g,hgm,hgi,hgp,hgf,hgmass,hgood⟩ := surviving_trace_NT_normalizer T J hTJ hT hC
    hθ0 hθ1 hN hAgev hmain
  refine ⟨g,hgm,hgi,hgp,hgf,hgmass,?_⟩
  filter_upwards [hgood] with lam hlam
  intro z β γ'
  have hcard : (Fintype.card {j : Fin n // j ∉ T}:ℝ) ≤ (n:ℝ) := by
    exact_mod_cast (Fintype.card_subtype_le (fun j : Fin n => j ∉ T)).trans_eq (Fintype.card_fin n)
  have hm : (Fintype.card {j : Fin n // j ∉ T}:ℝ) ≤ Real.log L^Aorder := hcard.trans hn
  let Ψ := fun Ω : EuclideanSpace ℝ
      {i : Fin (Fintype.card {j : Fin n // j ∉ T}) // i ∉ survivingSpecial T J} =>
    (g lam)⁻¹ • survivingTraceCoefficient T J hTJ C (ofLp Ω) lam
  have hD1 : WordDerivL1 Ψ (fun k => (1:ℝ)^(Fintype.card {j : Fin n // j ∉ T}) * ((4*k).factorial:ℝ)) := by
    simpa only [one_pow, one_mul] using hlam.2
  have hh := hL₀ L ((le_max_left _ _).trans hL) δ ⟨hδ0, hδ1⟩ _ hm z β γ' (survivingSpecial T J) Ψ
    hlam.1 hD1
  have he : (fun Ω : EuclideanSpace ℝ
      {i : Fin (Fintype.card {j : Fin n // j ∉ T}) // i ∉ survivingSpecial T J} =>
      survivingTraceCoefficient T J hTJ C (ofLp Ω) lam) = fun Ω => g lam • Ψ Ω := by
    funext Ω
    simp only [Ψ,smul_smul,mul_inv_cancel₀ (hgp lam).ne',one_smul]
  rw [he,approxSum_const_smul_symbol,mul_smul_comm,norm_smul,Real.norm_eq_abs,abs_of_pos (hgp lam)]
  exact mul_le_mul_of_nonneg_left hh (hgp lam).le

/-- Main's `wick_slice_scalar_envelope`, uniform in the modulations. -/
theorem wick_slice_scalar_envelope_u (hd : 3 ≤ d) {γ η : ℝ}
    (hγ : γ ∈ Set.Ioo (0:ℝ) 1) (hη0 : 0 < η) (hη : η ≤ 1/20)
    (hηγ : η ≤ ((d:ℝ)-1)*(1-γ)) :
    ∃ Knt : ℝ, 0 < Knt ∧ ∀ Aorder : ℝ, ∃ L₀ : ℝ, ∀ L : ℝ, L₀ ≤ L →
      ∀ δ : ℝ, L^(-(η/2)) ≤ δ → δ ≤ 1 →
      ∀ n : ℕ, (n:ℝ) ≤ Real.log L^Aorder → ∀ σ : Fin n → Fin 4, σ ≠ 0 →
      ∀ (J : Finset (Fin n)) (hTJ : Disjoint (wickTracedLinks σ) J),
      ∀ (C : ({j : Fin n // j ∉ J} → ℝ) → ℝ × ℝ → ℂ), SymReg C →
      ∀ θ N Agev : ℝ, 0 ≤ θ → θ ≤ 1 → 0 ≤ N → 0 ≤ Agev →
      (∀ k, ∫⁻ α, ∫⁻ lam, wL θ lam*dnorm k C α lam ≤ gev N Agev k) →
      ∃ g : (ℝ × ℝ) → ℝ, Measurable g ∧ Integrable g ∧ (∀ lam, 0 < g lam) ∧
        (∫⁻ lam, wL θ lam*ENNReal.ofReal (g lam)) < ⊤ ∧
        (∫⁻ lam, wL θ lam*ENNReal.ofReal (g lam)) ≤
          ENNReal.ofReal ((4*max 1 (4*Agev))^(wickTracedLinks σ).card*
            ((wickTracedLinks σ).card:ℝ)^(wickTracedLinks σ).card*((2*(wickTracedLinks σ).card).factorial:ℝ))*
            (ENNReal.ofReal N * ∑' k : ℕ,
              ENNReal.ofReal ((4*Agev)^k*((2*k).factorial:ℝ)/(4*k).factorial)) +
            (∫⁻ lam, wL θ lam*ENNReal.ofReal (frequencyGaussian lam)) ∧
        ∀ᵐ lam : ℝ × ℝ, ∀ z : (Fin n × Fin 2) → Fin d → ℤ, ∀ β γ' : Fin n → Mom d,
          ‖normalizedWickSlice L δ γ σ z β γ' J C lam‖ ≤
            2*(Knt*δ)^n * ((L^(-((d:ℝ)-2*γ)))^(wickTracedLinks σ).card*g lam) := by
  obtain ⟨Kbase,hKbase,hNT⟩ := traced_halfCell_sum_envelope_u hd hγ hη0 hη hηγ
  let K : ℝ := max (2^d) Kbase
  have hKpos : 0 < K := hKbase.trans_le (le_max_right _ _)
  refine ⟨2*K,by positivity,fun Aorder => ?_⟩
  obtain ⟨L₀,hL₀⟩ := hNT Aorder
  refine ⟨max L₀ 2,?_⟩
  intro L hL δ hδ hδ1 n hn σ hσ J hTJ C hC θ N Agev hθ0 hθ1 hN hAgev hmain
  have hL1 : 1 ≤ L := by linarith [(le_max_right L₀ 2).trans hL]
  have hL0 : 0 < L := zero_lt_one.trans_le hL1
  have hδ0 : 0 ≤ δ := (Real.rpow_nonneg hL0.le _).trans hδ
  obtain ⟨g,hgm,hgi,hgp,hgf,hgmass,hgood⟩ := hL₀ L ((le_max_left _ _).trans hL) δ hδ hδ1 n hn
    (wickTracedLinks σ) J hTJ (wickTracedLinks_nonempty hσ) C hC θ N Agev hθ0 hθ1 hN hAgev hmain
  refine ⟨g,hgm,hgi,hgp,hgf,hgmass,?_⟩
  filter_upwards [hgood] with lam hlam
  intro z β γ'
  have hsum := norm_normalized_wickSlice_le_traced_NT hL1 (L^(2*γ)*δ) δ γ hδ0 σ z β γ' J hTJ C lam
  have hnt := hlam (fun p => z (((wickSurvivorEquiv σ).symm p.1).val,p.2))
    (fun i => β ((wickSurvivorEquiv σ).symm i).val)
    (fun i => γ' ((wickSurvivorEquiv σ).symm i).val)
  have hbudget := normalized_wick_count_budget (γ := γ) hL0 hδ0 hδ1 hKbase.le
    (le_max_left (2^d) Kbase) (le_max_right (2^d) Kbase)
    (card_untraced_add_trace (wickTracedLinks σ))
  unfold normalizedWickSlice
  apply hsum.trans
  calc
    _ ≤ (2^n*(2^d*L^d)^(wickTracedLinks σ).card*
        (δ/(2*L^((d:ℝ)-γ)))^(2*(wickTracedLinks σ).card))*
        (g lam*(2*(Kbase*δ/4)^Fintype.card {j : Fin n // j ∉ wickTracedLinks σ})) :=
      mul_le_mul_of_nonneg_left hnt (by positivity)
    _ = ((δ/(2*L^((d:ℝ)-γ)))^(2*(wickTracedLinks σ).card)*
        (2^d*L^d)^(wickTracedLinks σ).card*(Kbase*δ/4)^Fintype.card {j : Fin n // j ∉ wickTracedLinks σ}*2^n)*
        (g lam*2) := by ring
    _ ≤ ((2*K*δ)^n*(L^(-((d:ℝ)-2*γ)))^(wickTracedLinks σ).card)*(g lam*2) :=
      mul_le_mul_of_nonneg_right hbudget (mul_nonneg (hgp lam).le (by norm_num))
    _ = _ := by ring

/-- FiltCoh's `wick_correction_envelope_theta`, uniform in the modulations. -/
theorem wick_correction_envelope_theta_u (hd : 3 ≤ d) {γ η : ℝ}
    (hγ : γ ∈ Set.Ioo (0:ℝ) 1) (hη0 : 0 < η) (hη : η ≤ 1/20)
    (hηγ : η ≤ ((d:ℝ)-1)*(1-γ)) :
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
          ‖normalizedWickCorrection L δ γ z β γ' J C lam‖ ≤ 2*(Knt*δ)^n*B lam := by
  classical
  intro Agev hAgev
  obtain ⟨Knt,hKnt,hNT⟩ := wick_slice_scalar_envelope_u hd hγ hη0 hη hηγ
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
        2*(Knt*δ)^n*((L^(-((d:ℝ)-2*γ)))^(wickTracedLinks σ.val).card*g σ lam) :=
      sum_le_sum (fun σ _ => hlam σ z β γ')
    _ = _ := by dsimp only [B,scaledWickEnvelope]; rw [Finset.mul_sum]

/-- FiltCoh's `physical_sum_envelope_theta`, uniform in the modulations. -/
theorem physical_sum_envelope_theta_u (hd : 3 ≤ d) {γ η : ℝ}
    (hγ : γ ∈ Set.Ioo (0:ℝ) 1) (hη0 : 0 < η) (hη : η ≤ 1/20)
    (hηγ : η ≤ ((d:ℝ)-1)*(1-γ)) :
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
              (resProfile J (fun Ω => C (ofLp Ω) lam))‖ ≤ 2*(Knt*δ)^n*g lam := by
  obtain ⟨K,hK,hNT⟩ := halfCell_crude_uniform_res hd hγ hη0 hη hηγ (le_refl (1:ℝ))
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
  have hD1 : WordDerivL1 Ψ (fun k => (1:ℝ)^n * ((4*k).factorial:ℝ)) := by
    simpa only [one_pow, one_mul] using hlam.2
  have hh := hL₀ L ((le_max_left _ _).trans hL) (2*δ) ⟨by linarith, hδ1⟩ n hn z β γ' J Ψ hlam.1 hD1
  have he : (fun Ω : EuclideanSpace ℝ {j : Fin n // j ∉ J} => C (ofLp Ω) lam) =
      fun Ω => g lam • Ψ Ω := by
    funext Ω
    simp only [Ψ,smul_smul,mul_inv_cancel₀ (hgp lam).ne',one_smul]
  rw [he,approxSum_const_smul_symbol,mul_smul_comm,norm_smul,Real.norm_eq_abs,abs_of_pos (hgp lam)]
  set X := (((δ/(2*L^((d:ℝ)-γ)))^(2*n):ℝ):ℂ) *
    approxSum L (L^(2*γ)*(2*δ)) (halfCellAmplitude z β γ') (resProfile J Ψ) with hXdef
  have hX : (4:ℝ)^n*‖X‖ ≤ 2*(K*(2*δ)/4)^n := by
    rw [doubled_coupling_prefactor, mul_assoc, norm_mul, norm_pow] at hh
    simpa only [hXdef, show ‖(4:ℂ)‖ = 4 by norm_num] using hh
  have hle : (K*(2*δ)/4)^n ≤ (4:ℝ)^n*(K*δ)^n := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by positivity) (by nlinarith [hK.le, hδ0.le]) n
  have hX' : ‖X‖ ≤ 2*(K*δ)^n := by
    have h4 : (0:ℝ) < 4^n := by positivity
    refine le_of_mul_le_mul_left ?_ h4
    calc (4:ℝ)^n*‖X‖ ≤ 2*(K*(2*δ)/4)^n := hX
      _ ≤ 2*((4:ℝ)^n*(K*δ)^n) := by linarith
      _ = (4:ℝ)^n*(2*(K*δ)^n) := by ring
  calc g lam*‖X‖ ≤ g lam*(2*(K*δ)^n) := mul_le_mul_of_nonneg_left hX' (hgp lam).le
    _ = 2*(K*δ)^n*g lam := by ring

end WaveTurbulence.Flower.FiltCoh
