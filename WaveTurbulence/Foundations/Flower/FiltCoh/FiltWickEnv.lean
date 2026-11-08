/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.FiltCoh.FiltSymbol
public import WaveTurbulence.Foundations.Flower.FiltCoh.FiltWickCrude
public import WaveTurbulence.Foundations.Flower.FiltCoh.SymbolEnvU

/-! # FILT-COH (d2d): envelopes of the filtered physical cell symbol, uniform in the modulations and filters

FiltCoh's `WickUniform` chain (`traced_halfCell_sum_envelope_u`, `wick_slice_scalar_envelope_u`,
`wick_correction_envelope_theta_u`, `physical_sum_envelope_theta_u`) and `SymbolEnvU.physical_symbol_envelope_u`
with the filtered crude sum `halfCell_crude_filt_res` in place of `halfCell_crude_uniform_res`. The envelopes are
main's coefficient normalizers (independent of the filters); every link filter is a product of at most `N` good
factors of constant `K`, the traced links cost `K^{N |T|} ≤ K^{N n}` (absorbed in the geometric constant). -/

public section
noncomputable section
namespace WaveTurbulence.Flower.FiltCoh
open WaveTurbulence.RegAsymp MeasureTheory ClassJR ApproxNT Finset WithLp
open scoped ENNReal ContDiff

variable {d : ℕ}

attribute [-instance] WaveTurbulence.Mole.instFintypePositionCode

/-- Traced NT envelope with filtered survivors. -/
theorem traced_halfCell_sum_envelope_filt (hd : 3 ≤ d) {γ η : ℝ}
    (hγ : γ ∈ Set.Ioo (0:ℝ) 1) (hη0 : 0 < η) (hη : η ≤ 1/20)
    (hηγ : η ≤ ((d:ℝ)-1)*(1-γ)) {K : ℝ} (hK : 1 ≤ K) (N : ℕ) :
    ∃ Knt : ℝ, 0 < Knt ∧ ∀ Aorder : ℝ, ∃ L₀ : ℝ, ∀ L : ℝ, L₀ ≤ L →
      ∀ δ : ℝ, L^(-(η/2)) ≤ δ → δ ≤ 1 →
      ∀ n : ℕ, (n:ℝ) ≤ Real.log L^Aorder →
      ∀ (T J : Finset (Fin n)) (hTJ : Disjoint T J), T.Nonempty →
      ∀ (C : ({j : Fin n // j ∉ J} → ℝ) → ℝ × ℝ → ℂ), SymReg C →
      ∀ θ N' Agev : ℝ, 0 ≤ θ → θ ≤ 1 → 0 ≤ N' → 0 ≤ Agev →
      (∀ k, ∫⁻ α, ∫⁻ lam, wL θ lam*dnorm k C α lam ≤ gev N' Agev k) →
      ∃ g : (ℝ × ℝ) → ℝ, Measurable g ∧ Integrable g ∧ (∀ lam, 0 < g lam) ∧
        (∫⁻ lam, wL θ lam*ENNReal.ofReal (g lam)) < ⊤ ∧
        (∫⁻ lam, wL θ lam*ENNReal.ofReal (g lam)) ≤
          ENNReal.ofReal ((4*max 1 (4*Agev))^T.card*(T.card:ℝ)^T.card*((2*T.card).factorial:ℝ))*
            (ENNReal.ofReal N' * ∑' k : ℕ,
              ENNReal.ofReal ((4*Agev)^k*((2*k).factorial:ℝ)/(4*k).factorial)) +
            (∫⁻ lam, wL θ lam*ENNReal.ofReal (frequencyGaussian lam)) ∧
        ∀ᵐ lam : ℝ × ℝ,
          ∀ z : (Fin (Fintype.card {j : Fin n // j ∉ T}) × Fin 2) → Fin d → ℤ,
          ∀ β γ' : Fin (Fintype.card {j : Fin n // j ∉ T}) → Mom d,
          ∀ ψs : Fin (Fintype.card {j : Fin n // j ∉ T}) → ℝ → ℂ, (∀ i, FiltMul d K N (ψs i)) →
          ‖(((δ/(2*L^((d:ℝ)-γ)))^(2*Fintype.card {j : Fin n // j ∉ T}):ℝ):ℂ) *
            approxSum L (L^(2*γ)*δ) (halfCellAmplitude z β γ')
              (filtRes (survivingSpecial T J)
                (fun Ω => survivingTraceCoefficient T J hTJ C (ofLp Ω) lam) ψs)‖ ≤
            g lam*(2*(Knt*δ/4)^Fintype.card {j : Fin n // j ∉ T}) := by
  obtain ⟨Knt,hKnt,hNT⟩ := halfCell_crude_filt_res hd hγ hη0 hη hηγ (le_refl (1:ℝ)) hK N
  refine ⟨Knt,hKnt,fun Aorder => ?_⟩
  obtain ⟨L₀,hL₀⟩ := hNT Aorder
  refine ⟨max L₀ 1,?_⟩
  intro L hL δ hδ hδ1 n hn T J hTJ hT C hC θ N' Agev hθ0 hθ1 hN hAgev hmain
  have hL0 : 0 < L := by linarith [le_max_right L₀ 1]
  have hδ0 : 0 < δ := (Real.rpow_pos_of_pos hL0 _).trans_le hδ
  obtain ⟨g,hgm,hgi,hgp,hgf,hgmass,hgood⟩ := surviving_trace_NT_normalizer T J hTJ hT hC
    hθ0 hθ1 hN hAgev hmain
  refine ⟨g,hgm,hgi,hgp,hgf,hgmass,?_⟩
  filter_upwards [hgood] with lam hlam
  intro z β γ' ψs hψs
  have hcard : (Fintype.card {j : Fin n // j ∉ T}:ℝ) ≤ (n:ℝ) := by
    exact_mod_cast (Fintype.card_subtype_le (fun j : Fin n => j ∉ T)).trans_eq (Fintype.card_fin n)
  have hm : (Fintype.card {j : Fin n // j ∉ T}:ℝ) ≤ Real.log L^Aorder := hcard.trans hn
  let Ψ := fun Ω : EuclideanSpace ℝ
      {i : Fin (Fintype.card {j : Fin n // j ∉ T}) // i ∉ survivingSpecial T J} =>
    (g lam)⁻¹ • survivingTraceCoefficient T J hTJ C (ofLp Ω) lam
  have hD1 : WordDerivL1 Ψ (fun k => (1:ℝ)^(Fintype.card {j : Fin n // j ∉ T}) * ((4*k).factorial:ℝ)) := by
    simpa only [one_pow, one_mul] using hlam.2
  have hh := hL₀ L ((le_max_left _ _).trans hL) δ ⟨hδ0, hδ1⟩ _ hm z β γ' (survivingSpecial T J) Ψ
    hlam.1 hD1 ψs hψs
  have he : (fun Ω : EuclideanSpace ℝ
      {i : Fin (Fintype.card {j : Fin n // j ∉ T}) // i ∉ survivingSpecial T J} =>
      survivingTraceCoefficient T J hTJ C (ofLp Ω) lam) = fun Ω => g lam • Ψ Ω := by
    funext Ω
    simp only [Ψ,smul_smul,mul_inv_cancel₀ (hgp lam).ne',one_smul]
  rw [he,approxSum_filtRes_smul,mul_smul_comm,norm_smul,Real.norm_eq_abs,abs_of_pos (hgp lam)]
  exact mul_le_mul_of_nonneg_left hh (hgp lam).le

/-- Filtered Wick slice envelope. -/
theorem wick_slice_scalar_envelope_filt (hd : 3 ≤ d) {γ η : ℝ}
    (hγ : γ ∈ Set.Ioo (0:ℝ) 1) (hη0 : 0 < η) (hη : η ≤ 1/20)
    (hηγ : η ≤ ((d:ℝ)-1)*(1-γ)) {K : ℝ} (hK : 1 ≤ K) (N : ℕ) :
    ∃ Knt : ℝ, 0 < Knt ∧ ∀ Aorder : ℝ, ∃ L₀ : ℝ, ∀ L : ℝ, L₀ ≤ L →
      ∀ δ : ℝ, L^(-(η/2)) ≤ δ → δ ≤ 1 →
      ∀ n : ℕ, (n:ℝ) ≤ Real.log L^Aorder → ∀ σ : Fin n → Fin 4, σ ≠ 0 →
      ∀ (J : Finset (Fin n)) (hTJ : Disjoint (wickTracedLinks σ) J),
      ∀ (C : ({j : Fin n // j ∉ J} → ℝ) → ℝ × ℝ → ℂ), SymReg C →
      ∀ θ N' Agev : ℝ, 0 ≤ θ → θ ≤ 1 → 0 ≤ N' → 0 ≤ Agev →
      (∀ k, ∫⁻ α, ∫⁻ lam, wL θ lam*dnorm k C α lam ≤ gev N' Agev k) →
      ∃ g : (ℝ × ℝ) → ℝ, Measurable g ∧ Integrable g ∧ (∀ lam, 0 < g lam) ∧
        (∫⁻ lam, wL θ lam*ENNReal.ofReal (g lam)) < ⊤ ∧
        (∫⁻ lam, wL θ lam*ENNReal.ofReal (g lam)) ≤
          ENNReal.ofReal ((4*max 1 (4*Agev))^(wickTracedLinks σ).card*
            ((wickTracedLinks σ).card:ℝ)^(wickTracedLinks σ).card*((2*(wickTracedLinks σ).card).factorial:ℝ))*
            (ENNReal.ofReal N' * ∑' k : ℕ,
              ENNReal.ofReal ((4*Agev)^k*((2*k).factorial:ℝ)/(4*k).factorial)) +
            (∫⁻ lam, wL θ lam*ENNReal.ofReal (frequencyGaussian lam)) ∧
        ∀ᵐ lam : ℝ × ℝ, ∀ z : (Fin n × Fin 2) → Fin d → ℤ, ∀ β γ' : Fin n → Mom d,
          ∀ ψ : Fin n → ℝ → ℂ, (∀ j, FiltMul d K N (ψ j)) →
          ‖filtWickSlice L δ γ σ ψ z β γ' J C lam‖ ≤
            2*(Knt*δ)^n * ((L^(-((d:ℝ)-2*γ)))^(wickTracedLinks σ).card*g lam) := by
  obtain ⟨Kbase,hKbase,hNT⟩ := traced_halfCell_sum_envelope_filt hd hγ hη0 hη hηγ hK N
  let K' : ℝ := max (2^d) Kbase
  have hKpos : 0 < K' := hKbase.trans_le (le_max_right _ _)
  have hBψ : 1 ≤ K^N := one_le_pow₀ hK
  refine ⟨2*K'*K^N,by positivity,fun Aorder => ?_⟩
  obtain ⟨L₀,hL₀⟩ := hNT Aorder
  refine ⟨max L₀ 2,?_⟩
  intro L hL δ hδ hδ1 n hn σ hσ J hTJ C hC θ N' Agev hθ0 hθ1 hN hAgev hmain
  have hL1 : 1 ≤ L := by linarith [(le_max_right L₀ 2).trans hL]
  have hL0 : 0 < L := zero_lt_one.trans_le hL1
  have hδ0 : 0 ≤ δ := (Real.rpow_nonneg hL0.le _).trans hδ
  obtain ⟨g,hgm,hgi,hgp,hgf,hgmass,hgood⟩ := hL₀ L ((le_max_left _ _).trans hL) δ hδ hδ1 n hn
    (wickTracedLinks σ) J hTJ (wickTracedLinks_nonempty hσ) C hC θ N' Agev hθ0 hθ1 hN hAgev hmain
  refine ⟨g,hgm,hgi,hgp,hgf,hgmass,?_⟩
  filter_upwards [hgood] with lam hlam
  intro z β γ' ψ hψ
  have hsum := norm_filtWickSlice_le_traced_NT hL1 δ γ hδ0 σ ψ (Bψ := K^N)
    (fun j => (hψ j).norm_le hK 0) z β γ' J hTJ C lam
  have hnt := hlam (fun p => z (((wickSurvivorEquiv σ).symm p.1).val,p.2))
    (fun i => β ((wickSurvivorEquiv σ).symm i).val)
    (fun i => γ' ((wickSurvivorEquiv σ).symm i).val) (wickSurvivorFilt σ ψ) (fun i => hψ _)
  have hbudget := normalized_wick_count_budget (γ := γ) hL0 hδ0 hδ1 hKbase.le
    (le_max_left (2^d) Kbase) (le_max_right (2^d) Kbase)
    (card_untraced_add_trace (wickTracedLinks σ))
  have hTn : (wickTracedLinks σ).card ≤ n := by
    simpa only [card_univ,Fintype.card_fin] using card_le_card (subset_univ (wickTracedLinks σ))
  have hBT : (K^N)^(wickTracedLinks σ).card ≤ (K^N)^n := pow_le_pow_right₀ hBψ hTn
  apply hsum.trans
  have hg2 : 0 ≤ g lam * 2 := mul_nonneg (hgp lam).le (by norm_num)
  calc
    _ ≤ (2^n*(2^d*L^d)^(wickTracedLinks σ).card*(K^N)^(wickTracedLinks σ).card*
        (δ/(2*L^((d:ℝ)-γ)))^(2*(wickTracedLinks σ).card))*
        (g lam*(2*(Kbase*δ/4)^Fintype.card {j : Fin n // j ∉ wickTracedLinks σ})) :=
      mul_le_mul_of_nonneg_left hnt (by positivity)
    _ = (K^N)^(wickTracedLinks σ).card * (((δ/(2*L^((d:ℝ)-γ)))^(2*(wickTracedLinks σ).card)*
        (2^d*L^d)^(wickTracedLinks σ).card*(Kbase*δ/4)^Fintype.card {j : Fin n // j ∉ wickTracedLinks σ}*2^n)*
        (g lam*2)) := by ring
    _ ≤ (K^N)^n * (((2*K'*δ)^n*(L^(-((d:ℝ)-2*γ)))^(wickTracedLinks σ).card)*(g lam*2)) := by
        refine mul_le_mul hBT (mul_le_mul_of_nonneg_right hbudget hg2) (by positivity) (by positivity)
    _ = _ := by rw [mul_pow (2*K') δ, mul_pow (2*K'*K^N) δ, mul_pow (2*K') (K^N)]; ring

/-- Filtered Wick correction envelope. -/
theorem wick_correction_envelope_theta_filt (hd : 3 ≤ d) {γ η : ℝ}
    (hγ : γ ∈ Set.Ioo (0:ℝ) 1) (hη0 : 0 < η) (hη : η ≤ 1/20)
    (hηγ : η ≤ ((d:ℝ)-1)*(1-γ)) {K : ℝ} (hK : 1 ≤ K) (N : ℕ) :
    ∀ Agev : ℝ, 0 ≤ Agev → ∃ Knt : ℝ, 0 < Knt ∧
      ∀ Aorder : ℝ, ∃ L₀ : ℝ, ∀ L : ℝ, L₀ ≤ L →
      ∀ δ : ℝ, L^(-(η/2)) ≤ δ → δ ≤ 1 →
      ∀ n : ℕ, (n:ℝ) ≤ Real.log L^Aorder → ∀ J : Finset (Fin n),
      ∀ C : ({j : Fin n // j ∉ J} → ℝ) → ℝ × ℝ → ℂ, SymReg C →
      ∀ θ N' : ℝ, 0 ≤ θ → θ ≤ 1 → 0 ≤ N' →
      (∀ k, ∫⁻ α, ∫⁻ lam, wL θ lam*dnorm k C α lam ≤ gev N' Agev k) →
      ∃ B : (ℝ × ℝ) → ℝ, Measurable B ∧ (∀ lam, 0 ≤ B lam) ∧
        (∫⁻ lam, wL θ lam*ENNReal.ofReal (B lam)) ≤
          (4:ℝ≥0∞)^n*ENNReal.ofReal (L^(-gamma1 d γ))*
            ((ENNReal.ofReal N'*∑' k : ℕ,
              ENNReal.ofReal ((4*Agev)^k*((2*k).factorial:ℝ)/(4*k).factorial)) +
              (∫⁻ lam, wL θ lam*ENNReal.ofReal (frequencyGaussian lam))) ∧
        ∀ᵐ lam : ℝ × ℝ, ∀ z : (Fin n × Fin 2) → Fin d → ℤ, ∀ β γ' : Fin n → Mom d,
          ∀ ψ : Fin n → ℝ → ℂ, (∀ j, FiltMul d K N (ψ j)) →
          ‖filtWickCorrection L δ γ ψ z β γ' J C lam‖ ≤ 2*(Knt*δ)^n*B lam := by
  classical
  intro Agev hAgev
  obtain ⟨Knt,hKnt,hNT⟩ := wick_slice_scalar_envelope_filt hd hγ hη0 hη hηγ hK N
  refine ⟨Knt,hKnt,fun Aorder => ?_⟩
  obtain ⟨Lnt,hLnt⟩ := hNT Aorder
  obtain ⟨Ltrace,hLtrace⟩ := exists_wick_block_trace_threshold
    (C := 4*max 1 (4*Agev)) (ε := 1/4) (by positivity) (by norm_num) Aorder
  refine ⟨max Lnt (max Ltrace 2),?_⟩
  intro L hL δ hδ hδ1 n hn J C hC θ N' hθ0 hθ1 hN hmain
  have hL1 : 1 ≤ L := by
    linarith [(le_trans (le_max_right Ltrace 2) (le_max_right Lnt (max Ltrace 2))).trans hL]
  have hL0 : 0 < L := zero_lt_one.trans_le hL1
  have hLT : Ltrace ≤ L := ((le_max_left Ltrace 2).trans (le_max_right Lnt _)).trans hL
  have hLN : Lnt ≤ L := (le_max_left Lnt _).trans hL
  have hex (σ : {σ // σ ∈ wickAdmissiblePatterns J}) :=
    hLnt L hLN δ hδ hδ1 n hn σ.val ((mem_erase.mp (mem_filter.mp σ.property).1).1) J
      (mem_filter.mp σ.property).2 C hC θ N' Agev hθ0 hθ1 hN hAgev hmain
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
    (ENNReal.ofReal N'*∑' k : ℕ, ENNReal.ofReal ((4*Agev)^k*((2*k).factorial:ℝ)/(4*k).factorial))
    (∫⁻ lam, wL θ lam*ENNReal.ofReal (frequencyGaussian lam)) hcost hmass
  refine ⟨B,hmB,hnB,hbB,?_⟩
  have hgoodAll := (ae_all_iff).mpr hgood
  filter_upwards [hgoodAll] with lam hlam
  intro z β γ' ψ hψ
  apply (norm_filtWickCorrection_le_sum hL0 δ γ ψ z β γ' J C lam).trans
  calc
    _ ≤ ∑ σ : {σ // σ ∈ wickAdmissiblePatterns J},
        2*(Knt*δ)^n*((L^(-((d:ℝ)-2*γ)))^(wickTracedLinks σ.val).card*g σ lam) :=
      sum_le_sum (fun σ _ => hlam σ z β γ' ψ hψ)
    _ = _ := by dsimp only [B,scaledWickEnvelope]; rw [Finset.mul_sum]

/-- Filtered NT-sum envelope. -/
theorem physical_sum_envelope_theta_filt (hd : 3 ≤ d) {γ η : ℝ}
    (hγ : γ ∈ Set.Ioo (0:ℝ) 1) (hη0 : 0 < η) (hη : η ≤ 1/20)
    (hηγ : η ≤ ((d:ℝ)-1)*(1-γ)) {K : ℝ} (hK : 1 ≤ K) (Nf : ℕ) :
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
          ∀ ψ : Fin n → ℝ → ℂ, (∀ j, FiltMul d K Nf (ψ j)) →
          ‖(((δ/(2*L^((d:ℝ)-γ)))^(2*n):ℝ):ℂ) *
            approxSum L (L^(2*γ)*(2*δ)) (halfCellAmplitude z β γ')
              (filtRes J (fun Ω => C (ofLp Ω) lam) ψ)‖ ≤ 2*(Knt*δ)^n*g lam := by
  obtain ⟨K',hK',hNT⟩ := halfCell_crude_filt_res hd hγ hη0 hη hηγ (le_refl (1:ℝ)) hK Nf
  refine ⟨K',hK',fun Aorder => ?_⟩
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
  intro z β γ' ψ hψ
  let Ψ := fun x : EuclideanSpace ℝ {j : Fin n // j ∉ J} => (g lam)⁻¹ • C (ofLp x) lam
  have hD1 : WordDerivL1 Ψ (fun k => (1:ℝ)^n * ((4*k).factorial:ℝ)) := by
    simpa only [one_pow, one_mul] using hlam.2
  have hh := hL₀ L ((le_max_left _ _).trans hL) (2*δ) ⟨by linarith, hδ1⟩ n hn z β γ' J Ψ hlam.1 hD1 ψ hψ
  have he : (fun Ω : EuclideanSpace ℝ {j : Fin n // j ∉ J} => C (ofLp Ω) lam) =
      fun Ω => g lam • Ψ Ω := by
    funext Ω
    simp only [Ψ,smul_smul,mul_inv_cancel₀ (hgp lam).ne',one_smul]
  rw [he,approxSum_filtRes_smul,mul_smul_comm,norm_smul,Real.norm_eq_abs,abs_of_pos (hgp lam)]
  set X := (((δ/(2*L^((d:ℝ)-γ)))^(2*n):ℝ):ℂ) *
    approxSum L (L^(2*γ)*(2*δ)) (halfCellAmplitude z β γ') (filtRes J Ψ ψ) with hXdef
  have hX : (4:ℝ)^n*‖X‖ ≤ 2*(K'*(2*δ)/4)^n := by
    rw [doubled_coupling_prefactor, mul_assoc, norm_mul, norm_pow] at hh
    simpa only [hXdef, show ‖(4:ℂ)‖ = 4 by norm_num] using hh
  have hle : (K'*(2*δ)/4)^n ≤ (4:ℝ)^n*(K'*δ)^n := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by positivity) (by nlinarith [hK'.le, hδ0.le]) n
  have hX' : ‖X‖ ≤ 2*(K'*δ)^n := by
    have h4 : (0:ℝ) < 4^n := by positivity
    refine le_of_mul_le_mul_left ?_ h4
    calc (4:ℝ)^n*‖X‖ ≤ 2*(K'*(2*δ)/4)^n := hX
      _ ≤ 2*((4:ℝ)^n*(K'*δ)^n) := by linarith
      _ = (4:ℝ)^n*(2*(K'*δ)^n) := by ring
  calc g lam*‖X‖ ≤ g lam*(2*(K'*δ)^n) := mul_le_mul_of_nonneg_left hX' (hgp lam).le
    _ = 2*(K'*δ)^n*g lam := by ring

/-- **One filtered physical cell symbol at weight `θ`, uniformly in the modulations and the filters.** -/
theorem filt_symbol_envelope (hd : 3 ≤ d) {γ η : ℝ}
    (hγ : γ ∈ Set.Ioo (0:ℝ) 1) (hη0 : 0 < η) (hη : η ≤ 1/20)
    (hηγ : η ≤ ((d:ℝ)-1)*(1-γ))
    {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ : θ ≤ 1-η/8)
    {Agev Cbase : ℝ} (hAgev : 0 ≤ Agev) (hCbase : 1 ≤ Cbase) {K : ℝ} (hK : 1 ≤ K) (Nf : ℕ) :
    ∃ Ks Cm : ℝ, 0 < Ks ∧ 1 ≤ Cm ∧
      ∀ Aorder : ℝ, ∃ L₀ : ℝ, ∀ L : ℝ, L₀ ≤ L →
      ∀ δ : ℝ, L^(-(η/2)) ≤ 2*δ → 2*δ ≤ 1 →
      ∀ n : ℕ, 0 < n → (n:ℝ) ≤ Real.log L^Aorder →
      ∀ (J : Finset (Fin n)) (C : ({j : Fin n // j ∉ J} → ℝ) → ℝ × ℝ → ℂ),
      SRep (1-η/8) (η/4) (1-η/2) Agev (Cbase^(4*n+1)) C →
      ∃ B : (ℝ × ℝ) → ℝ, Measurable B ∧ (∀ lam, 0 ≤ B lam) ∧
        (∫⁻ lam, wL θ lam*ENNReal.ofReal (B lam)) ≤ ENNReal.ofReal Cm^n ∧
        ∀ᵐ lam : ℝ × ℝ, ∀ (z : (Fin n × Fin 2) → Fin d → ℤ) (β γ' : Fin n → Mom d)
          (ψ : Fin n → ℝ → ℂ), (∀ j, FiltMul d K Nf (ψ j)) →
          ‖filtCellSymbol L δ γ ψ z β γ' J C lam‖ ≤ 2*(Ks*δ)^n*B lam := by
  have hθ1 : θ ≤ 1 := by linarith
  obtain ⟨Ks,hKs,hS⟩ := physical_sum_envelope_theta_filt hd hγ hη0 hη hηγ hK Nf
  obtain ⟨Kw,hKw,hW⟩ := wick_correction_envelope_theta_filt hd hγ hη0 hη hηγ hK Nf Agev hAgev
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
    intro z β γ' ψ hψ
    set K' := max Ks Kw
    have hKs' : (Ks*δ)^n ≤ (K'*δ)^n :=
      pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_right (le_max_left _ _) hδpos.le) n
    have hKw' : ((4:ℝ)^n)⁻¹*(Kw*(2*δ))^n ≤ (K'*δ)^n := by
      rw [← inv_pow, ← mul_pow]
      apply pow_le_pow_left₀ (by positivity)
      have : Kw ≤ K' := le_max_right _ _
      nlinarith [hKw.le, hδpos.le]
    rw [filtCellSymbol_eq_sum_add_wick (by linarith : (0:ℝ) < L)]
    refine (norm_add_le _ _).trans ?_
    have hw' : ∀ w : ℂ, ‖((4:ℂ)^n)⁻¹ * w‖ = ((4:ℝ)^n)⁻¹ * ‖w‖ := fun w => by
      rw [norm_mul, norm_inv, norm_pow]; norm_num
    rw [hw']
    have h1 := hN z β γ' ψ hψ
    have h2 := hW z β γ' ψ hψ
    have hw : ((4:ℝ)^n)⁻¹*‖filtWickCorrection L (2*δ) γ ψ z β γ' J C lam‖ ≤ 2*(K'*δ)^n*BW lam := by
      calc _ ≤ ((4:ℝ)^n)⁻¹*(2*(Kw*(2*δ))^n*BW lam) :=
            mul_le_mul_of_nonneg_left h2 (by positivity)
        _ = 2*(((4:ℝ)^n)⁻¹*(Kw*(2*δ))^n)*BW lam := by ring
        _ ≤ 2*(K'*δ)^n*BW lam :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hKw' (by norm_num)) (hpW lam)
    have hs := h1.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hKs' (by norm_num)) (hpN lam))
    calc _ ≤ 2*(K'*δ)^n*BN lam + 2*(K'*δ)^n*BW lam := add_le_add hs hw
      _ = _ := by ring

end WaveTurbulence.Flower.FiltCoh
