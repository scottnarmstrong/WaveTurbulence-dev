/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.RegularAsymptotics.RegAsympDraft.WickCorrectionEnvelope
public import WaveTurbulence.Foundations.RegAsymp.WickLargeOrder

/-! # The original J3 coefficient yields the full scalar Wick correction envelope -/

public section
noncomputable section
namespace WaveTurbulence.RegAsymp
open MeasureTheory ClassJR ApproxNT Finset
open scoped ENNReal

/-- DH23 Prop6.1's exceptional Wick term: each removed energy pays its
own trace cost, uniformly over arbitrary fixed polylogarithmic orders.
No oscillatory NT sum is replaced by an absolute lattice sum. -/
theorem wick_correction_scalar_envelope {d : ℕ} (hd : 3 ≤ d) {γ η : ℝ}
    (hγ : γ ∈ Set.Ioo (0:ℝ) 1) (hη0 : 0 < η) (hη : η ≤ 1/20)
    (hηγ : η ≤ ((d:ℝ)-1)*(1-γ)) (hηγ' : η ≤ γ) :
    ∀ Agev : ℝ, 0 ≤ Agev → ∃ Knt : ℝ, 0 < Knt ∧
      ∀ Aorder : ℝ, ∃ L₀ : ℝ, ∀ L : ℝ, L₀ ≤ L →
      ∀ δ : ℝ, L^(-(η/2)) ≤ δ → δ ≤ 1 →
      ∀ n : ℕ, (n:ℝ) ≤ Real.log L^Aorder → ∀ J : Finset (Fin n),
      ∀ C : ({j : Fin n // j ∉ J} → ℝ) → ℝ × ℝ → ℂ, SymReg C →
      ∀ N : ℝ, 0 ≤ N →
      (∀ k, ∫⁻ α, ∫⁻ lam, wL η lam*dnorm k C α lam ≤ gev N Agev k) →
      ∃ B : (ℝ × ℝ) → ℝ, Measurable B ∧ (∀ lam, 0 ≤ B lam) ∧
        (∫⁻ lam, wL η lam*ENNReal.ofReal (B lam)) < ⊤ ∧
        (∫⁻ lam, wL η lam*ENNReal.ofReal (B lam)) ≤
          (4:ℝ≥0∞)^n*ENNReal.ofReal (L^(-gamma1 d γ))*
            ((ENNReal.ofReal N*∑' k : ℕ,
              ENNReal.ofReal ((4*Agev)^k*((2*k).factorial:ℝ)/(4*k).factorial)) +
              (∫⁻ lam, wL η lam*ENNReal.ofReal (frequencyGaussian lam))) ∧
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
  intro L hL δ hδ hδ1 n hn J C hC N hN hmain
  have hL1 : 1 ≤ L := by linarith [(le_trans (le_max_right Ltrace 2) (le_max_right Lnt (max Ltrace 2))).trans hL]
  have hL0 : 0 < L := zero_lt_one.trans_le hL1
  have hLT : Ltrace ≤ L := ((le_max_left Ltrace 2).trans (le_max_right Lnt _)).trans hL
  have hLN : Lnt ≤ L := (le_max_left Lnt _).trans hL
  have hex (σ : {σ // σ ∈ wickAdmissiblePatterns J}) :=
    hLnt L hLN δ hδ hδ1 n hn σ.val ((mem_erase.mp (mem_filter.mp σ.property).1).1) J
      (mem_filter.mp σ.property).2 C hC η N Agev hη0.le (by linarith) hN hAgev hmain
  choose g hgm _hgi hgp _hgf hmass hgood using hex
  let B := scaledWickEnvelope d L γ J g
  have hmB : Measurable B := measurable_scaledWickEnvelope d L γ J g hgm
  have hnB : ∀ lam, 0 ≤ B lam := scaledWickEnvelope_nonneg d hL0.le γ J g (fun σ lam => (hgp σ lam).le)
  have hcost (σ : {σ // σ ∈ wickAdmissiblePatterns J}) :
      (4*max 1 (4*Agev))^(wickTracedLinks σ.val).card*
        ((wickTracedLinks σ.val).card:ℝ)^(wickTracedLinks σ.val).card*
          ((2*(wickTracedLinks σ.val).card).factorial:ℝ) ≤ L^(((wickTracedLinks σ.val).card:ℝ)/4) := by
    have hr : (wickTracedLinks σ.val).card ≤ n := by
      simpa only [card_univ,Fintype.card_fin] using card_le_card (subset_univ (wickTracedLinks σ.val))
    convert (hLtrace L hLT).2 n hn (wickTracedLinks σ.val).card hr using 1
    congr 1
    ring
  have hbB := lintegral_scaledWickEnvelope_le hd hL1 hγ η J g hgm (fun σ lam => (hgp σ lam).le)
    (fun σ => (4*max 1 (4*Agev))^(wickTracedLinks σ.val).card*
      ((wickTracedLinks σ.val).card:ℝ)^(wickTracedLinks σ.val).card*
      ((2*(wickTracedLinks σ.val).card).factorial:ℝ))
    (ENNReal.ofReal N*∑' k : ℕ, ENNReal.ofReal ((4*Agev)^k*((2*k).factorial:ℝ)/(4*k).factorial))
    (∫⁻ lam, wL η lam*ENNReal.ofReal (frequencyGaussian lam)) hcost hmass
  have hratio := (summable_gevrey_ratio (4*Agev) (by positivity)).tsum_ofReal_lt_top
  have hgauss := lintegral_wL_frequencyGaussian_lt_top (by linarith : η ≤ 1)
  refine ⟨B,hmB,hnB,?_,hbB,?_⟩
  · exact hbB.trans_lt (ENNReal.mul_lt_top
      (ENNReal.mul_lt_top (by finiteness) ENNReal.ofReal_lt_top)
      (ENNReal.add_lt_top.mpr ⟨ENNReal.mul_lt_top ENNReal.ofReal_lt_top hratio,hgauss⟩))
  · have hgoodAll := (ae_all_iff).mpr hgood
    filter_upwards [hgoodAll] with lam hlam
    intro z β γ'
    apply (norm_normalizedWickCorrection_le_sum hL0 δ γ z β γ' J C lam).trans
    calc
      _ ≤ ∑ σ : {σ // σ ∈ wickAdmissiblePatterns J},
          (1+2*Real.pi)*(1+((∑ j, ‖β j‖)+(∑ j, ‖γ' j‖)))*(Knt*δ)^n*
            ((L^(-((d:ℝ)-2*γ)))^(wickTracedLinks σ.val).card*g σ lam) :=
        sum_le_sum (fun σ _ => hlam σ z β γ')
      _ = _ := by dsimp only [B,scaledWickEnvelope]; rw [Finset.mul_sum]

end WaveTurbulence.RegAsymp
