/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.RegularAsymptotics.RegAsympDraft.HalfCellFrequencyMajorant
public import WaveTurbulence.Foundations.RegAsymp.CoefficientNormalizer
public import WaveTurbulence.Foundations.RegAsymp.DerivativeCoefficientNormalizer

/-! # Actual J3 fields yield an integrable common localized remainder envelope

The envelope is chosen independently of every link center and modulation.
Its η-weighted mass has exactly the DH23 rate L^(-γ1+2η).
-/

public section
noncomputable section
namespace WaveTurbulence.RegAsymp
open MeasureTheory ApproxNT ClassJR WithLp
open scoped ENNReal ContDiff

/-- Fully quantified coefficient-to-remainder envelope for an actual
half-cell NT amplitude, with the source weak/strong time weights kept distinct. -/
theorem local_symbol_remainder_envelope {d : ℕ} (hd : 3 ≤ d) {γ η : ℝ}
    (hγ : γ ∈ Set.Ioo (0:ℝ) 1) (hη0 : 0 < η) (hη : η ≤ 1/20)
    (hηγ : η ≤ ((d:ℝ)-1)*(1-γ)) (hηγ' : η ≤ γ) :
    ∃ K : ℝ, 0 < K ∧ ∀ Aorder : ℝ, ∃ L₀ : ℝ, ∀ L : ℝ, L₀ ≤ L →
      ∀ δ : ℝ, L^(-(η/2)) ≤ δ → δ ≤ 1 → ∀ n : ℕ, 0 < n → (n:ℝ) ≤ Real.log L^Aorder →
      ∀ (J : Finset (Fin n)) (C : ({j : Fin n // j ∉ J} → ℝ) → ℝ × ℝ → ℂ),
      SymReg C → ∀ N Agev : ℝ, 0 ≤ N → 0 ≤ Agev →
      (∀ k, ∫⁻ α, ∫⁻ lam, wL (1-η/8) lam*dnorm k C α lam ≤ gev N Agev k) →
      (∀ i : {j : Fin n // j ∉ J}, ∫⁻ α, ∫⁻ lam,
        wL (η/4) lam*(1+‖α i‖ₑ)^(1-η/2)*‖C α lam‖ₑ ≤ ENNReal.ofReal N) →
      ∃ B : (ℝ × ℝ) → ℝ, Measurable B ∧ (∀ lam, 0 ≤ B lam) ∧
        (∫⁻ lam, wL η lam*ENNReal.ofReal (B lam)) < ⊤ ∧
        (∫⁻ lam, wL η lam*ENNReal.ofReal (B lam)) ≤ ENNReal.ofReal (L^(-gamma1 d γ+2*η)) *
          (((ENNReal.ofReal N*(∑' k : ℕ, ENNReal.ofReal (Agev^k*((2*k).factorial:ℝ)/(4*k).factorial)) +
              Fintype.card {j : Fin n // j ∉ J}*ENNReal.ofReal N) +
                ∫⁻ lam, wL (η/4) lam*ENNReal.ofReal (frequencyGaussian lam)) +
            (ENNReal.ofReal N*(∑' k : ℕ, ENNReal.ofReal (Agev^k*((2*k).factorial:ℝ)/(4*k).factorial)) +
                ∫⁻ lam, wL (1-η/8) lam*ENNReal.ofReal (frequencyGaussian lam))) ∧
        ∀ᵐ lam : ℝ × ℝ, ∀ z : (Fin n × Fin 2) → Fin d → ℤ, ∀ β γ' : Fin n → Mom d,
          ‖(((δ/(2*L^((d:ℝ)-γ)))^(2*n):ℝ):ℂ) *
            (approxSum L (L^(2*γ)*δ) (halfCellAmplitude z β γ') (resProfile J (fun Ω => C (ofLp Ω) lam)) -
              approxApp L δ γ J (fun Ω => C (ofLp Ω) lam) (halfCellAmplitude z β γ'))‖ ≤
            ((1+2*Real.pi)*(1+((∑ j, ‖β j‖)+(∑ j, ‖γ' j‖)))*(K*δ/4)^n)*B lam := by
  obtain ⟨K,hK,hMaj⟩ := halfCell_frequency_majorant hd hγ hη0 hη hηγ hηγ'
  refine ⟨K,hK,fun Aorder => ?_⟩
  obtain ⟨L₀,hL₀⟩ := hMaj Aorder
  refine ⟨max L₀ 2,?_⟩
  intro L hL δ hδ hδ1 n hn hnlog J C hC N Agev hN hAgev hmain hper
  have hL0 : 0 < L := lt_of_lt_of_le (by norm_num : (0:ℝ)<2) ((le_max_right _ _).trans hL)
  have hL1 : 1 ≤ L := by linarith [(le_max_right L₀ 2).trans hL]
  obtain ⟨gM,hmM,hiM,hpM,hfM,hbM,hgoodM⟩ := coefficient_NT_normalizer hC
    (by linarith : 0 ≤ η/4) (by linarith : η/4 ≤ 1) (by linarith : η/4 ≤ 1-η/8)
    (by linarith : 0 ≤ 1-η/2) hN hAgev hmain hper
  obtain ⟨gD,hmD,hiD,hpD,hfD,hbD,hgoodD⟩ := derivative_coefficient_NT_normalizer hC
    (by linarith : 0 ≤ 1-η/8) (by linarith : 1-η/8 ≤ 1) hN hAgev hmain
  let B := temporalSplitEnvelope L (gamma1 d γ) η gD gM
  have hmB : Measurable B := measurable_temporalSplitEnvelope _ _ _ hmD hmM
  have hpB (lam : ℝ × ℝ) : 0 ≤ B lam :=
    le_min (hpD lam).le (mul_nonneg (Real.rpow_nonneg hL0.le _) (hpM lam).le)
  have hmass := lintegral_temporalSplitEnvelope_le hL1 (gamma1_le_one d γ) hη0.le hη hmM
    (fun lam => (hpD lam).le) (fun lam => (hpM lam).le)
  refine ⟨B,hmB,hpB,?_,?_,?_⟩
  · exact hmass.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (ENNReal.add_lt_top.mpr ⟨hfM,hfD⟩))
  · exact hmass.trans (mul_le_mul' le_rfl (add_le_add hbM hbD))
  · filter_upwards [hgoodM,hgoodD] with lam hgM hgD
    intro z β γ'
    exact hL₀ L ((le_max_left _ _).trans hL) δ hδ hδ1 n hn hnlog z β γ' J
      (fun Ω => C (ofLp Ω) lam) (gM lam) (gD lam) (hpM lam) (hpD lam)
      hgM.1 hgM.2.1 hgM.2.2 hgD.1 hgD.2

end WaveTurbulence.RegAsymp
