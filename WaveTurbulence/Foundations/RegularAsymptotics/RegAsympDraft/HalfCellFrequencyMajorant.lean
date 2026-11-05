/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.RegularAsymptotics.RegAsympDraft.LocalizedApproximation
public import WaveTurbulence.Foundations.RegularAsymptotics.RegAsympDraft.HalfCellCrudeApproximation
public import WaveTurbulence.Foundations.RegAsymp.SymbolLinearity
public import WaveTurbulence.Foundations.RegAsymp.TemporalSplitEnvelope

/-! # One pointwise actual-cell majorant for both temporal frequency regimes -/

public section
noncomputable section
namespace WaveTurbulence.RegAsymp
open ApproxNT MeasureTheory
open scoped ENNReal ContDiff

/-- The two independently normalized J3 profiles produce a common minimum
majorant for the literal remainder. The spatial factor is independent of
the root momentum and appears only once. -/
theorem halfCell_frequency_majorant {d : ℕ} (hd : 3 ≤ d) {γ η : ℝ}
    (hγ : γ ∈ Set.Ioo (0:ℝ) 1) (hη0 : 0 < η) (hη : η ≤ 1/20)
    (hηγ : η ≤ ((d:ℝ)-1)*(1-γ)) (hηγ' : η ≤ γ) :
    ∃ C : ℝ, 0 < C ∧ ∀ A : ℝ, ∃ L₀ : ℝ, ∀ L : ℝ, L₀ ≤ L →
      ∀ δ : ℝ, L ^ (-(η/2)) ≤ δ → δ ≤ 1 → ∀ n : ℕ, 0 < n → (n:ℝ) ≤ Real.log L ^ A →
      ∀ z : (Fin n × Fin 2) → Fin d → ℤ, ∀ β γ' : Fin n → Mom d,
      ∀ (J : Finset (Fin n)) (Ψ : EuclideanSpace ℝ {j // j ∉ J} → ℂ),
      ∀ gM gD : ℝ, 0 < gM → 0 < gD →
      ContDiff ℝ ∞ (fun Ω => gM⁻¹ • Ψ Ω) →
      WordDerivL1 (fun Ω => gM⁻¹ • Ψ Ω) (fun k => ((4*k).factorial:ℝ)) →
      (∫⁻ Ω, ENNReal.ofReal (wmax (1-η/2) (fun i => Ω i))*‖gM⁻¹ • Ψ Ω‖ₑ) ≤ 1 →
      ContDiff ℝ ∞ (fun Ω => gD⁻¹ • Ψ Ω) →
      WordDerivL1 (fun Ω => gD⁻¹ • Ψ Ω) (fun k => ((4*k).factorial:ℝ)) →
      ‖(((δ/(2*L^((d:ℝ)-γ)))^(2*n):ℝ):ℂ) *
        (approxSum L (L^(2*γ)*δ) (halfCellAmplitude z β γ') (resProfile J Ψ) -
          approxApp L δ γ J Ψ (halfCellAmplitude z β γ'))‖ ≤
      ((1+2*Real.pi)*(1+((∑ j, ‖β j‖)+(∑ j, ‖γ' j‖)))*(C*δ/4)^n) *
        min gD (L^(-gamma1 d γ+η)*gM) := by
  obtain ⟨Ce,hCe,hE⟩ := halfCell_normalized_approximation hd hγ hη0 hη hηγ hηγ'
  obtain ⟨Cd,hCd,hD⟩ := halfCell_crude_normalized_approximation hd hγ hη0 hη hηγ hηγ'
  let C := max Ce Cd
  have hC : 0 < C := hCe.trans_le (le_max_left _ _)
  refine ⟨C,hC,fun A => ?_⟩
  obtain ⟨Le,hLe⟩ := hE A
  obtain ⟨Ld,hLd⟩ := hD A
  refine ⟨max (max Le Ld) 2,?_⟩
  intro L hL δ hδ hδ1 n hn hnlog z β γ' J Ψ gM gD hgM hgD hΨM hDM hMM hΨD hDD
  have hLe' : Le ≤ L := (le_max_left _ _).trans ((le_max_left _ _).trans hL)
  have hLd' : Ld ≤ L := (le_max_right _ _).trans ((le_max_left _ _).trans hL)
  have hL0 : 0 < L := lt_of_lt_of_le (by norm_num : (0:ℝ)<2) ((le_max_right _ _).trans hL)
  have hδ0 : 0 < δ := (Real.rpow_pos_of_pos hL0 _).trans_le hδ
  let S := (1+2*Real.pi)*(1+((∑ j, ‖β j‖)+(∑ j, ‖γ' j‖)))
  let T := S*(C*δ/4)^n
  have hS : 0 ≤ S := by dsimp only [S]; positivity
  have hT : 0 ≤ T := by dsimp only [T]; positivity
  have hc (c : ℝ) (hc0 : 0 < c) (hcC : c ≤ C) : S*(c*δ/4)^n ≤ T := by
    apply mul_le_mul_of_nonneg_left _ hS
    exact pow_le_pow_left₀ (by positivity) (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right hcC hδ0.le) (by norm_num : 0 ≤ (4:ℝ))) n
  have he := hLe L hLe' δ hδ hδ1 n hn hnlog z β γ' J (fun Ω => gM⁻¹ • Ψ Ω) hΨM hDM hMM
  have hd := hLd L hLd' δ hδ hδ1 n hn hnlog z β γ' J (fun Ω => gD⁻¹ • Ψ Ω) hΨD hDD
  have hm1 : ‖(((δ/(2*L^((d:ℝ)-γ)))^(2*n):ℝ):ℂ) *
      (approxSum L (L^(2*γ)*δ) (halfCellAmplitude z β γ') (resProfile J Ψ) -
        approxApp L δ γ J Ψ (halfCellAmplitude z β γ'))‖ ≤ T*(L^(-gamma1 d γ+η)*gM) := by
    rw [normalized_remainder_norm L δ γ J Ψ (halfCellAmplitude z β γ') _ hgM]
    have hh := mul_le_mul_of_nonneg_left he hgM.le
    have hpow := mul_le_mul_of_nonneg_right (hc Ce hCe (le_max_left _ _))
      (Real.rpow_nonneg hL0.le (-gamma1 d γ+η))
    have hb := hh.trans (mul_le_mul_of_nonneg_left hpow hgM.le)
    simpa only [S,mul_assoc,mul_left_comm,mul_comm] using hb
  have hm2 : ‖(((δ/(2*L^((d:ℝ)-γ)))^(2*n):ℝ):ℂ) *
      (approxSum L (L^(2*γ)*δ) (halfCellAmplitude z β γ') (resProfile J Ψ) -
        approxApp L δ γ J Ψ (halfCellAmplitude z β γ'))‖ ≤ T*gD := by
    rw [normalized_remainder_norm L δ γ J Ψ (halfCellAmplitude z β γ') _ hgD]
    have hh := mul_le_mul_of_nonneg_left hd hgD.le
    have hb := hh.trans (mul_le_mul_of_nonneg_left (hc Cd hCd (le_max_right _ _)) hgD.le)
    simpa only [S,mul_comm] using hb
  rw [mul_min_of_nonneg _ _ hT]
  exact le_min hm2 hm1

end WaveTurbulence.RegAsymp
