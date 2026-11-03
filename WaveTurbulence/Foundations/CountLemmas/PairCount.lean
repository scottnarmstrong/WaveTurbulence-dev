/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.CountLemmas.HighPairTarget
public import WaveTurbulence.Foundations.CountLemmas.LowPairTarget

/-! # The complete pair half of TARGET Lemma A.8 -/

public section
open Set
namespace WaveTurbulence.CountLemmas

/-- TARGET Lemma A.8, first counting inequality. Only the lower norm
comparison is needed. The outside constant is uniform in δ; the threshold
may depend on its fixed value, exactly as in the audited B1.7 draft. -/
theorem coupledPair_bound (d : ℕ) (hd : 3 ≤ d) (γ : ℝ)
    (hγ : γ ∈ Ioo (0 : ℝ) 1) (c : ℝ) (hc : 1 ≤ c) :
    ∃ C : ℝ, 0 < C ∧ ∀ δ ∈ Ioc (0 : ℝ) 1, ∃ R : ℝ, ∀ L ≥ R,
    ∀ a b r : Mom d, ∀ α β : ℝ, ∀ ξsel : Fin 3, ∀ P : ℝ,
    (P = 0 ∨ P ∈ Icc L⁻¹ 1) → (0 < P → c⁻¹*P ≤ ‖r‖) →
      (coupledPairSet L a b r α β (δ⁻¹*L^(-2*γ)) ξsel).Finite ∧
      ((coupledPairSet L a b r α β (δ⁻¹*L^(-2*γ)) ξsel).ncard : ℝ) ≤
      C*δ⁻¹*L^(2*((d : ℝ)-γ))*(min (Real.log L^2) (1+δ*L^(2*γ)*P))⁻¹ := by
  by_cases hhalf : γ ≤ 1/2
  · obtain ⟨C,R,hC,hb⟩ := coupledPair_low_bound d hd γ hγ hhalf c hc
    refine ⟨C,hC,?_⟩
    intro δ hδ
    have hδp := hδ.1
    refine ⟨max R 1,?_⟩
    intro L hL a b r α β ξsel P hP hr
    have hL1 : 1 ≤ L := (le_max_right R 1).trans hL
    have hLp : 0 < L := lt_of_lt_of_le zero_lt_one hL1
    have hP' : P ∈ Icc (0 : ℝ) 1 := by
      rcases hP with rfl | hP
      · exact ⟨le_rfl,zero_le_one⟩
      · exact ⟨(inv_pos.mpr hLp).le.trans hP.1,hP.2⟩
    exact hb L ((le_max_left R 1).trans hL) δ hδ a b r α β ξsel P hP' hr
  · have hγhalf : (1 : ℝ)/2 < γ := lt_of_not_ge hhalf
    obtain ⟨Cb,Rb,hCb,hbase⟩ := coupledPair_baseline_bound d hd γ hγ
    refine ⟨Cb+1,by positivity,?_⟩
    intro δ hδ
    have hδp := hδ.1
    obtain ⟨Rh,hh⟩ := coupledPair_high_bound d hd γ hγhalf hγ.2 c hc δ hδ
    refine ⟨max Rh (max Rb (max 2 (Real.exp 1))),?_⟩
    intro L hL a b r α β ξsel P hP hr
    have hL2 : 2 ≤ L := (le_max_left 2 (Real.exp 1)).trans
      ((le_max_right Rb _).trans ((le_max_right Rh _).trans hL))
    have hLp : 0 < L := by linarith only [hL2]
    by_cases hPzero : P = 0
    · have hf := finite_coupledPairSet hLp a b r α β (δ⁻¹*L^(-2*γ)) ξsel
      refine ⟨hf,?_⟩
      have hlog : 1 ≤ Real.log L := (Real.le_log_iff_exp_le hLp).mpr
        ((le_max_right 2 (Real.exp 1)).trans ((le_max_right Rb _).trans ((le_max_right Rh _).trans hL)))
      have hlogsq : 1 ≤ Real.log L^2 := by nlinarith only [hlog]
      rw [hPzero,mul_zero,add_zero,min_eq_right hlogsq,inv_one,mul_one]
      have hb := hbase L ((le_max_left Rb _).trans ((le_max_right Rh _).trans hL)) δ hδ a b r α β ξsel
      exact hb.trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (by linarith : Cb ≤ Cb+1) (inv_nonneg.mpr hδ.1.le)) (by positivity))
    · have hP' : P ∈ Icc L⁻¹ 1 := hP.resolve_left hPzero
      have hPp : 0 < P := (inv_pos.mpr hLp).trans_le hP'.1
      obtain ⟨hf,hb⟩ := hh L ((le_max_left Rh _).trans hL) a b r α β ξsel P hP' (hr hPp)
      refine ⟨hf,hb.trans ?_⟩
      have hX : 0 ≤ (min (Real.log L^2) (1+δ*L^(2*γ)*P))⁻¹ := inv_nonneg.mpr
        (le_min (sq_nonneg _) (by have hδp := hδ.1; positivity))
      have hm := mul_le_mul_of_nonneg_left (by linarith : (1 : ℝ) ≤ Cb+1)
        (by positivity : 0 ≤ δ⁻¹*L^(2*((d : ℝ)-γ))*(min (Real.log L^2) (1+δ*L^(2*γ)*P))⁻¹)
      convert hm using 1 <;> ring

end WaveTurbulence.CountLemmas
