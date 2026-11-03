/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.CountLemmas.HighPairSelectors
public import WaveTurbulence.Foundations.CountLemmas.CoupledSets

/-! # The exact capped pair gain for γ>1/2 -/

public section
open Set
namespace WaveTurbulence.CountLemmas

/-- TARGET Lemma A.8, first inequality, above the transition. The strong
inverse-log bound dominates the smaller capped gain for every positive P. -/
theorem coupledPair_high_bound (d : ℕ) (hd : 3 ≤ d) (γ : ℝ)
    (hγ : (1 : ℝ)/2 < γ) (hγ1 : γ < 1) (c : ℝ) (hc : 1 ≤ c) :
    ∀ δ ∈ Ioc (0 : ℝ) 1, ∃ R : ℝ, ∀ L ≥ R,
    ∀ a b r : Mom d, ∀ α β : ℝ, ∀ ξsel : Fin 3, ∀ P ∈ Icc L⁻¹ 1,
    c⁻¹*P ≤ ‖r‖ →
      (coupledPairSet L a b r α β (δ⁻¹*L^(-2*γ)) ξsel).Finite ∧
      ((coupledPairSet L a b r α β (δ⁻¹*L^(-2*γ)) ξsel).ncard : ℝ) ≤
      δ⁻¹*L^(2*((d : ℝ)-γ))*(min (Real.log L^2) (1+δ*L^(2*γ)*P))⁻¹ := by
  intro δ hδ
  have hδp := hδ.1
  have hcpos : 0 < c := lt_of_lt_of_le zero_lt_one hc
  obtain ⟨R,hR⟩ := exists_high_pair_selector_bound d hd c γ hcpos hγ hγ1 δ hδ.1
  refine ⟨max R (max 2 (Real.exp 1)),?_⟩
  intro L hL a b r α β ξsel P hP hr
  have hL2 : 2 ≤ L := (le_max_left 2 (Real.exp 1)).trans ((le_max_right R _).trans hL)
  have hLp : 0 < L := by linarith only [hL2]
  have hlog : 1 ≤ Real.log L := (Real.le_log_iff_exp_le hLp).mpr
    ((le_max_right 2 (Real.exp 1)).trans ((le_max_right R _).trans hL))
  have hlogsq : 1 ≤ Real.log L^2 := by nlinarith only [hlog]
  have hPp : 0 < P := (inv_pos.mpr hLp).trans_le hP.1
  let X := min (Real.log L^2) (1+δ*L^(2*γ)*P)
  have hX : 0 < X := lt_of_lt_of_le zero_lt_one (le_min hlogsq (by
    have hh : 0 ≤ δ*L^(2*γ)*P := by positivity
    linarith only [hh]))
  have hgap : c⁻¹*L⁻¹ ≤ ‖r‖ :=
    (mul_le_mul_of_nonneg_left hP.1 (inv_nonneg.mpr hcpos.le)).trans hr
  have hf := finite_coupledPairSet hLp a b r α β (δ⁻¹*L^(-2*γ)) ξsel
  refine ⟨hf,?_⟩
  have hb := hR L ((le_max_left R _).trans hL) a b r α β hgap ξsel hf.toFinset
    (fun q hq => hf.mem_toFinset.mp hq)
  rw [← Set.ncard_eq_toFinset_card _ hf] at hb
  have hden : L^(2*((d : ℝ)-γ))/(Real.log L)^2 ≤ L^(2*((d : ℝ)-γ))/X :=
    div_le_div_of_nonneg_left (by positivity) hX (min_le_left _ _)
  have hδi : 1 ≤ δ⁻¹ := (one_le_inv₀ hδ.1).mpr hδ.2
  have hh := hb.trans hden
  have hm := mul_le_mul_of_nonneg_right hδi (by positivity : 0 ≤ L^(2*((d : ℝ)-γ))/X)
  apply hh.trans
  simpa only [one_mul,div_eq_mul_inv,mul_assoc,X] using hm

end WaveTurbulence.CountLemmas
