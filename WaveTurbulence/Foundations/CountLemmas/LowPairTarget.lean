/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.CountLemmas.LowPairSelectors
public import WaveTurbulence.Foundations.CountLemmas.PairBaseline
public import WaveTurbulence.Foundations.CountLemmas.TwoBranchGain
public import WaveTurbulence.Foundations.CountLemmas.StarMonomials

/-! # The exact capped pair gain for γ≤1/2 -/

public section
open Set
namespace WaveTurbulence.CountLemmas

/-- TARGET Lemma A.8, first inequality, below and at the transition γ=1/2.
The norm comparison is the only information about r needed in this regime. -/
theorem coupledPair_low_bound (d : ℕ) (hd : 3 ≤ d) (γ : ℝ)
    (hγ : γ ∈ Ioo (0 : ℝ) 1) (hγhalf : γ ≤ 1/2) (c : ℝ) (hc : 1 ≤ c) :
    ∃ C R : ℝ, 0 < C ∧ ∀ L ≥ R, ∀ δ ∈ Ioc (0 : ℝ) 1,
    ∀ a b r : Mom d, ∀ α β : ℝ, ∀ ξsel : Fin 3, ∀ P ∈ Icc (0 : ℝ) 1,
    (0 < P → c⁻¹*P ≤ ‖r‖) →
      (coupledPairSet L a b r α β (δ⁻¹*L^(-2*γ)) ξsel).Finite ∧
      ((coupledPairSet L a b r α β (δ⁻¹*L^(-2*γ)) ξsel).ncard : ℝ) ≤
      C*δ⁻¹*L^(2*((d : ℝ)-γ))*(min (Real.log L^2) (1+δ*L^(2*γ)*P))⁻¹ := by
  obtain ⟨Cb,R,hCb,hbase⟩ := coupledPair_baseline_bound d hd γ hγ
  obtain ⟨Cl,hCl,hstrip⟩ := exists_low_pair_selector_bound d hd c hc
  refine ⟨Cb+Cl,max R (max 2 (Real.exp 1)),by positivity,?_⟩
  intro L hL δ hδ a b r α β ξsel P hP hr
  have hL2 : 2 ≤ L := (le_max_left 2 (Real.exp 1)).trans ((le_max_right R _).trans hL)
  have hL1 : 1 ≤ L := by linarith only [hL2]
  have hLp : 0 < L := by linarith only [hL2]
  have hlog : 1 ≤ Real.log L := (Real.le_log_iff_exp_le hLp).mpr
    ((le_max_right 2 (Real.exp 1)).trans ((le_max_right R _).trans hL))
  have hlogsq : 1 ≤ Real.log L^2 := by nlinarith only [hlog]
  let τ := δ⁻¹*L^(-2*γ)
  let V := τ*L^(2*(d : ℝ))
  let X := min (Real.log L^2) (1+δ*L^(2*γ)*P)
  have hτ : 0 < τ := mul_pos (inv_pos.mpr hδ.1) (Real.rpow_pos_of_pos hLp _)
  have hV : 0 ≤ V := by dsimp only [V]; positivity
  have hδi : 1 ≤ δ⁻¹ := (one_le_inv₀ hδ.1).mpr hδ.2
  have hτL : 1 ≤ τ*L := by
    have hid : τ*L = δ⁻¹*L^(1-2*γ) := by
      simpa only [Real.rpow_one] using bandwidth_mul_rpow hLp δ γ 1
    rw [hid]
    exact one_le_mul_of_one_le_of_one_le hδi (Real.one_le_rpow hL1 (by linarith only [hγhalf]))
  have hVeq : V = δ⁻¹*L^(2*((d : ℝ)-γ)) := by
    rw [show V = (δ⁻¹*L^(-2*γ))*L^(2*(d : ℝ)) from rfl,bandwidth_mul_rpow hLp]
    congr 2
    ring
  have hX : 0 < X := lt_of_lt_of_le zero_lt_one (le_min hlogsq (by
    have hh : 0 ≤ δ*L^(2*γ)*P := mul_nonneg (mul_nonneg hδ.1.le (by positivity)) hP.1
    linarith only [hh]))
  have hf := finite_coupledPairSet hLp a b r α β τ ξsel
  refine ⟨hf,?_⟩
  have hb : ((coupledPairSet L a b r α β τ ξsel).ncard : ℝ) ≤ Cb*V := by
    rw [hVeq]
    simpa only [mul_assoc] using hbase L ((le_max_left R _).trans hL) δ hδ a b r α β ξsel
  have hfin : ((coupledPairSet L a b r α β τ ξsel).ncard : ℝ) ≤ (Cb+Cl)*V*X⁻¹ := by
    by_cases hPzero : P = 0
    · have hXone : X = 1 := by dsimp only [X]; rw [hPzero,mul_zero,add_zero,min_eq_right hlogsq]
      rw [hXone,inv_one,mul_one]
      exact hb.trans (mul_le_mul_of_nonneg_right (by linarith only [hCl] : Cb ≤ Cb+Cl) hV)
    · have hPp : 0 < P := lt_of_le_of_ne hP.1 (Ne.symm hPzero)
      have hs := hstrip L τ P hL1 hτL hPp hP.2 a b r α β (hr hPp) ξsel hf.toFinset
        (fun q hq => hf.mem_toFinset.mp hq)
      have hs' : ((coupledPairSet L a b r α β τ ξsel).ncard : ℝ) ≤ Cl*(τ*V/P) := by
        rw [Set.ncard_eq_toFinset_card _ hf]
        have hid : τ^2*L^(2*d)/P = τ*V/P := by
          dsimp only [V]
          rw [show L^(2*(d : ℝ)) = L^(2*d) by norm_cast]
          ring
        simpa only [hid] using hs
      have hinv : P/τ = δ*L^(2*γ)*P := by
        dsimp only [τ]
        rw [show -2*γ = -(2*γ) by ring,Real.rpow_neg hLp.le]
        field_simp [hδ.1.ne',(Real.rpow_pos_of_pos hLp (2*γ)).ne']
      exact two_branch_gain (Nat.cast_nonneg _) hτ hPp hX
        (by rw [hinv]; exact min_le_right _ _) hb hs'
  simpa only [hVeq,τ,X,mul_assoc] using hfin

end WaveTurbulence.CountLemmas
