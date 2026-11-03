/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.WeylSums.CubicChainIntegral
public import WaveTurbulence.Foundations.WeylSums.MinorArcExponents
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! # TARGET lemcubic for the cubic-chain phase -/

public section
open MeasureTheory Set Filter
namespace WaveTurbulence.WeylSums

/-- The source upper time scale eventually lies below the square lattice scale. -/
theorem exists_upper_time_le_square {T₀ γ : ℝ} (hT₀ : 0 < T₀) (hγ : γ < 1) :
    ∃ L₀ : ℝ, 2 ≤ L₀ ∧ ∀ L ≥ L₀, T₀*L^(2*γ) ≤ L^2 := by
  have ht := tendsto_rpow_neg_atTop (by linarith : 0 < 2-2*γ)
  have he : ∀ᶠ L : ℝ in atTop, L^(-(2-2*γ)) < 1/T₀ :=
    ht.eventually (Iio_mem_nhds (by positivity))
  obtain ⟨R,hR⟩ := eventually_atTop.mp he
  refine ⟨max 2 R,le_max_left _ _,?_⟩
  intro L hL
  have hLp : 0 < L := by have := (le_max_left 2 R).trans hL; linarith
  have hh := hR L ((le_max_right _ _).trans hL)
  rw [show -(2-2*γ) = 2*γ-2 by ring,Real.rpow_sub hLp,Real.rpow_two] at hh
  have hsq : 0 < L^2 := sq_pos_of_pos hLp
  have hmul := (lt_div_iff₀ hT₀).mp hh
  have hdiv : (T₀*L^(2*γ))/L^2 < 1 := by simpa only [div_mul_eq_mul_div,mul_comm T₀] using hmul
  simpa only [one_mul] using ((div_lt_iff₀ hsq).mp hdiv).le

/-- The `T^(2/3)` gain is stronger than the target cubic-chain power. -/
theorem cubic_chain_exponent_le {γ : ℝ} (_hγ : γ ∈ Ioo (0 : ℝ) 1) :
    (2*γ-2)*((2 : ℝ)/3) ≤ γ-2*min γ (1-γ) := by
  by_cases h : γ ≤ 1-γ
  · rw [min_eq_left h]
    linarith only [h]
  · rw [min_eq_right (le_of_not_ge h)]
    linarith only [le_of_not_ge h]

/-- TARGET `lemcubic` for `Λ=z·(x+y-z)`, with the exact six-vector and time
quantifiers of the audited `quadExpSum3` draft. -/
theorem quadExpSum3_false_bound :
    ∀ d : ℕ, 3 ≤ d → ∀ γ : ℝ, γ ∈ Ioo (0 : ℝ) 1 → ∀ T₀ : ℝ, 0 < T₀ →
      ∃ C L₀ : ℝ, ∀ L ≥ L₀, ∀ a b c ξ ζ ω : Mom d,
      (∫ ts : ℝ × ℝ in timeSquareWindow L (T₀*L^(2*γ)),
        ‖cubicLatticeSum L ts.1 ts.2 false a b c ξ ζ ω‖) ≤
        C*L^(3*(d : ℝ)+γ-2*min γ (1-γ))*Real.log L := by
  intro d hd γ hγ T₀ hT₀
  obtain ⟨C,hC,hb⟩ := exists_cubicChain_integral_bound d hd
  obtain ⟨R,hR,hupper⟩ := exists_upper_time_le_square hT₀ hγ.2
  let A := C*(T₀/4)^((2 : ℝ)/3)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  refine ⟨A,max R (Real.exp 1),?_⟩
  intro L hL a b c ξ ζ ω
  have hLR : R ≤ L := (le_max_left _ _).trans hL
  have hL2 : 2 ≤ L := hR.trans hLR
  have hL1 : 1 ≤ L := by linarith
  have hLp : 0 < L := by linarith
  have hlog : 1 ≤ Real.log L := by
    have hh := Real.log_le_log (Real.exp_pos 1) ((le_max_right _ _).trans hL)
    simpa only [Real.log_exp] using hh
  have hh := (hb L (T₀*L^(2*γ)) hL2 (by positivity) (hupper L hLR) a b c ξ ζ ω).2
  calc
    _ ≤ C*L^(3*(d : ℝ))*(T₀*L^(2*γ)/(4*L^2))^((2 : ℝ)/3) := hh
    _ = A*L^(3*(d : ℝ)+(2*γ-2)*((2 : ℝ)/3)) := by
      rw [upper_time_window_power hLp,Real.mul_rpow (by positivity : (0 : ℝ) ≤ T₀/4) (by positivity),
        ← Real.rpow_mul hLp.le,Real.rpow_add hLp]
      dsimp [A]
      ring
    _ ≤ A*L^(3*(d : ℝ)+γ-2*min γ (1-γ)) := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hL1 (by linarith only [cubic_chain_exponent_le hγ])) hA
    _ ≤ _ := le_mul_of_one_le_right (mul_nonneg hA (by positivity)) hlog

end WaveTurbulence.WeylSums
