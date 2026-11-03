/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.WeylSums.CubicStarIntegralReduction
public import WaveTurbulence.Foundations.WeylSums.CubicStarWeylIntegralThree
public import WaveTurbulence.Foundations.WeylSums.CubicChainTarget
public import WaveTurbulence.Foundations.WeylSums.CubicStarScale

/-! # TARGET lemcubic for the shared-vertex phase in dimension three -/

public section
open MeasureTheory Set
namespace WaveTurbulence.WeylSums

/-- The dimension-three shared-vertex bound retains an arbitrarily small
loss below the positive margin `1-γ`. -/
theorem quadExpSum3_true_bound_three (γ : ℝ) (hγ : γ ∈ Ioo (0 : ℝ) 1)
    (T₀ : ℝ) (hT₀ : 0 < T₀) :
    ∃ C L₀ : ℝ, ∀ L ≥ L₀, ∀ a b c ξ ζ ω : Mom 3,
      (∫ ts : ℝ × ℝ in timeSquareWindow L (T₀*L^(2*γ)),
        ‖cubicLatticeSum L ts.1 ts.2 true a b c ξ ζ ω‖) ≤
        C*L^(3*(3 : ℝ)+γ-2*min γ (1-γ))*Real.log L := by
  let ε := min (1/100 : ℝ) ((1-γ)/100)
  have hε : 0 < ε := lt_min (by norm_num) (by linarith only [hγ.2])
  have hεsmall : ε ≤ 1/100 := min_le_left _ _
  have hεγ : 2*ε ≤ 1-γ := by have hh := min_le_right (1/100 : ℝ) ((1-γ)/100); linarith only [hh,hγ.2]
  obtain ⟨C₀,hC₀,hred⟩ := exists_cubicStar_integral_reduction
  obtain ⟨C₁,hC₁,hweyl⟩ := exists_cubicStar_weyl_integral_bound_three ε hε (by linarith)
  obtain ⟨R,hR,hupper⟩ := exists_upper_time_le_square hT₀ hγ.2
  let K₁ := 16*(12 : ℝ)^(2*ε)*(T₀/4)^2
  let K₂ := 16*(12 : ℝ)^(-1+4*ε)*(T₀/4)
  let K := (C₀^3*C₁)*(K₁+K₂)
  have hK₁ : 0 ≤ K₁ := by dsimp [K₁]; positivity
  have hK₂ : 0 ≤ K₂ := by dsimp [K₂]; positivity
  have hK : 0 ≤ K := by dsimp [K]; positivity
  refine ⟨K,max R (Real.exp 1),?_⟩
  intro L hL a b c ξ ζ ω
  have hLR : R ≤ L := (le_max_left _ _).trans hL
  have hL2 : 2 ≤ L := hR.trans hLR
  have hL1 : 1 ≤ L := by linarith
  have hLp : 0 < L := by linarith
  have hMp : 0 < 12*L := by positivity
  have hJ : 0 < 4*L^2 := by positivity
  have hB : 0 < T₀*L^(2*γ) := by positivity
  have hT : 0 < T₀*L^(2*γ)/(4*L^2) := div_pos hB hJ
  have hT1 : T₀*L^(2*γ)/(4*L^2) ≤ 1 := by
    apply (div_le_iff₀ hJ).mpr
    nlinarith only [hupper L hLR,sq_nonneg L]
  have hA : 1/(12*L) < L/(4*L^2) := by
    apply (div_lt_div_iff₀ hMp hJ).mpr
    nlinarith only [sq_pos_of_pos hLp]
  obtain ⟨hi,hb⟩ := hweyl (12*L) (L/(4*L^2)) (T₀*L^(2*γ)/(4*L^2)) (by linarith) hA hT hT1
  have hh := (hred 3 L (T₀*L^(2*γ)) hL1 hi a b c ξ ζ ω).2
  have hraw := hh.trans (mul_le_mul_of_nonneg_left hb (by positivity))
  have hs₁ := cubic_star_physical_scale hLp hT₀.le 3 γ (2*ε) 2
  norm_num only [Nat.cast_ofNat,Real.rpow_two] at hs₁
  rw [show (10 : ℝ)+2*ε+(2*γ-2)*2 = 6+4*γ+2*ε by ring] at hs₁
  have hs₂ := cubic_star_physical_scale hLp hT₀.le 3 γ (-1+4*ε) 1
  norm_num only [Nat.cast_ofNat,Real.rpow_one] at hs₂
  rw [show (10 : ℝ)+(-1+4*ε)+(2*γ-2)*1 = 7+2*γ+4*ε by ring] at hs₂
  have hscale : C₀^3*L^(2*3)*(4*L^2)^2*
      (C₁*((12*L)^(2*ε)*(T₀*L^(2*γ)/(4*L^2))^2+(12*L)^(-1+4*ε)*(T₀*L^(2*γ)/(4*L^2)))) =
      (C₀^3*C₁)*(K₁*L^(6+4*γ+2*ε)+K₂*L^(7+2*γ+4*ε)) := by
    calc
      _ = (C₀^3*C₁)*
          (L^(2*3)*(4*L^2)^2*(12*L)^(2*ε)*(T₀*L^(2*γ)/(4*L^2))^2+
            L^(2*3)*(4*L^2)^2*(12*L)^(-1+4*ε)*(T₀*L^(2*γ)/(4*L^2))) := by ring
      _ = _ := by rw [hs₁,hs₂]
  rw [hscale] at hraw
  have hexp₁ : 6+4*γ+2*ε ≤ 3*(3 : ℝ)+γ-2*min γ (1-γ) := by
    by_cases hg : γ ≤ 1-γ
    · rw [min_eq_left hg]
      linarith only [hg,hεsmall]
    · rw [min_eq_right (le_of_not_ge hg)]
      linarith only [hεγ]
  have hexp₂ : 7+2*γ+4*ε ≤ 3*(3 : ℝ)+γ-2*min γ (1-γ) := by
    by_cases hg : γ ≤ 1-γ
    · rw [min_eq_left hg]
      linarith only [hg,hεsmall]
    · rw [min_eq_right (le_of_not_ge hg)]
      linarith only [le_of_not_ge hg,hεsmall]
  have hlog : 1 ≤ Real.log L := by
    have hh := Real.log_le_log (Real.exp_pos 1) ((le_max_right _ _).trans hL)
    simpa only [Real.log_exp] using hh
  have htarget : (C₀^3*C₁)*(K₁*L^(6+4*γ+2*ε)+K₂*L^(7+2*γ+4*ε)) ≤
      K*L^(3*(3 : ℝ)+γ-2*min γ (1-γ)) := by
    calc
      _ ≤ (C₀^3*C₁)*(K₁*L^(3*(3 : ℝ)+γ-2*min γ (1-γ))+K₂*L^(3*(3 : ℝ)+γ-2*min γ (1-γ))) :=
        mul_le_mul_of_nonneg_left (add_le_add
          (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hL1 hexp₁) hK₁)
          (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hL1 hexp₂) hK₂)) (by positivity)
      _ = _ := by dsimp [K]; ring
  exact (hraw.trans htarget).trans (le_mul_of_one_le_right (mul_nonneg hK (by positivity)) hlog)

end WaveTurbulence.WeylSums
