/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.WeylSums.CubicStarIntegralReduction
public import WaveTurbulence.Foundations.WeylSums.CubicStarWeylIntegralHigh
public import WaveTurbulence.Foundations.WeylSums.CubicChainTarget

/-! # TARGET lemcubic for the shared-vertex phase in dimension at least four -/

public section
open MeasureTheory Set
namespace WaveTurbulence.WeylSums

/-- The shared-vertex phase has the target bound in all dimensions `d≥4`. -/
theorem quadExpSum3_true_bound_high (d : ℕ) (hd : 4 ≤ d) (γ : ℝ)
    (hγ : γ ∈ Ioo (0 : ℝ) 1) (T₀ : ℝ) (hT₀ : 0 < T₀) :
    ∃ C L₀ : ℝ, ∀ L ≥ L₀, ∀ a b c ξ ζ ω : Mom d,
      (∫ ts : ℝ × ℝ in timeSquareWindow L (T₀*L^(2*γ)),
        ‖cubicLatticeSum L ts.1 ts.2 true a b c ξ ζ ω‖) ≤
        C*L^(3*(d : ℝ)+γ-2*min γ (1-γ))*Real.log L := by
  let ε : ℝ := 1/100
  let p : ℝ := (d : ℝ)-4+2*ε
  obtain ⟨C₀,hC₀,hred⟩ := exists_cubicStar_integral_reduction
  obtain ⟨C₁,hC₁,hweyl⟩ := exists_cubicStar_weyl_integral_bound_high d hd ε (by norm_num [ε]) (by norm_num [ε])
  obtain ⟨R,hR,hupper⟩ := exists_upper_time_le_square hT₀ hγ.2
  let K := C₀^d*C₁*(16*(12 : ℝ)^p*(T₀/4))
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
  obtain ⟨hi,hb⟩ := hweyl (12*L) (L/(4*L^2)) (T₀*L^(2*γ)/(4*L^2))
    (by linarith) hA hT hT1
  have hh := (hred d L (T₀*L^(2*γ)) hL1 hi a b c ξ ζ ω).2
  have hbound : (∫ ts : ℝ × ℝ in timeSquareWindow L (T₀*L^(2*γ)),
      ‖cubicLatticeSum L ts.1 ts.2 true a b c ξ ζ ω‖) ≤
      C₀^d*L^(2*d)*(4*L^2)^2*(C₁*(12*L)^p*(T₀*L^(2*γ)/(4*L^2))) :=
    hh.trans (mul_le_mul_of_nonneg_left hb (by positivity))
  have hLnat : L^(2*d) = L^(2*(d : ℝ)) := by
    rw [← Real.rpow_natCast]
    congr 1
    push_cast
    ring
  have hJac : (4*L^2)^2 = 16*L^(4 : ℝ) := by rw [show L^(4 : ℝ) = L^4 by norm_cast]; ring
  have hLP : L^(2*(d : ℝ))*L^(4 : ℝ)*L^p*L^(2*γ-2) = L^(3*(d : ℝ)+2*γ-2+2*ε) := by
    rw [← Real.rpow_add hLp,← Real.rpow_add hLp,← Real.rpow_add hLp]
    congr 1
    dsimp [p]
    ring
  have hscale : C₀^d*L^(2*d)*(4*L^2)^2*(C₁*(12*L)^p*(T₀*L^(2*γ)/(4*L^2))) =
      K*L^(3*(d : ℝ)+2*γ-2+2*ε) := by
    rw [hLnat,hJac,Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 12) hLp.le,upper_time_window_power hLp]
    calc
      _ = K*(L^(2*(d : ℝ))*L^(4 : ℝ)*L^p*L^(2*γ-2)) := by dsimp [K]; ring
      _ = _ := by rw [hLP]
  have hexp : 3*(d : ℝ)+2*γ-2+2*ε ≤ 3*(d : ℝ)+γ-2*min γ (1-γ) := by
    by_cases hg : γ ≤ 1-γ
    · rw [min_eq_left hg]
      dsimp [ε]
      linarith only [hg]
    · rw [min_eq_right (le_of_not_ge hg)]
      dsimp [ε]
      linarith only [le_of_not_ge hg]
  have hlog : 1 ≤ Real.log L := by
    have hh := Real.log_le_log (Real.exp_pos 1) ((le_max_right _ _).trans hL)
    simpa only [Real.log_exp] using hh
  rw [hscale] at hbound
  exact (hbound.trans (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hL1 hexp) hK)).trans
    (le_mul_of_one_le_right (mul_nonneg hK (by positivity)) hlog)

end WaveTurbulence.WeylSums
