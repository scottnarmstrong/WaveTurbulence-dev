/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.MoleProp.K4CountFibers
public import WaveTurbulence.Foundations.FinalCount.MoleProp.K4CountPowers
import Mathlib.Tactic

/-! # The actual small-sphere height factor has a strict gamma-zero margin

The square-root error from lattice floor cells is controlled at the source
threshold M=L^(1−γ₀/10). Keeping one full δ inverse avoids any hidden
constant dependence on δ.
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.MoleProp

/-- The genuine planar height factor at the source radius threshold has
extra γ₀/20 saving, uniformly for all fixed δ in (0,1]. -/
theorem k4_small_height_factor_le {L δ γ : ℝ} (hL : 1 ≤ L)
    (hδ : δ ∈ Set.Ioc (0 : ℝ) 1) (hγ : 0 < γ) (hγ1 : γ < 1) :
    2*Real.sqrt (2*(L^2*(2*(δ⁻¹*L^(-2*γ)))+
      4*(L*L^(1-min γ (1-γ)/10))+1))+2 ≤
      10*δ⁻¹*L^(1-min γ (1-γ)/20) := by
  have hLp : 0 < L := zero_lt_one.trans_le hL
  have hδi : 1 ≤ δ⁻¹ := (one_le_inv₀ hδ.1).mpr hδ.2
  have hδ0 : 0 ≤ δ⁻¹ := inv_nonneg.mpr hδ.1.le
  let g := min γ (1-γ)
  have hg0 : 0 ≤ g := le_min hγ.le (by linarith only [hγ1])
  have hgγ : g ≤ γ := min_le_left _ _
  have hg1 : g ≤ 1 := (min_le_right γ (1-γ)).trans (by linarith only [hγ])
  let P := L^(2-g/10)
  let S := δ⁻¹*P
  have hP0 : 0 ≤ P := Real.rpow_nonneg hLp.le _
  have hP1 : 1 ≤ P := Real.one_le_rpow hL (by linarith only [hg1])
  have hS1 : 1 ≤ S := one_le_mul_of_one_le_of_one_le hδi hP1
  have hS0 : 0 ≤ S := zero_le_one.trans hS1
  have hW : L^2*(2*(δ⁻¹*L^(-2*γ))) ≤ 2*S := by
    have he : L^2*(2*(δ⁻¹*L^(-2*γ))) = 2*δ⁻¹*L^(2-2*γ) := by
      calc
        _ = 2*δ⁻¹*(L^2*L^(-2*γ)) := by ring
        _ = _ := by
          rw [← Real.rpow_two,← Real.rpow_add hLp]
          congr 2
          ring
    rw [he]
    have hp : L^(2-2*γ) ≤ P := Real.rpow_le_rpow_of_exponent_le hL (by linarith only [hgγ,hγ])
    simpa only [S,mul_assoc] using mul_le_mul_of_nonneg_left hp (by positivity : 0 ≤ 2*δ⁻¹)
  have hLM : L*L^(1-g/10) ≤ S := by
    have he : L*L^(1-g/10)=P := by
      calc
        _ = L^(1 : ℝ)*L^(1-g/10) := by rw [Real.rpow_one]
        _ = L^((1 : ℝ)+(1-g/10)) := (Real.rpow_add hLp _ _).symm
        _ = P := by dsimp only [P]; congr 1; ring
    rw [he]
    have hh := mul_le_mul_of_nonneg_right hδi hP0
    simpa only [one_mul,S] using hh
  have hinside : 2*(L^2*(2*(δ⁻¹*L^(-2*γ)))+4*(L*L^(1-g/10))+1) ≤ 16*S := by
    linarith only [hW,hLM,hS1]
  have hsqrt : Real.sqrt (2*(L^2*(2*(δ⁻¹*L^(-2*γ)))+4*(L*L^(1-g/10))+1)) ≤ 4*Real.sqrt S := by
    apply (Real.sqrt_le_iff).mpr
    refine ⟨by positivity,?_⟩
    nlinarith only [hinside,Real.sq_sqrt hS0]
  have hroot1 : 1 ≤ Real.sqrt S := by
    nlinarith only [Real.sq_sqrt hS0,Real.sqrt_nonneg S,hS1]
  have hheight : 2*Real.sqrt (2*(L^2*(2*(δ⁻¹*L^(-2*γ)))+4*(L*L^(1-g/10))+1))+2 ≤ 10*Real.sqrt S := by
    linarith only [hsqrt,hroot1]
  have hpow : (L^(1-g/20))^2=P := by
    rw [← Real.rpow_mul_natCast hLp.le]
    dsimp only [P]
    congr 1
    ring
  have hroot : Real.sqrt S ≤ δ⁻¹*L^(1-g/20) := by
    apply (Real.sqrt_le_iff).mpr
    refine ⟨by positivity,?_⟩
    rw [mul_pow,hpow]
    have hδsq : δ⁻¹ ≤ (δ⁻¹)^2 := by nlinarith only [hδi]
    exact mul_le_mul_of_nonneg_right hδsq hP0
  exact hheight.trans (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hroot (by norm_num : (0 : ℝ)≤10))

end WaveTurbulence.MoleProp
