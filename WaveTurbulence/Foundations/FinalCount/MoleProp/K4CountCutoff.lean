/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.MoleProp.K4CountPowers
import Mathlib.Tactic

/-! # The actual coefficient cutoff pays the retained lattice-boundary term

For high gamma only the boundary contribution needs the cutoff
R≤L^(1−2γ). The volume contributions have enough power directly.
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.MoleProp

noncomputable def k4CoefficientCut (L γ : ℝ) : ℝ :=
  if γ ≤ 1/2 then 1 else L^(1-2*γ)

theorem k4_coefficient_cut_pos {L γ : ℝ} (hL : 0 < L) : 0 < k4CoefficientCut L γ := by
  unfold k4CoefficientCut
  split_ifs <;> positivity

theorem k4_coefficient_cut_le_one {L γ : ℝ} (hL : 1 ≤ L) : k4CoefficientCut L γ ≤ 1 := by
  unfold k4CoefficientCut
  split_ifs with h
  · exact le_rfl
  · have hh := Real.rpow_le_rpow_of_exponent_le hL (by linarith only [h] : 1-2*γ ≤ 0)
    simpa only [Real.rpow_zero] using hh

/-- All three actual radial monomials fit the same strict saving after
the source coefficient cutoff, leaving two positive summable powers. -/
theorem k4_cutoff_three_term_le (d : ℕ) (hd : 1 ≤ d) {L R γ : ℝ}
    (hL : 1 ≤ L) (hR : 0 ≤ R) (hcut : R ≤ k4CoefficientCut L γ) :
    L^(3*(d : ℝ)-4*γ-min γ (1-γ)/20)*R^(d-2)+
      L^(3*(d : ℝ)-2*γ-1-min γ (1-γ)/20)*R^(d-1)+
      L^(3*(d : ℝ)-2-min γ (1-γ)/20)*R^d ≤
    L^(3*((d : ℝ)-γ)-(21 : ℝ)/20*min γ (1-γ))*(R^(d-2)+2*R^(d-1)) := by
  have hLp : 0 < L := zero_lt_one.trans_le hL
  let E := 3*((d : ℝ)-γ)-(21 : ℝ)/20*min γ (1-γ)
  have hpow : R^d=R^(d-1)*R := by rw [← pow_succ,Nat.sub_add_cancel hd]
  by_cases hh : γ ≤ 1/2
  · have hmin : min γ (1-γ)=γ := min_eq_left (by linarith only [hh])
    have hR1 : R ≤ 1 := by simpa only [k4CoefficientCut,ite_eq_left hh] using hcut
    have he1 : 3*(d : ℝ)-4*γ-min γ (1-γ)/20=E := by simp only [E,hmin] <;> ring
    have he2 : 3*(d : ℝ)-2*γ-1-min γ (1-γ)/20 ≤ E := by dsimp only [E]; rw [hmin]; linarith only [hh]
    have he3 : 3*(d : ℝ)-2-min γ (1-γ)/20 ≤ E := by dsimp only [E]; rw [hmin]; linarith only [hh]
    have h2 := mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_le hL he2) (pow_nonneg hR (d-1))
    have hRp : R^d ≤ R^(d-1) := by rw [hpow]; simpa only [mul_one] using mul_le_mul_of_nonneg_left hR1 (pow_nonneg hR (d-1))
    have h3 := mul_le_mul (Real.rpow_le_rpow_of_exponent_le hL he3) hRp (pow_nonneg hR d) (Real.rpow_nonneg hLp.le E)
    rw [he1]
    nlinarith only [h2,h3]
  · have hmin : min γ (1-γ)=1-γ := min_eq_right (by linarith only [hh])
    have hRT : R ≤ L^(1-2*γ) := by simpa only [k4CoefficientCut,ite_eq_right hh] using hcut
    have he2 : 3*(d : ℝ)-2*γ-1-min γ (1-γ)/20=E := by simp only [E,hmin] <;> ring
    have he1 : 3*(d : ℝ)-4*γ-min γ (1-γ)/20 ≤ E := by dsimp only [E]; rw [hmin]; linarith only [hh]
    have h1 := mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_le hL he1) (pow_nonneg hR (d-2))
    have h3 : L^(3*(d : ℝ)-2-min γ (1-γ)/20)*R^d ≤ L^E*R^(d-1) := by
      rw [hpow]
      have hm := mul_le_mul_of_nonneg_left hRT
        (by positivity : 0 ≤ L^(3*(d : ℝ)-2-min γ (1-γ)/20)*R^(d-1))
      calc
        _ = (L^(3*(d : ℝ)-2-min γ (1-γ)/20)*R^(d-1))*R := by ring
        _ ≤ (L^(3*(d : ℝ)-2-min γ (1-γ)/20)*R^(d-1))*L^(1-2*γ) := hm
        _ = R^(d-1)*(L^(3*(d : ℝ)-2-min γ (1-γ)/20)*L^(1-2*γ)) := by ring
        _ = _ := by
          rw [← Real.rpow_add hLp]
          have he : (3*(d : ℝ)-2-min γ (1-γ)/20)+(1-2*γ)=E := by
            dsimp only [E]
            rw [hmin]
            ring
          rw [he,mul_comm]
    rw [he2]
    nlinarith only [h1,h3]

end WaveTurbulence.MoleProp
