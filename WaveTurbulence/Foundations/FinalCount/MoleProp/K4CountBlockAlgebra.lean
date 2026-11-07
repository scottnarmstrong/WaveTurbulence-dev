/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-! # Polynomial radial profile in the actual K4 block estimate

The source elementary base has both a volume and a lattice-boundary
term. Multiplying by the proved sphere-strip profile retains three
positive powers of the coefficient radius, suitable for finite geometric
summation in dimension at least three.
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.MoleProp

/-- Elementary coefficient arithmetic before inserting the radius powers. -/
theorem k4_block_polynomial_core {d L R τ H : ℝ}
    (hd : 1 ≤ d) (hL : 0 ≤ L) (hR : 0 ≤ R) (hτ : 0 ≤ τ) (hH : 1 ≤ H) :
    (τ*L^2*H+3*L*R)*(4*d*L*τ+2*R) ≤
      (16*d+8)*H*(τ^2*L^3+τ*L^2*R+L*R^2) := by
  have hd0 : 0 ≤ d := zero_le_one.trans hd
  have hH0 : 0 ≤ H := zero_le_one.trans hH
  have h1 : 4*d*H ≤ (16*d+8)*H := mul_le_mul_of_nonneg_right (by linarith only [hd]) hH0
  have h2a : 2*H+12*d ≤ (2+12*d)*H := by
    have hh := mul_le_mul_of_nonneg_left hH (by positivity : 0 ≤ 12*d)
    nlinarith only [hh]
  have h2 : 2*H+12*d ≤ (16*d+8)*H := h2a.trans
    (mul_le_mul_of_nonneg_right (by linarith only [hd]) hH0)
  have h3 : 6 ≤ (16*d+8)*H := by
    have hh := mul_le_mul_of_nonneg_left hH (by positivity : 0 ≤ 16*d+8)
    nlinarith only [hh,hd]
  have ha := mul_le_mul_of_nonneg_right h1 (by positivity : 0 ≤ τ^2*L^3)
  have hb := mul_le_mul_of_nonneg_right h2 (by positivity : 0 ≤ τ*L^2*R)
  have hc := mul_le_mul_of_nonneg_right h3 (by positivity : 0 ≤ L*R^2)
  nlinarith only [ha,hb,hc]

/-- Actual radial profile, with the positive radius canceling the strip
inverse and all three remaining powers kept explicitly. -/
theorem k4_block_radial_profile (n : ℕ) (hn : 1 ≤ n) {d L R τ H : ℝ}
    (hd : 1 ≤ d) (hL : 0 ≤ L) (hR : 0 < R) (hτ : 0 ≤ τ) (hH : 1 ≤ H) :
    R^n*(τ*L^2*H+3*L*R)*(4*d*L*τ/R+2) ≤
      (16*d+8)*H*(τ^2*L^3*R^(n-1)+τ*L^2*R^n+L*R^(n+1)) := by
  have hpow : R^n=R^(n-1)*R := by rw [← pow_succ,Nat.sub_add_cancel hn]
  have hpow1 : R^(n+1)=R^(n-1)*R^2 := by
    rw [pow_succ,hpow]
    ring
  have he : R^n*(τ*L^2*H+3*L*R)*(4*d*L*τ/R+2) =
      R^(n-1)*((τ*L^2*H+3*L*R)*(4*d*L*τ+2*R)) := by
    rw [hpow]
    field_simp [hR.ne'] <;> ring
  have hh := mul_le_mul_of_nonneg_left (k4_block_polynomial_core hd hL hR.le hτ hH)
    (pow_nonneg hR.le (n-1))
  rw [he]
  convert hh using 1 <;> rw [hpow,hpow1] <;> ring

end WaveTurbulence.MoleProp
