/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Frozen.Defs.LatticePoint

/-! # Exact conversion of physical dot-product bands to integer coordinates -/

public section
open Finset
namespace WaveTurbulence.CountLemmas

theorem integer_dot_eq_scaled_inner {d : ℕ} {L : ℝ} (hL : L ≠ 0)
    (x y : Fin d → ℤ) :
    (∑ i, (x i : ℝ)*(y i : ℝ)) = L^2*inner ℝ (latticePoint L x) (latticePoint L y) := by
  simp only [PiLp.inner_apply,Real.inner_apply,latticePoint,mul_sum]
  apply sum_congr rfl
  intro i _
  field_simp

theorem integer_dot_band {d : ℕ} {L τ α : ℝ} (hL : L ≠ 0)
    (x y : Fin d → ℤ) (h : |inner ℝ (latticePoint L x) (latticePoint L y)-α| ≤ τ) :
    |(∑ i, (x i : ℝ)*(y i : ℝ))-L^2*α| ≤ τ*L^2 := by
  rw [integer_dot_eq_scaled_inner hL,← mul_sub,abs_mul,abs_of_nonneg (sq_nonneg L)]
  exact (mul_le_mul_of_nonneg_left h (sq_nonneg L)).trans_eq (mul_comm _ _)

end WaveTurbulence.CountLemmas
