/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.CountLemmas.DotStrip

/-! # A uniform cap on the actual dot-product fibers -/

public section
namespace WaveTurbulence.CountLemmas

@[expose] noncomputable def pairFiberCap (d : ℕ) : ℝ := (3 : ℝ)^(d-1)*(2*(d : ℝ)+1)

theorem one_le_pairFiberCap (d : ℕ) : 1 ≤ pairFiberCap d := by
  exact one_le_mul_of_one_le_of_one_le
    (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 3)) (by have hh := Nat.cast_nonneg (α := ℝ) d; linarith)

/-- When τL does not exceed the coefficient norm lower bound, a dot-product
fiber has at most a fixed multiple of `L^(d-1)` points. -/
theorem card_dot_fiber_cap {d : ℕ} (hd : 0 < d) (s : Finset (Fin d → ℤ))
    {L τ R : ℝ} (hL : 1 ≤ L) (hτ : 0 ≤ τ) (hR : 0 < R) (hτR : τ*L ≤ R)
    (b x : Mom d) (α : ℝ) (hx : R ≤ ‖x‖)
    (hball : ∀ y ∈ s, ‖latticePoint L y-b‖ ≤ 1)
    (hband : ∀ y ∈ s, |inner ℝ x (latticePoint L y)-α| ≤ τ) :
    (s.card : ℝ) ≤ pairFiberCap d*L^(d-1) := by
  have hLp : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have hb := card_dot_strip_ball_norm_le hd s hLp (by norm_num : (0 : ℝ) ≤ 1) hτ hR b x α hx hball hband
  simp only [mul_one] at hb
  have hbox : (2*L+1)^(d-1) ≤ (3 : ℝ)^(d-1)*L^(d-1) := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by positivity) (by linarith only [hL]) _
  have hratio : τ*L/R ≤ 1 := (div_le_one hR).mpr hτR
  have ht : 2*(d : ℝ)*τ*L/R+1 ≤ 2*(d : ℝ)+1 := by
    have hh := mul_le_mul_of_nonneg_left hratio (by positivity : 0 ≤ 2*(d : ℝ))
    have hh' : 2*(d : ℝ)*τ*L/R ≤ 2*(d : ℝ) := by convert hh using 1 <;> ring
    exact add_le_add hh' le_rfl
  apply hb.trans
  have hh := mul_le_mul hbox ht (by positivity) (by positivity)
  convert hh using 1
  dsimp only [pairFiberCap]
  ring

end WaveTurbulence.CountLemmas
