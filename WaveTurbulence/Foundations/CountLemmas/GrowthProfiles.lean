/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.CountLemmas.PolynomialGrowth

/-! # Concrete growth profiles used by COUNT's large-scale estimates -/

public section
open Filter Asymptotics
namespace WaveTurbulence.CountLemmas

theorem growth_id : (fun L : ℝ => L) =O[atTop] (fun L : ℝ => L^(1 : ℝ)) := by
  simpa only [Real.rpow_one] using growth_rpow 1

theorem growth_box (C : ℝ) (n : ℕ) :
    (fun L : ℝ => (C*L+1)^n) =O[atTop] (fun L : ℝ => L^(n : ℝ)) := by
  have hh := growth_add (growth_id.const_mul_left C) (growth_const 1)
    (by norm_num : (1 : ℝ) ≤ 1) (by norm_num : (0 : ℝ) ≤ 1)
  simpa only [one_mul] using growth_pow hh n

theorem growth_bandwidth (δ γ : ℝ) :
    (fun L : ℝ => δ⁻¹*L^(-2*γ)) =O[atTop] (fun L : ℝ => L^(-2*γ)) :=
  (growth_rpow (-2*γ)).const_mul_left δ⁻¹

theorem growth_div_rpow {f : ℝ → ℝ} {a : ℝ}
    (hf : f =O[atTop] fun L => L^a) (b : ℝ) :
    (fun L => f L/L^b) =O[atTop] (fun L => L^(a-b)) := by
  have hh := growth_mul hf (growth_rpow (-b)) (by rfl : a + -b ≤ a-b)
  apply hh.congr' ?_ Filter.EventuallyEq.rfl
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with L hL
  rw [Real.rpow_neg hL,div_eq_mul_inv]

theorem growth_one_add {f : ℝ → ℝ} {a b : ℝ}
    (hf : f =O[atTop] fun L => L^a) (ha : a ≤ b) (hb : 0 ≤ b) :
    (fun L => 1+f L) =O[atTop] (fun L => L^b) :=
  growth_add (growth_const 1) hf hb ha

/-- Constants on both sides of a strict power comparison are absorbed
into its threshold. -/
theorem eventually_scaled_power_le {a b C D : ℝ} (hab : a < b)
    (hC : 0 ≤ C) (hD : 0 < D) :
    ∀ᶠ L : ℝ in atTop, C*L^a ≤ D*L^b := by
  have hh := eventually_monomial_log_le hab (div_nonneg hC hD.le) 0
  filter_upwards [hh] with L hL
  have he : (C/D)*L^a ≤ L^b := by simpa only [pow_zero,mul_one] using hL
  have hm := mul_le_mul_of_nonneg_left he hD.le
  have hid : D*(C/D*L^a) = C*L^a := by field_simp
  rw [hid] at hm
  exact hm

end WaveTurbulence.CountLemmas
