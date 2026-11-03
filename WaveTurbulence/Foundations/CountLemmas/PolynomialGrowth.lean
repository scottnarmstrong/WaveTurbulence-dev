/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.CountLemmas.PowerAbsorption

/-! # Compositional polynomial growth bounds for the counting majorants -/

public section
open Filter Asymptotics
namespace WaveTurbulence.CountLemmas

/-- Identity power profile. -/
theorem growth_rpow (a : ℝ) : (fun L : ℝ => L^a) =O[atTop] (fun L : ℝ => L^a) :=
  Asymptotics.isBigO_refl _ _

/-- Constant coefficients do not change a growth exponent. -/
theorem growth_const (C : ℝ) : (fun _ : ℝ => C) =O[atTop] (fun L : ℝ => L^(0 : ℝ)) := by
  simpa only [Real.rpow_zero,mul_one] using (growth_rpow 0).const_mul_left C

/-- Monotonicity of power profiles on the positive tail. -/
theorem growth_mono {a b : ℝ} (hab : a ≤ b) :
    (fun L : ℝ => L^a) =O[atTop] (fun L : ℝ => L^b) := by
  apply Asymptotics.IsBigO.of_bound 1
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with L hL
  rw [Real.norm_of_nonneg (by positivity : 0 ≤ L^a),Real.norm_of_nonneg (by positivity : 0 ≤ L^b),one_mul]
  exact Real.rpow_le_rpow_of_exponent_le hL hab

/-- Multiply two polynomial profiles and collect their exponents. -/
theorem growth_mul {f g : ℝ → ℝ} {a b c : ℝ}
    (hf : f =O[atTop] fun L => L^a) (hg : g =O[atTop] fun L => L^b) (hab : a+b ≤ c) :
    (fun L => f L*g L) =O[atTop] (fun L => L^c) :=
  hf.mul_atTop_rpow_of_isBigO_rpow a b c hg hab

/-- Add two profiles under a common upper exponent. -/
theorem growth_add {f g : ℝ → ℝ} {a b c : ℝ}
    (hf : f =O[atTop] fun L => L^a) (hg : g =O[atTop] fun L => L^b)
    (ha : a ≤ c) (hb : b ≤ c) :
    (fun L => f L+g L) =O[atTop] (fun L => L^c) :=
  (hf.trans (growth_mono ha)).add (hg.trans (growth_mono hb))

/-- Positive integer powers multiply the growth exponent. -/
theorem growth_pow {f : ℝ → ℝ} {a : ℝ}
    (hf : f =O[atTop] fun L => L^a) (n : ℕ) :
    (fun L => (f L)^n) =O[atTop] (fun L => L^(a*n)) := by
  apply (hf.pow n).congr' Filter.EventuallyEq.rfl
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with L hL
  exact (Real.rpow_mul_natCast hL a n).symm

/-- Natural powers are real-power profiles. -/
theorem growth_natpow (n : ℕ) : (fun L : ℝ => L^n) =O[atTop] (fun L => L^(n : ℝ)) := by
  simpa only [Real.rpow_natCast] using growth_rpow (n : ℝ)

/-- Any positive power absorbs the squared logarithm. -/
theorem growth_log_sq {ε : ℝ} (hε : 0 < ε) :
    (fun L : ℝ => (1+Real.log L)^2) =O[atTop] (fun L => L^ε) := by
  apply Asymptotics.IsBigO.of_bound 1
  filter_upwards [eventually_monomial_log_le hε (by norm_num : (0 : ℝ) ≤ 1) 2,
    eventually_ge_atTop (1 : ℝ)] with L h hL
  simpa only [Real.rpow_zero,one_mul,Real.norm_of_nonneg (sq_nonneg _),
    Real.norm_of_nonneg (by positivity : 0 ≤ L^ε)] using h

/-- A strict power gain converts a polynomial growth bound into the inverse
logarithmic gain required by the exact COUNT draft. -/
theorem growth_eventually_le_div_log_sq {f : ℝ → ℝ} {a b : ℝ}
    (hf : f =O[atTop] fun L => L^a) (hab : a < b) :
    ∀ᶠ L : ℝ in atTop, f L ≤ L^b/(Real.log L)^2 := by
  obtain ⟨C,hC,hb⟩ := hf.exists_nonneg
  have hh := eventually_monomial_log_le_div_log_sq hab hC 0
  filter_upwards [hb.bound,hh,eventually_ge_atTop (1 : ℝ)] with L hbound hcomp hL
  have hn : ‖f L‖ ≤ C*L^a := by
    simpa only [Real.norm_of_nonneg (by positivity : 0 ≤ L^a)] using hbound
  exact (le_abs_self (f L)).trans (by simpa only [Real.norm_eq_abs] using hn) |>.trans
    (by simpa only [pow_zero,mul_one] using hcomp)

/-- A strict polynomial growth gap also gives the unweighted eventual bound. -/
theorem growth_eventually_le {f : ℝ → ℝ} {a b : ℝ}
    (hf : f =O[atTop] fun L => L^a) (hab : a < b) :
    ∀ᶠ L : ℝ in atTop, f L ≤ L^b := by
  filter_upwards [growth_eventually_le_div_log_sq hf hab,
    Real.tendsto_log_atTop.eventually_ge_atTop 1,eventually_ge_atTop (1 : ℝ)] with L hb hlog hL
  exact hb.trans (div_le_self (by positivity) (by nlinarith only [hlog] : 1 ≤ (Real.log L)^2))

end WaveTurbulence.CountLemmas
