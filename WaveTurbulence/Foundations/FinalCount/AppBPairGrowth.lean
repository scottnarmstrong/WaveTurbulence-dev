/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.CountLemmas.GrowthProfiles
import Mathlib.Tactic

/-! # Polynomial-logarithmic windows and the Appendix B pair saving -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole
open Filter Asymptotics CountLemmas

/-- Actual tolerance after summing at most a polynomial-logarithmic
number of energy windows. -/
noncomputable def appbWidth (δ γ : ℝ) (m : ℕ) (L : ℝ) : ℝ :=
  δ⁻¹ * (1+Real.log L)^m * L^(-2*γ)

theorem appb_growth_log_natpow (m : ℕ) {ε : ℝ} (hε : 0 < ε) :
    (fun L : ℝ => (1+Real.log L)^m) =O[atTop] (fun L => L^ε) := by
  apply Asymptotics.IsBigO.of_bound 1
  filter_upwards [eventually_monomial_log_le hε (by norm_num : (0 : ℝ) ≤ 1) m,
    eventually_ge_atTop (1 : ℝ)] with L h hL
  have hlog : 0 ≤ Real.log L := Real.log_nonneg hL
  simpa only [Real.rpow_zero,one_mul,Real.norm_of_nonneg (by positivity : 0 ≤ (1+Real.log L)^m),
    Real.norm_of_nonneg (by positivity : 0 ≤ L^ε)] using h

theorem appb_growth_width (δ γ : ℝ) (m : ℕ) {ε : ℝ} (hε : 0 < ε) :
    appbWidth δ γ m =O[atTop] (fun L => L^(-2*γ+ε)) := by
  have hh := growth_mul (appb_growth_log_natpow m hε) (growth_bandwidth δ γ)
    (c := -2*γ+ε) (by ring_nf; exact le_rfl)
  convert hh using 1
  funext L
  unfold appbWidth
  ring

/-- The elementary two-strip exponent is exactly the source gamma0 gain. -/
theorem appb_pair_exponent_identity (D γ : ℝ) :
    2*(D-1)+(1-γ)+max 0 (1-2*γ) = 2*(D-γ)-min γ (1-γ) := by
  by_cases h : γ ≤ 1/2
  · rw [max_eq_right (by linarith only [h]),min_eq_left (by linarith only [h])]
    ring
  · rw [max_eq_left (by linarith only [h]),min_eq_right (by linarith only [h])]
    ring

/-- A center-independent explicit majorant for selector x. -/
noncomputable def appbPairXMajorant (d : ℕ) (c δ γ : ℝ) (m : ℕ) (L : ℝ) : ℝ :=
  15^d*L^d + 12*((d : ℝ)+1)*(3^(d-1)*L^(d-1))^2 *
    (1+(2*(d : ℝ)*c)*(appbWidth δ γ m L*L/L^(-γ))) * (1+appbWidth δ γ m L*L)

/-- Constants and polynomial logarithms fit strictly inside the gamma0
power gap. No counting estimate is assumed here. -/
theorem appb_growth_pair_x_majorant (d : ℕ) (hd : 3 ≤ d) (c δ γ : ℝ)
    (hγ : γ ∈ Set.Ioo (0 : ℝ) 1) (m : ℕ) :
    appbPairXMajorant d c δ γ m =O[atTop]
      (fun L => L^(2*((d : ℝ)-γ)-min γ (1-γ)+2*(min γ (1-γ)/100))) := by
  let ε := min γ (1-γ)/100
  let α := max 0 (1-2*γ)
  let E0 := 2*((d : ℝ)-γ)-min γ (1-γ)
  have hε : 0 < ε := div_pos (lt_min hγ.1 (sub_pos.mpr hγ.2)) (by norm_num)
  have hD : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have hc : ((d-1 : ℕ) : ℝ) = (d : ℝ)-1 := by rw [Nat.cast_sub (by omega)]; norm_num
  have hE : 2*((d-1 : ℕ) : ℝ)+(1-γ)+α = E0 := by
    rw [hc]
    exact appb_pair_exponent_identity (d : ℝ) γ
  have hwidth := appb_growth_width δ γ m hε
  have hτL := growth_mul hwidth growth_id (c := 1-2*γ+ε) (by ring_nf; exact le_rfl)
  have hdiv := growth_div_rpow hτL (-γ)
  have hcoef := growth_one_add (hdiv.const_mul_left (2*(d : ℝ)*c))
    (b := 1-γ+ε) (by ring_nf; exact le_rfl) (by linarith only [hγ.2,hε])
  have htail := growth_one_add hτL (b := α+ε)
    (by have := le_max_right (0 : ℝ) (1-2*γ); dsimp only [α]; linarith only [this])
    (by have := le_max_left (0 : ℝ) (1-2*γ); dsimp only [α]; linarith only [this,hε])
  have hsquare := growth_pow ((growth_natpow (d-1)).const_mul_left ((3 : ℝ)^(d-1))) 2
  have hprod := growth_mul hsquare hcoef
    (c := 2*((d-1 : ℕ) : ℝ)+(1-γ+ε)) (by ring_nf; exact le_rfl)
  have hrest := growth_mul hprod htail (c := E0+2*ε) (by linarith only [hE])
  have hterm : (d : ℝ) ≤ E0+2*ε := by
    have hm := min_le_right γ (1-γ)
    dsimp only [E0]
    linarith only [hD,hγ.2,hm,hε]
  have htotal := growth_add ((growth_natpow d).const_mul_left ((15 : ℝ)^d))
    (hrest.const_mul_left (12*((d : ℝ)+1))) hterm le_rfl
  convert htotal using 1
  funext L
  unfold appbPairXMajorant
  ring

/-- The raw large-difference pair count has room for all later logarithmic
ladder-factor losses: two-thirds gamma0 is larger than five-eighths. -/
theorem appb_pair_x_majorant_eventual (d : ℕ) (hd : 3 ≤ d) (c δ γ : ℝ)
    (hγ : γ ∈ Set.Ioo (0 : ℝ) 1) (m : ℕ) :
    ∀ᶠ L : ℝ in atTop, appbPairXMajorant d c δ γ m L ≤
      L^(2*((d : ℝ)-γ)-2*min γ (1-γ)/3) := by
  apply growth_eventually_le (appb_growth_pair_x_majorant d hd c δ γ hγ m)
  have hpos := lt_min hγ.1 (sub_pos.mpr hγ.2)
  linarith only [hpos]

end WaveTurbulence.Mole
