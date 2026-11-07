/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.AppBPairGrowth
import Mathlib.Tactic

/-! # Power profiles for the sum selector with logarithmic energy windows -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole
open Filter Asymptotics CountLemmas

theorem appb_positive_shell_exponent (γ : ℝ) :
    max 1 (2-2*γ) = 2-γ-min γ (1-γ) := by
  by_cases h : γ ≤ 1/2
  · rw [max_eq_right (by linarith only [h]),min_eq_left (by linarith only [h])]
    ring
  · rw [max_eq_left (by linarith only [h]),min_eq_right (by linarith only [h])]
    ring

/-- The exact majorant from the fixed-sum annulus fiber and strip count. -/
noncomputable def appbPairSumMajorant (n : ℕ) (c δ γ : ℝ) (m : ℕ) (L : ℝ) : ℝ :=
  (4*L+1)^(n+1) *
    (1+(2*((n+2 : ℕ) : ℝ)*c)*(appbWidth δ γ m L*L/L^(-γ))) *
    ((2*L+1)^n*(6*Real.pi+1284002)*(2*appbWidth δ γ m L*L^2+L))

theorem appb_growth_pair_sum_majorant (n : ℕ) (c δ γ : ℝ)
    (hγ : γ ∈ Set.Ioo (0 : ℝ) 1) (m : ℕ) :
    appbPairSumMajorant n c δ γ m =O[atTop]
      (fun L => L^(2*((((n+2 : ℕ) : ℝ))-γ)-min γ (1-γ)+2*(min γ (1-γ)/100))) := by
  let ε := min γ (1-γ)/100
  let ψ := max 1 (2-2*γ)
  have hε : 0 < ε := div_pos (lt_min hγ.1 (sub_pos.mpr hγ.2)) (by norm_num)
  have hψ : ψ = 2-γ-min γ (1-γ) := appb_positive_shell_exponent γ
  have hwidth := appb_growth_width δ γ m hε
  have hτL := growth_mul hwidth growth_id (c := 1-2*γ+ε) (by ring_nf; exact le_rfl)
  have hdiv := growth_div_rpow hτL (-γ)
  have hcoef := growth_one_add (hdiv.const_mul_left (2*((n+2 : ℕ) : ℝ)*c))
    (b := 1-γ+ε) (by ring_nf; exact le_rfl) (by linarith only [hγ.2,hε])
  have hprojection := growth_mul (growth_box 4 (n+1)) hcoef
    (c := (((n+2 : ℕ) : ℝ))-γ+ε) (by push_cast; ring_nf; exact le_rfl)
  have hτL2 := growth_mul hwidth (growth_natpow 2) (c := 2-2*γ+ε) (by norm_num; ring_nf; exact le_rfl)
  have htail := growth_add (hτL2.const_mul_left 2) growth_id (c := ψ+ε)
    (by have := le_max_right (1 : ℝ) (2-2*γ); dsimp only [ψ]; linarith only [this])
    (by have := le_max_left (1 : ℝ) (2-2*γ); dsimp only [ψ]; linarith only [this,hε])
  have hbox := (growth_box 2 n).const_mul_left (6*Real.pi+1284002)
  have hfiber := growth_mul hbox htail
    (c := (((n+2 : ℕ) : ℝ))-γ-min γ (1-γ)+ε) (by push_cast; linarith only [hψ])
  have htotal := growth_mul hprojection hfiber
    (c := 2*((((n+2 : ℕ) : ℝ))-γ)-min γ (1-γ)+2*ε) (by ring_nf; exact le_rfl)
  convert htotal using 1
  funext L
  unfold appbPairSumMajorant
  ring

theorem appb_pair_sum_majorant_eventual (n : ℕ) (c δ γ : ℝ)
    (hγ : γ ∈ Set.Ioo (0 : ℝ) 1) (m : ℕ) :
    ∀ᶠ L : ℝ in atTop, appbPairSumMajorant n c δ γ m L ≤
      L^(2*((((n+2 : ℕ) : ℝ))-γ)-2*min γ (1-γ)/3) := by
  apply growth_eventually_le (appb_growth_pair_sum_majorant n c δ γ hγ m)
  have hpos := lt_min hγ.1 (sub_pos.mpr hγ.2)
  linarith only [hpos]

/-- The scalar tolerance used by Appendix B is above the one-cell annulus
width for all sufficiently large L, uniformly in all graph centers. -/
theorem appb_width_times_sq_eventually_ge_one (δ γ : ℝ) (hδ : 0 < δ) (hγ : γ < 1) (m : ℕ) :
    ∀ᶠ L : ℝ in atTop, 1 ≤ appbWidth δ γ m L * L^2 := by
  have hbase := eventually_scaled_power_le (show (0 : ℝ) < 2-2*γ by linarith only [hγ])
    (by norm_num : (0 : ℝ) ≤ 1) (inv_pos.mpr hδ)
  filter_upwards [hbase,eventually_ge_atTop (1 : ℝ)] with L hb hL
  have hLp : 0 < L := zero_lt_one.trans_le hL
  have hlog : 0 ≤ Real.log L := Real.log_nonneg hL
  have hpow : 1 ≤ (1+Real.log L)^m := one_le_pow₀ (by linarith only [hlog])
  have he : appbWidth δ γ m L * L^2 = δ⁻¹*(1+Real.log L)^m*L^(2-2*γ) := by
    unfold appbWidth
    rw [mul_assoc, show L^2 = L^(2 : ℝ) from (Real.rpow_natCast L 2).symm,← Real.rpow_add hLp]
    congr 2
    ring
  rw [he]
  calc
    1 ≤ δ⁻¹*L^(2-2*γ) := by simpa only [Real.rpow_zero,one_mul] using hb
    _ ≤ _ := by
      have hh := mul_le_mul_of_nonneg_right hpow (by positivity : 0 ≤ δ⁻¹*L^(2-2*γ))
      simpa only [one_mul,mul_assoc,mul_comm,mul_left_comm] using hh

end WaveTurbulence.Mole
