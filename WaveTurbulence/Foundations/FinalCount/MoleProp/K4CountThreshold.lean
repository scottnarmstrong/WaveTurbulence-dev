/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.CountLemmas.PowerAbsorption
import Mathlib.Tactic

/-! # Source-uniform large-L separation for the actual K4 sphere threshold

Only d,gamma and fixed delta determine this threshold. All graph, spatial
and energy parameters are quantified later in the counting application.
-/

@[expose] public section
set_option autoImplicit false
open Filter
namespace WaveTurbulence.MoleProp

/-- The source threshold M=L^(1−γ₀/10) eventually separates the actual
squared-energy tolerance from zero, uniformly in all source centers. -/
theorem k4_sphere_threshold_separation (d : ℕ) (hd : 0 < d) {γ δ : ℝ}
    (hγ : 0 < γ) (hγ1 : γ < 1) (hδ : δ ∈ Set.Ioc (0 : ℝ) 1) :
    ∃ L₀ : ℝ, ∀ L ≥ L₀,
      1 ≤ L^2*(2*(δ⁻¹*L^(-2*γ))) ∧
      4*(L^2*(2*(δ⁻¹*L^(-2*γ)))) ≤
        ((L*L^(1-min γ (1-γ)/10))/(d : ℝ))^2 := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hD0 : 0 < δ⁻¹ := inv_pos.mpr hδ.1
  have hD1 : 1 ≤ δ⁻¹ := (one_le_inv₀ hδ.1).mpr hδ.2
  have hgap : 2-2*γ < 4-min γ (1-γ)/5 := by
    have hh := min_le_left γ (1-γ)
    linarith only [hh,hγ]
  have hev := CountLemmas.eventually_monomial_log_le
    (C := 8*(d : ℝ)^2*δ⁻¹) hgap (by positivity) 0
  have hfinal : ∀ᶠ L : ℝ in atTop,
      1 ≤ L^2*(2*(δ⁻¹*L^(-2*γ))) ∧
      4*(L^2*(2*(δ⁻¹*L^(-2*γ)))) ≤
        ((L*L^(1-min γ (1-γ)/10))/(d : ℝ))^2 := by
    filter_upwards [hev,eventually_ge_atTop (1 : ℝ)] with L hpower hL
    have hLp : 0 < L := zero_lt_one.trans_le hL
    simp only [pow_zero,mul_one] at hpower
    have hW : L^2*(2*(δ⁻¹*L^(-2*γ))) = 2*δ⁻¹*L^(2-2*γ) := by
      calc
        _ = 2*δ⁻¹*(L^2*L^(-2*γ)) := by ring
        _ = _ := by rw [← Real.rpow_two,← Real.rpow_add hLp]; congr 2; ring
    have hM : ((L*L^(1-min γ (1-γ)/10))/(d : ℝ))^2 =
        L^(4-min γ (1-γ)/5)/(d : ℝ)^2 := by
      have he : L*L^(1-min γ (1-γ)/10) = L^(2-min γ (1-γ)/10) := by
        calc
          _ = L^(1 : ℝ)*L^(1-min γ (1-γ)/10) := by rw [Real.rpow_one]
          _ = _ := by rw [← Real.rpow_add hLp]; congr 1; ring
      rw [he,div_pow,← Real.rpow_mul_natCast hLp.le]
      congr 2
      ring
    constructor
    · rw [hW]
      have hP : 1 ≤ L^(2-2*γ) := Real.one_le_rpow hL (by linarith only [hγ1])
      have hh := one_le_mul_of_one_le_of_one_le hD1 hP
      linarith only [hh]
    · rw [hW,hM]
      apply (le_div_iff₀ (sq_pos_of_pos hdR)).mpr
      convert hpower using 1 <;> ring
  exact eventually_atTop.mp hfinal

end WaveTurbulence.MoleProp
