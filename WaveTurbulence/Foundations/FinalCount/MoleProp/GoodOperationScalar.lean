/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.MoleProp.DeletionScalars
public import WaveTurbulence.Foundations.FinalCount.MoleProp.LargeGraphAbsorption
import Mathlib.Tactic

/-! # Normalization and internal logarithmic-size absorption for good steps -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.MoleProp

theorem good_operation_scalar_le {L a gain δ B C N : ℝ} {p j : ℕ}
    (hL : 1 ≤ L) (hgain : gain ≤ a*j) (hN : 1 ≤ N)
    (hδ : δ ∈ Set.Ioc (0 : ℝ) 1) (hB : 0 ≤ B) (hB1 : B ≤ 1)
    (hC : 0 ≤ C) (hp : p ≤ 3) :
    (⌈C*N^2*(δ⁻¹)^p*L^(a*j-gain)⌉₊ : ℝ)*L^(-(a*j))*B^j ≤
      (C+1)*N^2*(δ⁻¹)^3*L^(-gain) := by
  have hLp : 0 < L := zero_lt_one.trans_le hL
  have hD : 1 ≤ δ⁻¹ := (one_le_inv₀ hδ.1).mpr hδ.2
  have hA : 1 ≤ N^2*(δ⁻¹)^p*L^(a*j-gain) :=
    one_le_mul_of_one_le_of_one_le
      (one_le_mul_of_one_le_of_one_le (one_le_pow₀ hN) (one_le_pow₀ hD))
      (Real.one_le_rpow hL (sub_nonneg.mpr hgain))
  have hk : (⌈C*N^2*(δ⁻¹)^p*L^(a*j-gain)⌉₊ : ℝ) ≤
      (C+1)*(N^2*(δ⁻¹)^p*L^(a*j-gain)) := by
    simpa only [mul_assoc] using ceil_mul_scale_le hC hA
  have hb : B^j ≤ 1 := pow_le_one₀ hB hB1
  have hm := mul_le_mul hk hb (pow_nonneg hB _)
    (by positivity : 0 ≤ (C+1)*(N^2*(δ⁻¹)^p*L^(a*j-gain)))
  have hm' := mul_le_mul_of_nonneg_right hm (Real.rpow_nonneg hLp.le (-(a*j)))
  have hpow : L^(a*j-gain)*L^(-(a*j)) = L^(-gain) := by
    rw [← Real.rpow_add hLp]
    congr 1 <;> ring
  calc
    _ = ((⌈C*N^2*(δ⁻¹)^p*L^(a*j-gain)⌉₊ : ℝ)*B^j)*L^(-(a*j)) := by ring
    _ ≤ _ := hm'
    _ = (C+1)*N^2*(δ⁻¹)^p*L^(-gain) := by
      calc
        _ = (C+1)*N^2*(δ⁻¹)^p*(L^(a*j-gain)*L^(-(a*j))) := by ring
        _ = _ := by rw [hpow]
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hD hp) (by positivity : 0 ≤ (C+1)*N^2))
      (Real.rpow_nonneg hLp.le _)

/-- A fixed polynomial size loss is absorbed internally on the small-graph
branch. Both exponents are arbitrary, so this applies to all good cases. -/
theorem eventually_log_size_power_gain {C a b : ℝ} (hC : 0 ≤ C) (hab : a < b) (m : ℕ) :
    ∃ R : ℝ, ∀ L ≥ R, ∀ n : ℕ, (n : ℝ) ≤ Real.log L →
      C*((n : ℝ)+1)^m*L^(-b) ≤ L^(-a) := by
  obtain ⟨R,hR⟩ := eventually_log_size_polynomial_bound hC (sub_pos.mpr hab) m
  refine ⟨max R 1,?_⟩
  intro L hL n hn
  have hLp : 0 < L := zero_lt_one.trans_le ((le_max_right R 1).trans hL)
  calc
    _ ≤ L^(b-a)*L^(-b) := mul_le_mul_of_nonneg_right
      (hR L ((le_max_left R 1).trans hL) n hn) (Real.rpow_nonneg hLp.le _)
    _ = _ := by rw [← Real.rpow_add hLp]; congr 1; ring

end WaveTurbulence.MoleProp
