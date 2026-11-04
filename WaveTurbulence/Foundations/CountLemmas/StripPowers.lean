/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-! # Scale algebra for the atomic strip estimates -/

public section
namespace WaveTurbulence.CountLemmas

/-- The endpoint term in a strip count is absorbed when its threshold power
is nonnegative. The scale exponent is written separately from the dimension. -/
theorem strip_power_bound {L δ γ η a D : ℝ} (hL : 1 ≤ L)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (ha : 0 < a)
    (he : 0 ≤ 1-γ-η) (hgap : L^(-γ+η) ≤ D*a) :
    (δ⁻¹*L^(-2*γ))*L/a+1 ≤ (D+1)*δ⁻¹*L^(1-γ-η) := by
  have hLp : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have hpow : 1 ≤ L^(1-γ-η) := Real.one_le_rpow hL he
  have hδi : 1 ≤ δ⁻¹ := (one_le_inv₀ hδ).mpr hδ1
  have hA : 1 ≤ δ⁻¹*L^(1-γ-η) := one_le_mul_of_one_le_of_one_le hδi hpow
  have hid : L^(-γ+η)*L^(1-γ-η) = L^(-2*γ)*L := by
    calc
      _ = L^(-2*γ)*L^(1 : ℝ) := by
        rw [← Real.rpow_add hLp,← Real.rpow_add hLp]
        congr 1
        ring
      _ = _ := by rw [Real.rpow_one]
  have hm := mul_le_mul_of_nonneg_right hgap
    (mul_nonneg (inv_nonneg.mpr hδ.le) (Real.rpow_nonneg hLp.le (1-γ-η)))
  have hstrip : (δ⁻¹*L^(-2*γ))*L/a ≤ D*δ⁻¹*L^(1-γ-η) := by
    apply (div_le_iff₀ ha).mpr
    calc
      _ = L^(-γ+η)*(δ⁻¹*L^(1-γ-η)) := by
        calc
          _ = δ⁻¹*(L^(-2*γ)*L) := by ring
          _ = δ⁻¹*(L^(-γ+η)*L^(1-γ-η)) := by rw [hid]
          _ = _ := by ring
      _ ≤ (D*a)*(δ⁻¹*L^(1-γ-η)) := hm
      _ = _ := by ring
  calc
    _ ≤ D*δ⁻¹*L^(1-γ-η)+δ⁻¹*L^(1-γ-η) := add_le_add hstrip hA
    _ = _ := by ring

/-- The nonzero lattice spacing absorbs the endpoint at the coarser scale
`δ⁻¹ L^(2-2γ)`. -/
theorem strip_lattice_power_bound {L δ γ a : ℝ} (hL : 1 ≤ L)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hγ : γ ≤ 1)
    (hgap : L⁻¹ ≤ a) :
    (δ⁻¹*L^(-2*γ))*L/a+1 ≤ 2*δ⁻¹*L^(2-2*γ) := by
  have hLp : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have ha : 0 < a := (inv_pos.mpr hLp).trans_le hgap
  have hA : 1 ≤ δ⁻¹*L^(2-2*γ) := one_le_mul_of_one_le_of_one_le
    ((one_le_inv₀ hδ).mpr hδ1) (Real.one_le_rpow hL (by linarith only [hγ]))
  have hid : L^(-2*γ)*L = L⁻¹*L^(2-2*γ) := by
    calc
      _ = L^(-2*γ)*L^(1 : ℝ) := by rw [Real.rpow_one]
      _ = L^(-1 : ℝ)*L^(2-2*γ) := by
        rw [← Real.rpow_add hLp,← Real.rpow_add hLp]
        congr 1
        ring
      _ = _ := by rw [Real.rpow_neg_one]

  have hb : (δ⁻¹*L^(-2*γ))*L/a ≤ δ⁻¹*L^(2-2*γ) := by
    apply (div_le_iff₀ ha).mpr
    calc
      _ = (δ⁻¹*L^(2-2*γ))*L⁻¹ := by rw [mul_assoc,hid]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hgap (by positivity)
  linarith only [hb,hA]

/-- Absorb the translated-box endpoint and combine its dimension power. -/
theorem box_times_rpow_bound {L A B e : ℝ} (n : ℕ) (hL : 1 ≤ L)
    (hA : 0 ≤ A) (hB : 0 ≤ B) :
    (2*L+1)^n*(A*B*L^e) ≤ (3^n*A)*B*L^((n : ℝ)+e) := by
  have hLp : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have hb : (2*L+1)^n ≤ 3^n*L^n := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by positivity) (by linarith only [hL]) n
  calc
    _ ≤ (3^n*L^n)*(A*B*L^e) := mul_le_mul_of_nonneg_right hb (by positivity)
    _ = (3^n*A)*B*(L^(n : ℝ)*L^e) := by rw [Real.rpow_natCast]; ring
    _ = _ := by rw [← Real.rpow_add hLp]

end WaveTurbulence.CountLemmas
