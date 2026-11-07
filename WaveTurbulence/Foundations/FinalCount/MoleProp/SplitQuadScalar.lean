/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.MoleProp.DeletionScalars
import Mathlib.Tactic

/-! # Uniform large-L absorption for the direct beta-plus-removal count

The side size N stays outside the large-L threshold. Its polynomial loss
is accounted for by discarded atoms, never by assuming N is small.
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.MoleProp

theorem split_quad_scalar_le_gain {L a η δ B C N : ℝ}
    (hL : 1 ≤ L) (ha : η ≤ a) (hη : 0 < η) (hN : 1 ≤ N)
    (hδ : δ ∈ Set.Ioc (0 : ℝ) 1) (hB : 0 ≤ B) (hB1 : B ≤ 1) (hC : 0 ≤ C)
    (hlarge : ((C+1)*(δ⁻¹)^2)^(η⁻¹) ≤ L) :
    (⌈C*N^2*(δ⁻¹)^2*L^(2*(a-η))⌉₊ : ℝ)*L^(-2*a)*B^2 ≤ N^2*L^(-η) := by
  have hLp : 0 < L := zero_lt_one.trans_le hL
  have hD : 1 ≤ δ⁻¹ := (one_le_inv₀ hδ.1).mpr hδ.2
  have hA : 1 ≤ N^2*(δ⁻¹)^2*L^(2*(a-η)) :=
    one_le_mul_of_one_le_of_one_le
      (one_le_mul_of_one_le_of_one_le (one_le_pow₀ hN) (one_le_pow₀ hD))
      (Real.one_le_rpow hL (by linarith only [ha]))
  have hk : (⌈C*N^2*(δ⁻¹)^2*L^(2*(a-η))⌉₊ : ℝ) ≤
      (C+1)*(N^2*(δ⁻¹)^2*L^(2*(a-η))) := by
    simpa only [mul_assoc] using ceil_mul_scale_le hC hA
  have hK0 : 0 ≤ (C+1)*(δ⁻¹)^2 := mul_nonneg (by linarith only [hC]) (sq_nonneg _)
  have hp := Real.rpow_le_rpow (Real.rpow_nonneg hK0 _) hlarge hη.le
  rw [← Real.rpow_mul hK0,inv_mul_cancel₀ hη.ne',Real.rpow_one] at hp
  have hconst : (C+1)*(δ⁻¹)^2*L^(-η) ≤ 1 := by
    rw [Real.rpow_neg hLp.le,← div_eq_mul_inv]
    exact (div_le_one (Real.rpow_pos_of_pos hLp η)).mpr hp
  have hBsq : B^2 ≤ 1 := pow_le_one₀ hB hB1
  have hm := mul_le_mul hk hBsq (sq_nonneg B) (by positivity : 0 ≤ (C+1)*(N^2*(δ⁻¹)^2*L^(2*(a-η))))
  have hm' := mul_le_mul_of_nonneg_right hm (Real.rpow_nonneg hLp.le (-2*a))
  have hpow : L^(2*(a-η))*L^(-2*a) = L^(-η)*L^(-η) := by
    rw [← Real.rpow_add hLp,← Real.rpow_add hLp]
    congr 1 <;> ring
  calc
    _ = ((⌈C*N^2*(δ⁻¹)^2*L^(2*(a-η))⌉₊ : ℝ)*B^2)*L^(-2*a) := by ring
    _ ≤ _ := hm'
    _ = ((C+1)*(δ⁻¹)^2*L^(-η))*(N^2*L^(-η)) := by
      calc
        _ = (C+1)*N^2*(δ⁻¹)^2*(L^(2*(a-η))*L^(-2*a)) := by ring
        _ = _ := by rw [hpow]; ring
    _ ≤ 1*(N^2*L^(-η)) := mul_le_mul_of_nonneg_right hconst (by positivity)
    _ = _ := one_mul _

end WaveTurbulence.MoleProp
