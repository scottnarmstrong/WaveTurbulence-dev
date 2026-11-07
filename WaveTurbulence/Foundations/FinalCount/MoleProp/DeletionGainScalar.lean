/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.MoleProp.DeletionScalars
import Mathlib.Tactic

/-! # Retaining a power saving from the genuine LG pair estimate -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.MoleProp

theorem pair_deletion_scalar_le_gain {L a η ε δ B C : ℝ}
    (hL : 1 ≤ L) (ha : η ≤ a) (hε : 0 < ε)
    (hδ : δ ∈ Set.Ioc (0 : ℝ) 1) (hB : 0 ≤ B) (hB1 : B ≤ 1) (hC : 0 ≤ C)
    (hlarge : ((C+1)*δ⁻¹)^(ε⁻¹) ≤ L) :
    (⌈C*δ⁻¹*L^(a-η)⌉₊ : ℝ)*L^(-a)*B ≤ L^(-(η-ε)) := by
  have hLp : 0 < L := zero_lt_one.trans_le hL
  have hs := pair_deletion_scalar_le_one (a := a-η+ε) (η := ε) hL
    (by linarith only [ha]) hε hδ hB hB1 hC hlarge
  rw [show a-η+ε-ε = a-η by ring] at hs
  have hh := mul_le_mul_of_nonneg_right hs (Real.rpow_nonneg hLp.le (-(η-ε)))
  have hid : L^(-(a-η+ε))*L^(-(η-ε)) = L^(-a) := by
    rw [← Real.rpow_add hLp]
    congr 1 <;> ring
  calc
    _ = ((⌈C*δ⁻¹*L^(a-η)⌉₊ : ℝ)*L^(-(a-η+ε))*B)*L^(-(η-ε)) := by
      calc
        _ = (⌈C*δ⁻¹*L^(a-η)⌉₊ : ℝ)*(L^(-(a-η+ε))*L^(-(η-ε)))*B := by rw [hid]
        _ = _ := by ring
    _ ≤ 1*L^(-(η-ε)) := hh
    _ = _ := one_mul _

end WaveTurbulence.MoleProp
