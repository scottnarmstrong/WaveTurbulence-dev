/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.MoleProp.DeletionGainScalar
import Mathlib.Tactic

/-! # The quantitative margin in DH23 A.3(5) gives the terminal gain -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.MoleProp

theorem K4_deletion_scalar_le_gain {L a g η δ B C : ℝ}
    (hL : 1 ≤ L) (ha : (101 : ℝ)/100*g ≤ 3*a) (hη : η < g/100)
    (hδ : δ ∈ Set.Ioc (0 : ℝ) 1) (hB : 0 ≤ B) (hB1 : B ≤ 1) (hC : 0 ≤ C)
    (hlarge : ((C+1)*(δ^3)⁻¹)^((g/100-η)⁻¹) ≤ L) :
    (⌈C*(δ⁻¹)^3*L^(3*a-(101 : ℝ)/100*g)⌉₊ : ℝ)*L^(-3*a)*B^3 ≤ L^(-g-η) := by
  have hδ3 : δ^3 ∈ Set.Ioc (0 : ℝ) 1 :=
    ⟨pow_pos hδ.1 _,pow_le_one₀ hδ.1.le hδ.2⟩
  have hh := pair_deletion_scalar_le_gain (a := 3*a) (η := (101 : ℝ)/100*g)
    (ε := g/100-η) (B := B^3) hL ha (sub_pos.mpr hη) hδ3 (pow_nonneg hB 3) (pow_le_one₀ hB hB1) hC hlarge
  rw [show (101 : ℝ)/100*g-(g/100-η) = g+η by ring] at hh
  simpa only [inv_pow,show -(g+η) = -g-η by ring,show -(3*a) = -3*a by ring] using hh

end WaveTurbulence.MoleProp
