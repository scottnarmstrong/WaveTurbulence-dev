/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.WaveB.FrozenB1
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle

/-! # The actual garden sign as a unit-modulus analytic source sign -/

public section
noncomputable section
namespace WaveTurbulence.IncohInst

/-- The global source garden factor always has norm one. -/
theorem norm_garden_zeta {w : ℕ} (G : Garden w) : ‖G.zeta‖ = 1 := by
  unfold Garden.zeta
  rw [norm_prod]
  apply Finset.prod_eq_one
  intro b _
  rcases Int.units_eq_one_or (G.sign b.toNode) with h | h <;> simp [h]

/-- The exact global source sign, retaining its value in the analytic carrier. -/
@[expose] def gardenCircle {w : ℕ} (G : Garden w) : Circle :=
  ⟨G.zeta, mem_sphere_zero_iff_norm.mpr (norm_garden_zeta G)⟩

@[simp] theorem gardenCircle_coe {w : ℕ} (G : Garden w) : (gardenCircle G : ℂ) = G.zeta := rfl

end WaveTurbulence.IncohInst
