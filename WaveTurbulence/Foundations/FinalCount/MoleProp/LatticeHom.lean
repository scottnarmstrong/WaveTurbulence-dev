/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.MoleProp.StarEquations
public import WaveTurbulence.Foundations.FinalCount.Degen.LatticeLabels
import Mathlib.Tactic

/-! # The actual frozen lattice-point function as an additive homomorphism -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.MoleProp

noncomputable def latticePointHom {d : ℕ} (L : ℝ) : (Fin d → ℤ) →+ Mom d where
  toFun := latticePoint L
  map_zero' := by ext j; simp [latticePoint]
  map_add' := WeylSums.latticePoint_add_eq L

theorem latticePointHom_injective {d : ℕ} {L : ℝ} (hL : L ≠ 0) :
    Function.Injective (latticePointHom (d := d) L) := by
  intro a b h
  change latticePoint L a = latticePoint L b at h
  exact Degen.coset_label_injective hL (0 : Mom d) (by simpa only [zero_add] using h)

@[simp] theorem latticePointHom_apply {d : ℕ} (L : ℝ) (n : Fin d → ℤ) :
    latticePointHom L n = latticePoint L n := rfl

theorem latticePoint_zsmul {d : ℕ} (L : ℝ) (z : ℤ) (n : Fin d → ℤ) :
    latticePoint L (z • n) = z • latticePoint L n :=
  (latticePointHom L).map_zsmul z n

end WaveTurbulence.MoleProp
