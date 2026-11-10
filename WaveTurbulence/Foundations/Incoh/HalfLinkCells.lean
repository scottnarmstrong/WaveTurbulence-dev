/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Incoh.LeafCellProfile
public import WaveTurbulence.Foundations.Incoh.LinkFactor

/-!
# Smooth half-width link cells and exact insertion of the analytic cutoff

The actual partition is supported where TARGET's fixed `χ₀` equals one.
Thus multiplying by the analytic link cutoff changes no localized term.
-/

public section
noncomputable section
open scoped ContDiff

namespace WaveTurbulence.Incoh

/-- Actual center of a half-width cell, on the half-integer lattice. -/
@[expose] def halfCellCenter {d : ℕ} (c : Fin d → ℤ) : Mom d := (1 / 2 : ℝ) • NTSP.intVec c

/-- The literal smooth partition in link momentum variables, at half the leaf-cell width. -/
@[expose] def halfLinkCell {d : ℕ} (c : Fin d → ℤ) (x : Mom d) : ℂ :=
  (ApproxNT.thetaMom d ((2 : ℝ) • x - NTSP.intVec c) : ℂ)

/-- Every nonzero half-cell lies where the fixed analytic cutoff is identically one. -/
theorem latticeCutoff_eq_one_of_halfLinkCell_ne_zero {d : ℕ} {c : Fin d → ℤ} {x : Mom d}
    (hx : halfLinkCell c x ≠ 0) : WeylSums.latticeCutoff (x - halfCellCenter c) = 1 := by
  have hθ : ApproxNT.thetaMom d ((2 : ℝ) • x - NTSP.intVec c) ≠ 0 := by
    intro h
    exact hx (by simp only [halfLinkCell, h, Complex.ofReal_zero])
  unfold WeylSums.latticeCutoff
  apply Finset.prod_eq_one
  intro i _
  apply Fourier.chi0_eq_one
  have hi := ApproxNT.abs_lt_one_of_thetaMom_ne_zero hθ i
  have he : ((2 : ℝ) • x - NTSP.intVec c) i = 2 * (x - halfCellCenter c) i := by
    simp only [halfCellCenter, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]
    ring
  rw [he, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)] at hi
  linarith only [hi]

/-- Exact cutoff insertion, including zero cells and all support boundaries. -/
theorem halfLinkCell_mul_latticeCutoff {d : ℕ} (c : Fin d → ℤ) (x : Mom d) :
    halfLinkCell c x * (WeylSums.latticeCutoff (x - halfCellCenter c) : ℂ) = halfLinkCell c x := by
  by_cases hx : halfLinkCell c x = 0
  · rw [hx, zero_mul]
  · rw [latticeCutoff_eq_one_of_halfLinkCell_ne_zero hx, Complex.ofReal_one, mul_one]

end WaveTurbulence.Incoh
