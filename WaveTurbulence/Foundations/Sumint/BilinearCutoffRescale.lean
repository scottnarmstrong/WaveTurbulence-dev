/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Sumint.CutoffRescale
public import WaveTurbulence.Foundations.WeylSums.MinorArcSums
import Mathlib.Tactic

/-!
# Exact width-four bilinear rescaling

The inserted input cutoffs yield the landed bilinear sum at mesh `4L`.
Linear frequencies acquire a factor four and the bilinear time frequency
a factor sixteen. No change of integer summation variables is involved.
-/

public section

open WithLp
open scoped InnerProductSpace

namespace WaveTurbulence.Sumint

/-- Exact conversion of the inserted bilinear lattice sum to the landed sum. -/
theorem inputCutoff_bilinear_sum_eq {d : ℕ} (L s : ℝ)
    (a b : Fin d → ℝ) (ξ ζ : Mom d) :
    (∑' p : (Fin d → ℤ) × (Fin d → ℤ),
      ((inputCutoff a (latticePoint L p.1) * inputCutoff b (latticePoint L p.2) : ℝ) : ℂ) *
        (Real.fourierChar (inner ℝ (latticePoint L p.1) ξ +
          inner ℝ (latticePoint L p.2) ζ +
          s * inner ℝ (latticePoint L p.1) (latticePoint L p.2)) : ℂ)) =
      WeylSums.bilinearLatticeSum (4*L) (16*s)
        ((1/4:ℝ) • toLp 2 a) ((1/4:ℝ) • toLp 2 b) ((4:ℝ) • ξ) ((4:ℝ) • ζ) := by
  unfold WeylSums.bilinearLatticeSum
  apply tsum_congr
  intro p
  have ha := inputCutoff_rescale L a p.1
  have hb := inputCutoff_rescale L b p.2
  simp only [Complex.ofReal_mul] at ⊢
  rw [ha, hb]
  apply congrArg₂ (fun x y : ℂ => x*y)
  · rfl
  · unfold WeylSums.e
    rw [Real.fourierChar_apply]
    congr 1
    have he : inner ℝ (latticePoint L p.1) ξ + inner ℝ (latticePoint L p.2) ζ +
        s * inner ℝ (latticePoint L p.1) (latticePoint L p.2) =
        inner ℝ (latticePoint (4*L) p.1) ((4:ℝ) • ξ) +
        inner ℝ (latticePoint (4*L) p.2) ((4:ℝ) • ζ) +
        (16*s) * inner ℝ (latticePoint (4*L) p.1) (latticePoint (4*L) p.2) := by
      rw [latticePoint_four_mul L p.1, latticePoint_four_mul L p.2]
      simp only [inner_smul_left, inner_smul_right, conj_trivial]
      ring
    rw [he]

end WaveTurbulence.Sumint
