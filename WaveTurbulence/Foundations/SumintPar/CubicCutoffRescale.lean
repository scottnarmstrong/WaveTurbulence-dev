/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.SumintPar.BilinearCutoffRescale
import Mathlib.Tactic

/-!
# Exact width-four cubic rescaling

Both source quadratic forms are homogeneous of degree two. The same
mesh and frequency rescaling therefore works for both normal-block forms.
-/

@[expose] public section
set_option autoImplicit false

open WithLp
open scoped InnerProductSpace

namespace WaveTurbulence.SumintPar

/-- Both normal quadratic forms have the required exact scaling. -/
theorem cubicQuadraticForm_smul {d : ℕ} (sel : Bool) (x y z : Mom d) (a : ℝ) :
    WeylSums.cubicQuadraticForm sel (a • x) (a • y) (a • z) =
      a^2 * WeylSums.cubicQuadraticForm sel x y z := by
  cases sel <;> simp [WeylSums.cubicQuadraticForm, ← smul_add, ← smul_sub,
    inner_smul_left, inner_smul_right] <;> ring

/-- Exact conversion of the inserted cubic lattice sum to the landed sum. -/
theorem inputCutoff_cubic_sum_eq {d : ℕ} (L t s : ℝ) (sel : Bool)
    (a b c : Fin d → ℝ) (ξ ζ ω : Mom d) :
    (∑' p : (Fin d → ℤ) × (Fin d → ℤ) × (Fin d → ℤ),
      ((inputCutoff a (latticePoint L p.1) * inputCutoff b (latticePoint L p.2.1) *
        inputCutoff c (latticePoint L p.2.2) : ℝ) : ℂ) *
        (Real.fourierChar (t * inner ℝ (latticePoint L p.1) (latticePoint L p.2.1) +
          s * WeylSums.cubicQuadraticForm sel (latticePoint L p.1)
            (latticePoint L p.2.1) (latticePoint L p.2.2) +
          inner ℝ ξ (latticePoint L p.1) + inner ℝ ζ (latticePoint L p.2.1) +
          inner ℝ ω (latticePoint L p.2.2)) : ℂ)) =
      WeylSums.cubicLatticeSum (4*L) (16*t) (16*s) sel
        ((1/4:ℝ) • toLp 2 a) ((1/4:ℝ) • toLp 2 b) ((1/4:ℝ) • toLp 2 c)
        ((4:ℝ) • ξ) ((4:ℝ) • ζ) ((4:ℝ) • ω) := by
  unfold WeylSums.cubicLatticeSum
  apply tsum_congr
  intro p
  simp only [Complex.ofReal_mul]
  rw [inputCutoff_rescale, inputCutoff_rescale, inputCutoff_rescale]
  apply congrArg₂ (fun x y : ℂ => x*y)
  · rfl
  · unfold WeylSums.e
    rw [Real.fourierChar_apply]
    have he : t * inner ℝ (latticePoint L p.1) (latticePoint L p.2.1) +
        s * WeylSums.cubicQuadraticForm sel (latticePoint L p.1)
          (latticePoint L p.2.1) (latticePoint L p.2.2) +
        inner ℝ ξ (latticePoint L p.1) + inner ℝ ζ (latticePoint L p.2.1) +
        inner ℝ ω (latticePoint L p.2.2) =
        (16*t) * inner ℝ (latticePoint (4*L) p.1) (latticePoint (4*L) p.2.1) +
        (16*s) * WeylSums.cubicQuadraticForm sel (latticePoint (4*L) p.1)
          (latticePoint (4*L) p.2.1) (latticePoint (4*L) p.2.2) +
        inner ℝ ((4:ℝ) • ξ) (latticePoint (4*L) p.1) +
        inner ℝ ((4:ℝ) • ζ) (latticePoint (4*L) p.2.1) +
        inner ℝ ((4:ℝ) • ω) (latticePoint (4*L) p.2.2) := by
      rw [latticePoint_four_mul L p.1, latticePoint_four_mul L p.2.1,
        latticePoint_four_mul L p.2.2, cubicQuadraticForm_smul]
      simp only [inner_smul_left, inner_smul_right, conj_trivial]
      ring
    rw [he]

end WaveTurbulence.SumintPar
