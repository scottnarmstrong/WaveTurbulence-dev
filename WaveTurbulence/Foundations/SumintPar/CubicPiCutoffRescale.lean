/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.SumintPar.CubicCutoffRescale
import Mathlib.Tactic

/-!
# The width-four cubic sum in three-coordinate function notation

The normal source input is a function on Fin 3. Reindexing by the literal
triple equivalence identifies it with the landed tuple-indexed cubic sum.
-/

@[expose] public section
set_option autoImplicit false

open WithLp

namespace WaveTurbulence.SumintPar

/-- A three-coordinate function is exactly a nested triple. -/
@[expose] def tripleInputEquiv (α : Type*) : (Fin 3 → α) ≃ α × α × α where
  toFun n := (n 0,n 1,n 2)
  invFun n := ![n.1,n.2.1,n.2.2]
  left_inv n := by funext j; fin_cases j <;> rfl
  right_inv n := rfl

/-- Exact width-four rescaling for the three-function-coordinate cubic sum. -/
theorem inputCutoff_cubic_pi_sum_eq {d : ℕ} (L t s : ℝ) (sel : Bool)
    (a : Fin 3 → Fin d → ℝ) (ξ : Fin 3 → Mom d) :
    (∑' n : Fin 3 → Fin d → ℤ,
      ((∏ j : Fin 3, inputCutoff (a j) (latticePoint L (n j)) : ℝ) : ℂ) *
      (Real.fourierChar (t*inner ℝ (latticePoint L (n 0)) (latticePoint L (n 1)) +
        s*WeylSums.cubicQuadraticForm sel (latticePoint L (n 0)) (latticePoint L (n 1)) (latticePoint L (n 2)) +
        ∑ j : Fin 3, inner ℝ (ξ j) (latticePoint L (n j))) : ℂ)) =
      WeylSums.cubicLatticeSum (4*L) (16*t) (16*s) sel
        ((1/4:ℝ) • toLp 2 (a 0)) ((1/4:ℝ) • toLp 2 (a 1)) ((1/4:ℝ) • toLp 2 (a 2))
        ((4:ℝ) • ξ 0) ((4:ℝ) • ξ 1) ((4:ℝ) • ξ 2) := by
  rw [← (tripleInputEquiv (Fin d → ℤ)).symm.tsum_eq]
  have hh := inputCutoff_cubic_sum_eq L t s sel (a 0) (a 1) (a 2) (ξ 0) (ξ 1) (ξ 2)
  refine Eq.trans ?_ hh
  apply tsum_congr
  intro q
  apply congrArg₂ (fun z w : ℂ => z*w)
  · apply congrArg (fun z : ℝ => (z : ℂ))
    rw [Fin.prod_univ_three]
    rfl
  · apply congrArg (fun z : ℝ => (Real.fourierChar z : ℂ))
    rw [Fin.sum_univ_three]
    change t*inner ℝ (latticePoint L q.1) (latticePoint L q.2.1) +
      s*WeylSums.cubicQuadraticForm sel (latticePoint L q.1) (latticePoint L q.2.1) (latticePoint L q.2.2) +
      (inner ℝ (ξ 0) (latticePoint L q.1)+inner ℝ (ξ 1) (latticePoint L q.2.1)+
        inner ℝ (ξ 2) (latticePoint L q.2.2)) = _
    ring

end WaveTurbulence.SumintPar
