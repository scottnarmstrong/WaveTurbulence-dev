/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.VdCB.CircleIntegerSource
public import WaveTurbulence.Foundations.Counting.LatticeDisc

/-! # The actual right octant source block -/

public section

open Set
open WaveTurbulence.NumberTheory WaveTurbulence.Counting

namespace WaveTurbulence.VdCB

/-- The right half of the endpoint dyadic block, with its exact open boundaries. -/
@[expose] noncomputable def circleRightBlock (R c U : ℝ) : Finset ℤ :=
  (Counting.integerInterval (c - R) (c + R)).filter (fun x : ℤ =>
    R / Real.sqrt 2 < (x : ℝ) - c ∧ U < R - ((x : ℝ) - c) ∧
      R - ((x : ℝ) - c) ≤ 2 * U)

@[simp] theorem mem_circleRightBlock (x : ℤ) (R c U : ℝ) :
    x ∈ circleRightBlock R c U ↔
      c - R ≤ (x : ℝ) ∧ (x : ℝ) ≤ c + R ∧
      R / Real.sqrt 2 < (x : ℝ) - c ∧ U < R - ((x : ℝ) - c) ∧
      R - ((x : ℝ) - c) ≤ 2 * U := by
  simp only [circleRightBlock, Finset.mem_filter, Counting.mem_integerInterval, and_assoc]

/-- The actual right block has the transformed exponent-pair scale. -/
theorem norm_sum_circleRightBlock_le {R c U h : ℝ} (hR : 0 < R)
    (hU : 1 ≤ U) (hh : 1 ≤ h) :
    ‖∑ x ∈ circleRightBlock R c U, expPhase (h * circleHeight R c x)‖ ≤
      (circleBConstant + 1) * circleBScale R h U := by
  classical
  by_cases hS : (circleRightBlock R c U).Nonempty
  · obtain ⟨x, hx⟩ := hS
    have hx' := (mem_circleRightBlock x R c U).mp hx
    have hxoct : R + c - (x : ℝ) ≤ R * (1 - 1 / Real.sqrt 2) := by
      simp only [div_eq_mul_inv, one_mul] at hx' ⊢
      nlinarith only [hx'.2.2.1]
    have h3 := three_mul_le_of_circle_octant hR.le hxoct
    have hUR : 3 * U ≤ R := by linarith only [hx'.2.2.2.1, h3]
    have hs := norm_sum_circleColumnPhase_convex_le (c := c) hU hUR hh (circleRightBlock R c U)
      (fun x hx y hy z hxz hzy => by
        have hx' := (mem_circleRightBlock x R c U).mp hx
        have hy' := (mem_circleRightBlock y R c U).mp hy
        have hxz' : (x : ℝ) ≤ z := by exact_mod_cast hxz
        have hzy' : (z : ℝ) ≤ y := by exact_mod_cast hzy
        apply (mem_circleRightBlock z R c U).mpr
        exact ⟨by linarith only [hx'.1, hxz'], by linarith only [hy'.2.1, hzy'],
          by linarith only [hx'.2.2.1, hxz'], by linarith only [hy'.2.2.2.1, hzy'],
          by linarith only [hx'.2.2.2.2, hxz']⟩)
      (fun x hx => by
        have hx' := (mem_circleRightBlock x R c U).mp hx
        constructor <;> linarith only [hx'.2.2.2.1, hx'.2.2.2.2])
      (fun x hx => by
        have hx' := (mem_circleRightBlock x R c U).mp hx
        simp only [div_eq_mul_inv, one_mul] at hx' ⊢
        nlinarith only [hx'.2.2.1])
    simpa only [circleColumnPhase, circleHeight] using hs
  · rw [Finset.not_nonempty_iff_eq_empty.mp hS, Finset.sum_empty, norm_zero]
    apply mul_nonneg
    · unfold circleBConstant; positivity
    · unfold circleBScale; positivity

end WaveTurbulence.VdCB
