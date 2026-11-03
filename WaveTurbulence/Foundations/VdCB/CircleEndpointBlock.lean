/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.VdCB.CircleRightBlock

/-! # The two-sided endpoint block required by the circle counting transfer -/

public section

open WaveTurbulence.NumberTheory WaveTurbulence.Counting

namespace WaveTurbulence.VdCB

/-- The exact endpoint block, including the counting API's strict inequalities. -/
@[expose] noncomputable def circleEndpointBlock (R c U : ℝ) : Finset ℤ :=
  (Counting.integerInterval (c - R) (c + R)).filter (fun x : ℤ =>
    R / Real.sqrt 2 < |(x : ℝ) - c| ∧ U < R - |(x : ℝ) - c| ∧
      R - |(x : ℝ) - c| ≤ 2 * U)

private theorem right_positive {R c U : ℝ} (hR : 0 < R) {x : ℤ}
    (hx : x ∈ circleRightBlock R c U) : 0 < (x : ℝ) - c :=
  (div_pos hR (Real.sqrt_pos.mpr (by norm_num))).trans
    ((mem_circleRightBlock x R c U).mp hx).2.2.1

/-- The two octants are related by reflection of the integer lattice. -/
theorem circleEndpointBlock_eq_union {R c U : ℝ} (hR : 0 < R) :
    circleEndpointBlock R c U = circleRightBlock R c U ∪
      (circleRightBlock R (-c) U).image (fun x => -x) := by
  classical
  ext x
  simp only [circleEndpointBlock, Finset.mem_filter, Counting.mem_integerInterval,
    Finset.mem_union, Finset.mem_image]
  constructor
  · rintro ⟨hx, hphase⟩
    by_cases hsign : 0 ≤ (x : ℝ) - c
    · left
      rw [abs_of_nonneg hsign] at hphase
      exact (mem_circleRightBlock x R c U).mpr ⟨hx.1, hx.2, hphase⟩
    · right
      rw [abs_of_neg (lt_of_not_ge hsign)] at hphase
      refine ⟨-x, ?_, neg_neg x⟩
      apply (mem_circleRightBlock (-x) R (-c) U).mpr
      push_cast
      exact ⟨by linarith only [hx.2], by linarith only [hx.1],
        by linarith only [hphase.1], by linarith only [hphase.2.1],
        by linarith only [hphase.2.2]⟩
  · rintro (hx | ⟨y, hy, hxy⟩)
    · have hh := (mem_circleRightBlock x R c U).mp hx
      rw [abs_of_pos (right_positive hR hx)]
      exact ⟨⟨hh.1, hh.2.1⟩, hh.2.2⟩
    · subst x
      have hh := (mem_circleRightBlock y R (-c) U).mp hy
      have hp := right_positive hR hy
      push_cast
      rw [abs_of_neg (by linarith only [hp] : -(y : ℝ) - c < 0)]
      refine ⟨⟨?_, ?_⟩, ?_, ?_, ?_⟩ <;> linarith only [hh.1, hh.2.1, hh.2.2.1, hh.2.2.2.1, hh.2.2.2.2]

/-- The two reflected right blocks are disjoint. -/
theorem disjoint_circleRightBlock_reflected {R c U : ℝ} (hR : 0 < R) :
    Disjoint (circleRightBlock R c U) ((circleRightBlock R (-c) U).image (fun x => -x)) := by
  classical
  apply Finset.disjoint_left.mpr
  intro x hx hy
  obtain ⟨y, hy, hxy⟩ := Finset.mem_image.mp hy
  have hx0 := right_positive hR hx
  have hy0 := right_positive hR hy
  subst x
  push_cast at hx0
  linarith only [hx0, hy0]

/-- Unconditional actual endpoint-block estimate for the pair `(11/30,16/30)`.
This is the direct circle-family form of the B transform consumed by counting. -/
theorem norm_sum_circleEndpointBlock_le {R c U h : ℝ} (hR : 0 < R)
    (hU : 1 ≤ U) (hh : 1 ≤ h) :
    ‖∑ x ∈ circleEndpointBlock R c U, expPhase (h * circleHeight R c x)‖ ≤
      (2 * (circleBConstant + 1)) * circleBScale R h U := by
  classical
  rw [circleEndpointBlock_eq_union hR, Finset.sum_union (disjoint_circleRightBlock_reflected hR)]
  have hreflect : (∑ x ∈ (circleRightBlock R (-c) U).image (fun x => -x),
      expPhase (h * circleHeight R c x)) =
      ∑ x ∈ circleRightBlock R (-c) U, expPhase (h * circleHeight R (-c) x) := by
    rw [Finset.sum_image (by intro a _ b _ hab; exact neg_injective hab)]
    apply Finset.sum_congr rfl
    intro x _
    congr 2
    unfold circleHeight
    push_cast
    congr 1
    ring
  rw [hreflect]
  have hr := norm_sum_circleRightBlock_le (c := c) hR hU hh
  have hl := norm_sum_circleRightBlock_le (c := -c) hR hU hh
  calc
    _ ≤ ‖∑ x ∈ circleRightBlock R c U, expPhase (h * circleHeight R c x)‖ +
        ‖∑ x ∈ circleRightBlock R (-c) U, expPhase (h * circleHeight R (-c) x)‖ := norm_add_le _ _
    _ ≤ (circleBConstant + 1) * circleBScale R h U +
        (circleBConstant + 1) * circleBScale R h U := add_le_add hr hl
    _ = _ := by ring

end WaveTurbulence.VdCB
