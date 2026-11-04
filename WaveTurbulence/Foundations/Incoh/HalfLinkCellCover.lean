/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Incoh.HalfLinkCells
public import WaveTurbulence.Foundations.ApproxNT.Cells

/-!
# Uniformly many half-link cells meet a localized momentum ball

The finite integer boxes and their cardinality estimate are reused from
NT6. The count is independent of the center of the momentum ball.
-/

public section
noncomputable section

namespace WaveTurbulence.Incoh

/-- Actual possible half-cell indices for momenta in the specified localization ball. -/
@[expose] def halfLinkCellCover {d : ℕ} (a : Mom d) (R : ℝ) : Finset (Fin d → ℤ) :=
  ApproxNT.intBox ((2 : ℝ) • a) (2 * R + 1)

/-- Any nonzero cell meeting the localization ball belongs to the finite index cover. -/
theorem mem_halfLinkCellCover {d : ℕ} {a x : Mom d} {R : ℝ} {c : Fin d → ℤ}
    (hx : ‖x - a‖ ≤ R) (hc : halfLinkCell c x ≠ 0) : c ∈ halfLinkCellCover a R := by
  have hθ : ApproxNT.thetaMom d ((2 : ℝ) • x - NTSP.intVec c) ≠ 0 := by
    intro hz
    exact hc (by simp only [halfLinkCell, hz, Complex.ofReal_zero])
  apply ApproxNT.mem_intBox
  intro i
  have hxi : |x i - a i| ≤ R := by
    simpa only [PiLp.sub_apply, Real.norm_eq_abs] using (PiLp.norm_apply_le (x - a) i).trans hx
  have hci := ApproxNT.abs_lt_one_of_thetaMom_ne_zero hθ i
  simp only [PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul, NTSP.intVec_apply] at hci ⊢
  have he : (c i : ℝ) - 2 * a i = -(2 * x i - c i) + 2 * (x i - a i) := by ring
  rw [he]
  calc
    _ ≤ |2 * x i - c i| + 2 * |x i - a i| := by
      simpa only [abs_neg, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)] using
        abs_add_le (-(2 * x i - c i)) (2 * (x i - a i))
    _ ≤ 2 * R + 1 := by linarith only [hci, hxi]

/-- The number of admissible half-cells is uniform in the original localization center. -/
theorem card_halfLinkCellCover_le {d : ℕ} (a : Mom d) {R : ℝ} (hR : 0 ≤ R) :
    ((halfLinkCellCover a R).card : ℝ) ≤ (4 * R + 3) ^ d := by
  have h := ApproxNT.card_intBox_le ((2 : ℝ) • a) (show 0 ≤ 2 * R + 1 by positivity)
  have he : 2 * (2 * R + 1) + 1 = 4 * R + 3 := by ring
  simpa only [halfLinkCellCover, he] using h

end WaveTurbulence.Incoh
