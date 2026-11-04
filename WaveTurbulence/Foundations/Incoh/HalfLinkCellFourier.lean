/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Incoh.HalfLinkCells
public import WaveTurbulence.Foundations.Fourier.SchwartzNorm
public import WaveTurbulence.Foundations.Fourier.TimeFourier

/-!
# Uniform Fourier norms of the actual half-width link cells

TARGET (incohproof8). Each cell is a translate of one fixed smooth compact
profile. Its Fourier norm is therefore finite and independent of its center.
-/

public section
noncomputable section
open MeasureTheory WithLp
open scoped ContDiff ENNReal

namespace WaveTurbulence.Incoh

@[fun_prop] theorem contDiff_halfLinkCell {d : ℕ} (c : Fin d → ℤ) :
    ContDiff ℝ ∞ (halfLinkCell c) :=
  Complex.ofRealCLM.contDiff.comp (ApproxNT.contDiff_thetaMom.comp (by fun_prop))

/-- The actual half-width profile has compact support. -/
theorem hasCompactSupport_halfLinkCell {d : ℕ} (c : Fin d → ℤ) :
    HasCompactSupport (halfLinkCell c) := by
  have h := (hasCompactSupport_leafCellProfile d (NTSP.intVec c)).comp_homeomorph
    (Homeomorph.smulOfNeZero (2 : ℝ) (by norm_num) : Mom d ≃ₜ Mom d)
  exact h

/-- Exact translation of the fixed half-width profile. -/
theorem halfLinkCell_eq_translate_zero {d : ℕ} (c : Fin d → ℤ) (x : Mom d) :
    halfLinkCell c x = halfLinkCell (0 : Fin d → ℤ) (x - halfCellCenter c) := by
  unfold halfLinkCell halfCellCenter
  have he : (2 : ℝ) • (x - (1 / 2 : ℝ) • NTSP.intVec c) =
      (2 : ℝ) • x - NTSP.intVec c := by
    rw [smul_sub, smul_smul]
    norm_num
  rw [he]
  have hz : NTSP.intVec (0 : Fin d → ℤ) = (0 : Mom d) := by
    ext i
    simp [NTSP.intVec]
  rw [hz, sub_zero]

/-- Coordinate form of the literal translated half-cell. -/
theorem halfLinkCell_coordinates_eq_translate_zero {d : ℕ} (c : Fin d → ℤ) :
    (fun x : Fin d → ℝ => halfLinkCell c (toLp 2 x)) =
      fun x => halfLinkCell (0 : Fin d → ℤ) (toLp 2 (x + (-ofLp (halfCellCenter c)))) := by
  funext x
  rw [halfLinkCell_eq_translate_zero]
  congr 1

/-- The pointwise Fourier amplitude is independent of the translating center. -/
theorem enorm_timeFourier_halfLinkCell_eq {d : ℕ} (c : Fin d → ℤ) (ξ : Fin d → ℝ) :
    ‖Fourier.timeFourier (fun x : Fin d → ℝ => halfLinkCell c (toLp 2 x)) ξ‖ₑ =
      ‖Fourier.timeFourier (fun x : Fin d → ℝ => halfLinkCell (0 : Fin d → ℤ) (toLp 2 x)) ξ‖ₑ := by
  rw [halfLinkCell_coordinates_eq_translate_zero c,
    Fourier.timeFourier_translate
      (fun x : Fin d → ℝ => halfLinkCell (0 : Fin d → ℤ) (toLp 2 x))
      (-ofLp (halfCellCenter c)), Circle.enorm_smul]

/-- Every weighted Fourier norm of the actual profile is independent of its center. -/
theorem timeFourierNorm_halfLinkCell_eq {d : ℕ} (θ : ℝ) (c : Fin d → ℤ) :
    Fourier.timeFourierNorm θ (fun x : Fin d → ℝ => halfLinkCell c (toLp 2 x)) =
      Fourier.timeFourierNorm θ (fun x : Fin d → ℝ => halfLinkCell (0 : Fin d → ℤ) (toLp 2 x)) := by
  have he : (fun x : Fin d → ℝ => halfLinkCell c (toLp 2 x)) =
      fun x => halfLinkCell (0 : Fin d → ℤ) (toLp 2 (x + (-ofLp (halfCellCenter c)))) := by
    funext x
    rw [halfLinkCell_eq_translate_zero]
    congr 1
  rw [he]
  exact Fourier.timeFourierNorm_translate θ
    (fun x : Fin d → ℝ => halfLinkCell (0 : Fin d → ℤ) (toLp 2 x))
    (-ofLp (halfCellCenter c))

/-- Finite uniform Fourier norm, with no assumed Fourier bound. -/
theorem timeFourierNorm_halfLinkCell_lt_top {d : ℕ} (θ : ℝ) (c : Fin d → ℤ) :
    Fourier.timeFourierNorm θ (fun x : Fin d → ℝ => halfLinkCell c (toLp 2 x)) < ⊤ := by
  apply Fourier.timeFourierNorm_lt_top_of_smooth_compact
  · exact (hasCompactSupport_halfLinkCell c).comp_homeomorph
      (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin d => ℝ)).symm.toHomeomorph
  · exact (contDiff_halfLinkCell c).comp
      (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin d => ℝ)).symm.contDiff

end WaveTurbulence.Incoh
