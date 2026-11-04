/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Incoh.SmoothLeafCells
public import WaveTurbulence.Foundations.WeylSums.ScaledSobolevCutoff

/-!
# Actual translated smooth momentum-cell profiles

Their support and derivative-integral bounds are uniform in the center.
The profile is the landed tensor partition, with no assumed norm fields.
-/

public section
noncomputable section
open MeasureTheory Set
open scoped ContDiff

namespace WaveTurbulence.Incoh

/-- The complex-valued smooth profile at an arbitrary momentum center. -/
@[expose] def leafCellProfile (d : ℕ) (c x : Mom d) : ℂ :=
  (ApproxNT.thetaMom d (x - c) : ℂ)

@[fun_prop] theorem contDiff_leafCellProfile (d : ℕ) (c : Mom d) :
    ContDiff ℝ ∞ (leafCellProfile d c) :=
  Complex.ofRealCLM.contDiff.comp (ApproxNT.contDiff_thetaMom.comp (by fun_prop))

theorem hasCompactSupport_leafCellProfile (d : ℕ) (c : Mom d) :
    HasCompactSupport (leafCellProfile d c) := by
  have ht : HasCompactSupport (fun x : Mom d => ApproxNT.thetaMom d (x - c)) :=
    ApproxNT.hasCompactSupport_thetaMom.comp_homeomorph (Homeomorph.subRight c)
  exact ht.comp_left (g := fun r : ℝ => (r : ℂ)) (by simp)

/-- Even at support boundaries, the actual cell stays in the stated fixed-radius ball. -/
theorem tsupport_leafCellProfile_subset (d : ℕ) (c : Mom d) :
    tsupport (leafCellProfile d c) ⊆ {x : Mom d | ‖x - c‖ ≤ Real.sqrt d} := by
  apply closure_minimal
  · intro x hx
    have hθ : ApproxNT.thetaMom d (x - c) ≠ 0 := by
      intro hz
      exact hx (by simp only [leafCellProfile, hz, Complex.ofReal_zero])
    have hs := ApproxNT.thetaMom_support_subset hθ
    simpa only [mem_ofPred_eq, Metric.mem_closedBall, dist_zero_right] using hs
  · exact isClosed_le (by fun_prop) continuous_const

/-- The landed cutoff translation estimate supplies a center-independent Sobolev bound. -/
theorem derivativeL1Sum_leafCellProfile_le (d N : ℕ) (c : Mom d) :
    Fourier.derivativeL1Sum N (leafCellProfile d c) ≤
      Fourier.derivativeL1Sum N (leafCellProfile d 0) := by
  have he : WeylSums.scaledTranslatedCutoff (leafCellProfile d 0) 1 c = leafCellProfile d c := by
    funext x
    simp only [WeylSums.scaledTranslatedCutoff, inv_one, one_smul, leafCellProfile, sub_zero]
  simpa only [he, one_pow, one_mul] using
    WeylSums.derivativeL1Sum_scaledTranslated_le (hasCompactSupport_leafCellProfile d 0)
      ((contDiff_leafCellProfile d 0).of_le (by simp : (N : ℕ∞ω) ≤ ∞)) (le_refl (1 : ℝ)) c

end WaveTurbulence.Incoh
