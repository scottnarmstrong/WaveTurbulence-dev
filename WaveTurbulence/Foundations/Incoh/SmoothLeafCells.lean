/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.ApproxNT.Partition
public import Mathlib.Topology.Algebra.InfiniteSum.Basic

/-!
# Exact smooth momentum-cell decomposition of the leaf inputs

TARGET Step (2). The landed smooth integer partition is used literally;
no hard momentum restriction is substituted into the Fourier-L¹ argument.
-/

public section
noncomputable section
open MeasureTheory
open scoped ContDiff

namespace WaveTurbulence.Incoh

/-- The literal localized leaf input, with the landed smooth cell profile. -/
@[expose] def leafCell {d : ℕ} (f : Mom d → ℂ) (c : Fin d → ℤ) (x : Mom d) : ℂ :=
  f x * (ApproxNT.thetaMom d (x - NTSP.intVec c) : ℂ)

/-- At each point only finitely many actual cell factors can be nonzero. -/
theorem leafCell_eq_zero_of_notMem {d : ℕ} (f : Mom d → ℂ) (x : Mom d)
    {c : Fin d → ℤ} (hc : c ∉ ApproxNT.thetaSupport x) : leafCell f c x = 0 := by
  rw [leafCell, ApproxNT.thetaMom_sub_eq_zero hc, Complex.ofReal_zero, mul_zero]

/-- The actual smooth leaf cells sum to the original input, pointwise. -/
theorem hasSum_leafCell {d : ℕ} (f : Mom d → ℂ) (x : Mom d) :
    HasSum (fun c : Fin d → ℤ => leafCell f c x) (f x) := by
  have hs : HasSum (fun c : Fin d → ℤ => leafCell f c x)
      (∑ c ∈ ApproxNT.thetaSupport x, leafCell f c x) := hasSum_sum_of_ne_finset_zero
    (s := ApproxNT.thetaSupport x) (fun c hc => leafCell_eq_zero_of_notMem f x hc)
  convert hs using 1
  simp_rw [leafCell]
  rw [← Finset.mul_sum, ← Complex.ofReal_sum, ApproxNT.sum_thetaMom,
    Complex.ofReal_one, mul_one]

/-- Exact recovery of a leaf input from its countable smooth momentum cells. -/
theorem tsum_leafCell {d : ℕ} (f : Mom d → ℂ) (x : Mom d) :
    (∑' c : Fin d → ℤ, leafCell f c x) = f x := (hasSum_leafCell f x).tsum_eq

/-- Localization preserves the finite source smoothness order. -/
theorem contDiff_leafCell {d : ℕ} {K : ℕ} {f : Mom d → ℂ} (hf : ContDiff ℝ K f)
    (c : Fin d → ℤ) : ContDiff ℝ K (leafCell f c) := by
  have hθ : ContDiff ℝ ∞ (fun x : Mom d => (ApproxNT.thetaMom d (x - NTSP.intVec c) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (ApproxNT.contDiff_thetaMom.comp (by fun_prop))
  exact hf.mul (hθ.of_le (by simp))

/-- Every cell is compactly supported by its actual translated profile. -/
theorem hasCompactSupport_leafCell {d : ℕ} (f : Mom d → ℂ) (c : Fin d → ℤ) :
    HasCompactSupport (leafCell f c) := by
  have ht : HasCompactSupport (fun x : Mom d => ApproxNT.thetaMom d (x - NTSP.intVec c)) :=
    ApproxNT.hasCompactSupport_thetaMom.comp_homeomorph (Homeomorph.subRight (NTSP.intVec c))
  have hc : HasCompactSupport (fun x : Mom d => (ApproxNT.thetaMom d (x - NTSP.intVec c) : ℂ)) :=
    ht.comp_left (g := fun r : ℝ => (r : ℂ)) (by simp)
  exact hc.mul_left

end WaveTurbulence.Incoh
