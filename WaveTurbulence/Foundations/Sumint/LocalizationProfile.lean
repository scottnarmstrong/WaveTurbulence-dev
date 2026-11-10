/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Sumint.ShapeFacts
public import WaveTurbulence.Foundations.ApproxNT.Partition
import Mathlib.Tactic

/-!
# A half-mesh smooth localization for TARGET sumint Step 1

The landed partition is evaluated at twice the momentum. Each resulting
piece is supported in a half-unit coordinate cube, where the source χ₀
cutoff at the corresponding half-integer center is identically one.
-/

public section

open Finset
open scoped ContDiff

namespace WaveTurbulence.Sumint

/-- The smooth localization piece centered at `a/2`. -/
@[expose] noncomputable def localizationProfile {d : ℕ} (a : Fin d → ℤ) (x : Mom d) : ℝ :=
  ApproxNT.thetaMom d ((2 : ℝ) • x - NTSP.intVec a)

/-- Every localization piece is nonnegative. -/
theorem localizationProfile_nonneg {d : ℕ} (a : Fin d → ℤ) (x : Mom d) :
    0 ≤ localizationProfile a x := ApproxNT.thetaMom_nonneg _

/-- The profiles sum exactly to one, with an explicit finite active set at each point. -/
theorem sum_localizationProfile {d : ℕ} (x : Mom d) :
    ∑ a ∈ ApproxNT.thetaSupport ((2 : ℝ) • x), localizationProfile a x = 1 :=
  ApproxNT.sum_thetaMom _

/-- Outside the explicit active set every summand vanishes. -/
theorem localizationProfile_eq_zero {d : ℕ} (x : Mom d) {a : Fin d → ℤ}
    (ha : a ∉ ApproxNT.thetaSupport ((2 : ℝ) • x)) : localizationProfile a x = 0 :=
  ApproxNT.thetaMom_sub_eq_zero ha

/-- The localization functions are smooth. -/
theorem localizationProfile_contDiff {d : ℕ} (a : Fin d → ℤ) :
    ContDiff ℝ ∞ (localizationProfile a) := by
  apply ApproxNT.contDiff_thetaMom.comp
  fun_prop

/-- Compact support is inherited through the explicit affine homeomorphism. -/
theorem localizationProfile_hasCompactSupport {d : ℕ} (a : Fin d → ℤ) :
    HasCompactSupport (localizationProfile a) := by
  let e : Mom d ≃ₜ Mom d :=
    { toFun := fun x => (2 : ℝ) • x - NTSP.intVec a
      invFun := fun y => (1 / 2 : ℝ) • (y + NTSP.intVec a)
      left_inv := by
        intro x
        change (1 / 2 : ℝ) • ((2 : ℝ) • x - NTSP.intVec a + NTSP.intVec a) = x
        rw [sub_add_cancel, smul_smul]
        norm_num
      right_inv := by
        intro y
        change (2 : ℝ) • ((1 / 2 : ℝ) • (y + NTSP.intVec a)) - NTSP.intVec a = y
        rw [smul_smul]
        norm_num
      continuous_toFun := by fun_prop
      continuous_invFun := by fun_prop }
  exact ApproxNT.hasCompactSupport_thetaMom.comp_homeomorph e

/-- Uniform finite-order derivative bounds for every localization center. -/
theorem norm_iteratedFDeriv_localizationProfile_le {d : ℕ} (a : Fin d → ℤ)
    (k : ℕ) (x : Mom d) :
    ‖iteratedFDeriv ℝ k (localizationProfile a) x‖ ≤
      (2 : ℝ) ^ k * ApproxNT.thetaDerivConst d k := by
  have hf : ContDiff ℝ k (fun y : Mom d => ApproxNT.thetaMom d (y - NTSP.intVec a)) :=
    (ApproxNT.contDiff_thetaMom.comp (contDiff_id.sub contDiff_const)).of_le (by simp)
  have he := congrFun (iteratedFDeriv_comp_const_smul (2 : ℝ) hf) x
  change iteratedFDeriv ℝ k (localizationProfile a) x = _ at he
  rw [he, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  exact mul_le_mul_of_nonneg_left (ApproxNT.norm_iteratedFDeriv_thetaMom_sub_le k _ _) (by positivity)

end WaveTurbulence.Sumint
