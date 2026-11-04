/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Incoh.SourceRootMask

/-! # Actual support, derivative and weight bounds for the fixed source root masks -/

public section
noncomputable section
open MeasureTheory Set
open scoped ContDiff

namespace WaveTurbulence.Incoh

/-- One finite dimensional coefficient controls every mask derivative up to the stated order. -/
@[expose] def rootMaskDerivativeConstant (d J : ℕ) : ℝ :=
  1 + ∑ j ∈ Finset.range (J + 1), NTSP.chiDerivConst d j

theorem one_le_rootMaskDerivativeConstant (d J : ℕ) : 1 ≤ rootMaskDerivativeConstant d J := by
  unfold rootMaskDerivativeConstant
  exact le_add_of_nonneg_right (Finset.sum_nonneg (fun j _ => NTSP.chiDerivConst_nonneg d j))

/-- The actual mask derivatives are bounded independently of every leaf center and root scale. -/
theorem norm_iteratedFDeriv_sourceRootMask_le {d m J j : ℕ}
    (c : Fin m → Fin d → ℤ) (hj : j ≤ J) (k : Mom d) :
    ‖iteratedFDeriv ℝ j (sourceRootMask c) k‖ ≤ rootMaskDerivativeConstant d J := by
  have hχ := NTSP.norm_iteratedFDeriv_chiScaled_le
    ((by norm_num : (1 : ℝ) ≤ 2).trans (two_le_sourceRootMaskWidth c)) (0 : Mom d) j k
  have hsum : NTSP.chiDerivConst d j ≤ ∑ i ∈ Finset.range (J + 1), NTSP.chiDerivConst d i :=
    Finset.single_le_sum (fun i _ => NTSP.chiDerivConst_nonneg d i) (Finset.mem_range.mpr (by omega))
  have hχ' : ‖iteratedFDeriv ℝ j (sourceRootMask c) k‖ ≤ NTSP.chiDerivConst d j := by
    simpa only [sourceRootMask, sub_zero] using hχ
  exact hχ'.trans (by unfold rootMaskDerivativeConstant; linarith only [hsum])

/-- The actual closed support stays in the exact source-mask radius. -/
theorem tsupport_sourceRootMask_subset {d m : ℕ} (c : Fin m → Fin d → ℤ) :
    tsupport (sourceRootMask c) ⊆ {k : Mom d | ‖k‖ ≤ sourceRootMaskWidth c * Real.sqrt d} := by
  apply closure_minimal
  · intro k hk
    exact NTSP.norm_le_of_chiScaled_ne_zero
      (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2) (two_le_sourceRootMaskWidth c)) hk
  · exact isClosed_le continuous_norm continuous_const

/-- The root weight on the actual mask support costs only exponential leaf-count growth and
one copy of the source weight at each localization center. -/
theorem momentumBracket_pow_le_on_sourceRootMask {d m W : ℕ}
    (c : Fin m → Fin d → ℤ) (k : Mom d) (hk : k ∈ tsupport (sourceRootMask c)) :
    Fourier.momentumBracket k ^ W ≤
      ((1 + 2 * Real.sqrt d) * (2 + Real.sqrt d) ^ m) ^ W *
        ∏ a : Fin m, Fourier.momentumBracket (NTSP.intVec (c a)) ^ W := by
  have hnorm := tsupport_sourceRootMask_subset c hk
  change ‖k‖ ≤ sourceRootMaskWidth c * Real.sqrt d at hnorm
  have hbr : Fourier.momentumBracket k ≤ 1 + ‖k‖ := by
    unfold Fourier.momentumBracket
    apply (Real.sqrt_le_left (by positivity)).mpr
    nlinarith [norm_nonneg k]
  have hp : 1 ≤ ∏ a : Fin m, Fourier.momentumBracket (NTSP.intVec (c a)) :=
    Finset.one_le_prod₀ (fun a _ => one_le_momentumBracket _)
  have hb : 1 ≤ (2 + Real.sqrt (d : ℝ)) ^ m := one_le_pow₀ (by nlinarith [Real.sqrt_nonneg (d : ℝ)])
  have hprod : 1 ≤ (2 + Real.sqrt (d : ℝ)) ^ m *
      ∏ a : Fin m, Fourier.momentumBracket (NTSP.intVec (c a)) :=
    one_le_mul_of_one_le_of_one_le hb hp
  have hpoint : Fourier.momentumBracket k ≤ ((1 + 2 * Real.sqrt d) * (2 + Real.sqrt d) ^ m) *
      ∏ a : Fin m, Fourier.momentumBracket (NTSP.intVec (c a)) := by
    unfold sourceRootMaskWidth at hnorm
    nlinarith only [hnorm, hbr, hprod]
  simpa only [mul_pow, Finset.prod_pow] using
    pow_le_pow_left₀ (zero_le_one.trans (one_le_momentumBracket k)) hpoint W

end WaveTurbulence.Incoh
