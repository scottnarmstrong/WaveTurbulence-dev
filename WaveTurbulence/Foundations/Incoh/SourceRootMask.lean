/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Incoh.RootInputCoordinates
public import WaveTurbulence.Foundations.Incoh.SourceRootFrequency
public import WaveTurbulence.Foundations.Incoh.SpatialCenterDecay
public import WaveTurbulence.Foundations.NTSP.Basic

/-! # Smooth root masks fixed by the source leaf localization centers

The mask equals one on the actual localized source. Its scale and spatial
weight cost are exponential in the number of leaves and dimensional only.
-/

public section
noncomputable section
open MeasureTheory Set
open scoped ContDiff

namespace WaveTurbulence.Incoh

/-- Positive radius fixed solely by the source leaf-center array. -/
@[expose] def sourceRootMaskWidth {d m : ℕ} (c : Fin m → Fin d → ℤ) : ℝ :=
  2 * (2 + Real.sqrt d) ^ m * ∏ a, Fourier.momentumBracket (NTSP.intVec (c a))

/-- The root mask uses the already landed smooth tensor cutoff. -/
@[expose] def sourceRootMask {d m : ℕ} (c : Fin m → Fin d → ℤ) : Mom d → ℂ :=
  NTSP.chiScaled (sourceRootMaskWidth c)

/-- Every actual root mask has width at least two. -/
theorem two_le_sourceRootMaskWidth {d m : ℕ} (c : Fin m → Fin d → ℤ) : 2 ≤ sourceRootMaskWidth c := by
  have hp : 1 ≤ ∏ a : Fin m, Fourier.momentumBracket (NTSP.intVec (c a)) :=
    Finset.one_le_prod₀ (fun a _ => one_le_momentumBracket _)
  have hb : 1 ≤ (2 + Real.sqrt (d : ℝ)) ^ m := one_le_pow₀ (by nlinarith [Real.sqrt_nonneg (d : ℝ)])
  unfold sourceRootMaskWidth
  nlinarith only [hp, hb, mul_le_mul hp hb (by positivity) (by positivity)]

/-- The literal source root relation and input-cell support bound the actual root momentum. -/
theorem RootInputCoordinates.norm_root_le_maskWidth_half {d n m w : ℕ} {P : MomentumTreeData n m w}
    (C : RootInputCoordinates P) (c : Fin m → Fin d → ℤ) (k : Mom d)
    (x : Fin n → Fin 2 → Mom d) (hx : P.inputCellWeight c k x ≠ 0) :
    ‖k‖ ≤ sourceRootMaskWidth c / 2 := by
  have hclose (a : Fin m) : ‖P.inputMomentum k x a - NTSP.intVec (c a)‖ ≤ Real.sqrt d :=
    tsupport_leafCellProfile_subset d (NTSP.intVec (c a))
      (subset_closure ((Finset.prod_ne_zero_iff.mp hx) a (Finset.mem_univ a)))
  have hn (a : Fin m) : ‖P.inputMomentum k x a‖ ≤ ‖NTSP.intVec (c a)‖ + Real.sqrt d := by
    have h := norm_add_le (P.inputMomentum k x a - NTSP.intVec (c a)) (NTSP.intVec (c a))
    rw [sub_add_cancel] at h
    exact h.trans (by linarith only [hclose a])
  have hb (a : Fin m) : 1 + ‖P.inputMomentum k x a‖ ≤
      (2 + Real.sqrt d) * Fourier.momentumBracket (NTSP.intVec (c a)) := by
    have h1 := one_le_momentumBracket (NTSP.intVec (c a))
    have h2 : ‖NTSP.intVec (c a)‖ ≤ Fourier.momentumBracket (NTSP.intVec (c a)) := by
      unfold Fourier.momentumBracket
      exact (Real.le_sqrt (norm_nonneg _) (by positivity)).mpr (by linarith)
    nlinarith only [hn a, h1, h2, mul_nonneg (Real.sqrt_nonneg (d : ℝ)) (sub_nonneg.mpr h1)]
  calc
    _ ≤ ∑ a, ‖C.sigma a • P.inputMomentum k x a‖ :=
      (congrArg norm (C.root_eq_sum_inputs k x)).le.trans (norm_sum_le _ _)
    _ ≤ ∑ a, ‖P.inputMomentum k x a‖ := Finset.sum_le_sum (fun a _ => by
      rw [← Int.cast_smul_eq_zsmul ℝ, norm_smul, Real.norm_eq_abs]
      exact mul_le_of_le_one_left (norm_nonneg _) (C.abs_cast_sigma_le a))
    _ ≤ ∏ a, (1 + ‖P.inputMomentum k x a‖) := by
      have h := one_add_sum_le_prod_one_add Finset.univ
        (fun a => ‖P.inputMomentum k x a‖) (fun a _ => norm_nonneg _)
      linarith only [h]
    _ ≤ ∏ a, (2 + Real.sqrt d) * Fourier.momentumBracket (NTSP.intVec (c a)) :=
      Finset.prod_le_prod₀ (fun a _ => by positivity) (fun a _ => hb a)
    _ = _ := by simp only [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin, sourceRootMaskWidth]; ring

/-- The fixed mask equals one on every actual source input-cell region. -/
theorem RootInputCoordinates.sourceRootMask_eq_one {d n m w : ℕ} {P : MomentumTreeData n m w}
    (C : RootInputCoordinates P) (c : Fin m → Fin d → ℤ) (k : Mom d)
    (x : Fin n → Fin 2 → Mom d) (hx : P.inputCellWeight c k x ≠ 0) : sourceRootMask c k = 1 := by
  have hw : 0 < sourceRootMaskWidth c := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2) (two_le_sourceRootMaskWidth c)
  rw [sourceRootMask, NTSP.chiScaled_apply, Fourier.chi0Tensor_eq_one, Complex.ofReal_one]
  intro i
  change |(sourceRootMaskWidth c)⁻¹ * k i| ≤ 1 / 2
  rw [abs_mul, abs_inv, abs_of_pos hw, ← div_eq_inv_mul, div_le_iff₀ hw]
  have hi : |k i| ≤ ‖k‖ := by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le k i
  linarith only [hi, C.norm_root_le_maskWidth_half c k x hx]

/-- No source smoothness is lost by the fixed root mask. -/
theorem contDiff_sourceRootMask {d m : ℕ} (c : Fin m → Fin d → ℤ) :
    ContDiff ℝ ∞ (sourceRootMask c) := NTSP.contDiff_chiScaled _

end WaveTurbulence.Incoh
