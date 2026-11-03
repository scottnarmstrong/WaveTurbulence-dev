/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.VdCB.CircleLocalization
public import WaveTurbulence.Foundations.VdCB.CircleLatticeDual
public import Mathlib.Analysis.Calculus.Deriv.Shift

/-!
# Smooth actual-column representatives for translated circles

The real center remains arbitrary. Reflection of the source localization
preserves every actual derivative on the physical column block.
-/

public section

open Set Filter
open scoped Topology ContDiff

namespace WaveTurbulence.VdCB

/-- Global smooth representative on the original translated column axis. -/
@[expose] noncomputable def circleColumnExtension (R h U : ℝ) (hU : 0 < U) (c x : ℝ) : ℝ :=
  circleSourceExtension R h U hU (R + c - x)

theorem contDiff_circleColumnExtension {R U : ℝ} (hU : 0 < U) (hUR : 3 * U ≤ R) (h c : ℝ) :
    ContDiff ℝ ∞ (circleColumnExtension R h U hU c) := by
  unfold circleColumnExtension
  exact (contDiff_circleSourceExtension hU hUR h).comp (contDiff_const.sub contDiff_id)

/-- Actual agreement on a neighborhood of every column in the block. -/
theorem circleColumnExtension_eventuallyEq {R h U c x : ℝ} (hU : 0 < U)
    (hx : R + c - x ∈ Icc U (2 * U)) :
    circleColumnExtension R h U hU c =ᶠ[𝓝 x] (fun y => circleColumnPhase R h (y - c)) := by
  have hsub : Continuous (fun y : ℝ => R + c - y) := continuous_const.sub continuous_id
  have heq := (circleSourceExtension_eventuallyEq (R := R) (h := h) hU hx).comp_tendsto (hsub.tendsto x)
  filter_upwards [heq] with y hy
  dsimp only [Function.comp_apply] at hy
  dsimp only [circleColumnExtension]
  rw [hy]
  have hh := circleColumnPhase_reflection R h (R + c - y)
  rw [show R - (R + c - y) = y - c by ring] at hh
  exact hh.symm

/-- Every actual derivative is transported, including endpoints of the block. -/
theorem iteratedDeriv_circleColumnExtension {R h U c x : ℝ} (hU : 0 < U)
    (hx : R + c - x ∈ Icc U (2 * U)) (n : ℕ) :
    iteratedDeriv n (circleColumnExtension R h U hU c) x =
      (-1 : ℝ) ^ n * iteratedDeriv n (circlePhase R h) (R + c - x) := by
  unfold circleColumnExtension
  rw [iteratedDeriv_comp_const_sub]
  dsimp only
  rw [smul_eq_mul, iteratedDeriv_circleSourceExtension hU hx]

theorem deriv_circleColumnExtension {R h U c x : ℝ} (hU : 0 < U)
    (hR : 0 < R) (hx : R + c - x ∈ Icc U (2 * U)) (hUR : 3 * U ≤ R) :
    deriv (circleColumnExtension R h U hU c) x = -circleSourceFirst R h (R + c - x) := by
  have hh := iteratedDeriv_circleColumnExtension (R := R) (h := h) (c := c) hU hx 1
  simp only [iteratedDeriv_succ, iteratedDeriv_zero, pow_one, neg_one_mul] at hh
  rw [hh]
  rw [(hasDerivAt_circlePhase_rpow (h := h) hR
    (show R + c - x ∈ Ioo 0 R from ⟨hU.trans_le hx.1, by linarith [hx.2]⟩)).deriv]

theorem deriv_deriv_circleColumnExtension {R h U c x : ℝ} (hU : 0 < U)
    (hR : 0 < R) (hx : R + c - x ∈ Icc U (2 * U)) (hUR : 3 * U ≤ R) :
    deriv (deriv (circleColumnExtension R h U hU c)) x = circleSourceSecond R h (R + c - x) := by
  have hh := iteratedDeriv_circleColumnExtension (R := R) (h := h) (c := c) hU hx 2
  simp only [iteratedDeriv_succ, iteratedDeriv_zero, neg_one_sq, one_mul] at hh
  rw [hh]
  exact deriv_deriv_circlePhase hR ⟨hU.trans_le hx.1, by linarith [hx.2]⟩

theorem abs_iteratedDeriv_three_circleColumnExtension {R h U c x : ℝ} (hU : 0 < U)
    (hx : R + c - x ∈ Icc U (2 * U)) :
    |iteratedDeriv 3 (circleColumnExtension R h U hU c) x| =
      |iteratedDeriv 3 (circlePhase R h) (R + c - x)| := by
  rw [iteratedDeriv_circleColumnExtension hU hx]
  norm_num

end WaveTurbulence.VdCB
