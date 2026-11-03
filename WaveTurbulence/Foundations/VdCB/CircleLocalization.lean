/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.VdCB.CircleSourceCalculus
public import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct

/-!
# Smooth localization of a circle dyadic block

The source square root is smooth on its open arc. A smooth bump supported
strictly inside that arc gives a global smooth extension agreeing with
all actual derivatives on the dyadic block. This permits use of the
sharp analytic lemmas without assuming endpoint smoothness of the arc.
-/

public section

open Set Filter Metric
open scoped Topology ContDiff

namespace WaveTurbulence.VdCB

/-- A concrete cutoff equal to one near `[U,2U]`. -/
@[expose] noncomputable def circleSourceCutoff (U : ℝ) (hU : 0 < U) : ContDiffBump (3 * U / 2) where
  rIn := U
  rOut := 5 * U / 4
  rIn_pos := hU
  rIn_lt_rOut := by linarith

/-- A globally defined smooth representative of the dyadic circle block. -/
@[expose] noncomputable def circleSourceExtension (R h U : ℝ) (hU : 0 < U) (x : ℝ) : ℝ :=
  circleSourceCutoff U hU x * circlePhase R h x

theorem contDiffOn_circlePhase (R h : ℝ) (hR : 0 < R) :
    ContDiffOn ℝ ∞ (circlePhase R h) (Ioo 0 R) := by
  have hp : ContDiffOn ℝ ∞ (fun u : ℝ => 2 * R * u - u ^ 2) (Ioo 0 R) := by fun_prop
  unfold circlePhase
  exact contDiffOn_const.mul (hp.sqrt (fun u hu => (show 0 < 2 * R * u - u ^ 2 by nlinarith only [hR, hu.1, hu.2]).ne'))

/-- The localization is globally smooth; the original phase is used only
where the cutoff support stays strictly within the open arc. -/
theorem contDiff_circleSourceExtension {R U : ℝ} (hU : 0 < U) (hUR : 3 * U ≤ R) (h : ℝ) :
    ContDiff ℝ ∞ (circleSourceExtension R h U hU) := by
  have hR : 0 < R := (by positivity : 0 < 3 * U).trans_le hUR
  let ψ := circleSourceCutoff U hU
  have hsub : tsupport ψ ⊆ Ioo 0 R := by
    intro x hx
    rw [ContDiffBump.tsupport_eq] at hx
    simp only [mem_closedBall, Real.dist_eq, ψ, circleSourceCutoff] at hx
    have hh := abs_le.mp hx
    constructor <;> linarith [hh.1, hh.2]
  apply contDiff_iff_contDiffAt.mpr
  intro x
  by_cases hx : x ∈ Ioo 0 R
  · exact ψ.contDiff.contDiffAt.mul ((contDiffOn_circlePhase R h hR).contDiffAt (isOpen_Ioo.mem_nhds hx))
  · have hxψ : x ∉ tsupport ψ := fun hmem => hx (hsub hmem)
    have heq : circleSourceExtension R h U hU =ᶠ[𝓝 x] (fun _ => 0) := by
      filter_upwards [(isClosed_tsupport ψ).isOpen_compl.mem_nhds hxψ] with y hy
      dsimp only [circleSourceExtension]
      rw [image_eq_zero_of_notMem_tsupport hy, zero_mul]
    exact contDiffAt_const.congr_of_eventuallyEq heq

/-- Every point of the dyadic block has a neighborhood of exact agreement. -/
theorem circleSourceExtension_eventuallyEq {R h U x : ℝ} (hU : 0 < U)
    (hx : x ∈ Icc U (2 * U)) :
    circleSourceExtension R h U hU =ᶠ[𝓝 x] circlePhase R h := by
  have hxball : x ∈ ball (3 * U / 2) (circleSourceCutoff U hU).rIn := by
    simp only [mem_ball, Real.dist_eq, circleSourceCutoff]
    apply abs_lt.mpr
    constructor <;> linarith [hx.1, hx.2]
  filter_upwards [(circleSourceCutoff U hU).eventuallyEq_one_of_mem_ball hxball] with y hy
  dsimp only [circleSourceExtension]
  rw [hy, Pi.one_apply, one_mul]

/-- The extension preserves every actual source derivative on the block. -/
theorem iteratedDeriv_circleSourceExtension {R h U x : ℝ} (hU : 0 < U)
    (hx : x ∈ Icc U (2 * U)) (n : ℕ) :
    iteratedDeriv n (circleSourceExtension R h U hU) x = iteratedDeriv n (circlePhase R h) x :=
  (circleSourceExtension_eventuallyEq hU hx).iteratedDeriv_eq n

end WaveTurbulence.VdCB
