/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.RegAsymp.MomentumSingularScale

/-! # Reality of actual source singular operators -/

public section
noncomputable section
namespace WaveTurbulence.RegAsymp
open ApproxNT Filter Topology

/-- Delta integration preserves a real-valued complex kernel, without
an integrability assumption on the defining Bochner integral. -/
theorem deltaInner_im_eq_zero {d : ℕ} (F : Mom d → Mom d → ℂ)
    (hF : ∀ x y, (F x y).im = 0) : (NTSP.deltaInner F).im = 0 := by
  have he : F = fun x y => ((F x y).re:ℂ) := by
    funext x y
    exact Complex.ext rfl (hF x y)
  rw [he,NTSP.deltaInner_ofReal]
  rfl

/-- Every finite source PV cutoff preserves a real-valued complex kernel. -/
theorem pvTrunc_im_eq_zero {d : ℕ} (s : ℝ) (F : Mom d → Mom d → ℂ)
    (hF : ∀ x y, (F x y).im = 0) : (pvTrunc s F).im = 0 := by
  have he : F = fun x y => ((F x y).re:ℂ) := by
    funext x y
    exact Complex.ext rfl (hF x y)
  have ht := pvTrunc_neg_right_ofReal s (fun x y => (F x (-y)).re)
  simp only [neg_neg] at ht
  rw [he,ht]
  simp

/-- A genuine convergent source PV preserves reality. Convergence is
explicit because an arbitrary nonconvergent limUnder has no such law. -/
theorem pvOp_im_eq_zero_of_tendsto {d : ℕ} (F : Mom d → Mom d → ℂ)
    (hF : ∀ x y, (F x y).im = 0) {v : ℂ}
    (hv : Tendsto (fun s : ℝ => pvTrunc s F) atTop (𝓝 v)) : (pvOp F).im = 0 := by
  have ht := Complex.continuous_im.continuousAt.tendsto.comp hv
  have hz : Tendsto (fun s : ℝ => (pvTrunc s F).im) atTop (𝓝 (0:ℝ)) := by
    simpa only [pvTrunc_im_eq_zero _ F hF] using
      (tendsto_const_nhds : Tendsto (fun _ : ℝ => (0:ℝ)) atTop (𝓝 0))
  have he : v.im = 0 := tendsto_nhds_unique ht hz
  rw [show pvOp F = v from hv.limUnder_eq]
  exact he

end WaveTurbulence.RegAsymp
