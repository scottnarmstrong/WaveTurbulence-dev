/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.SolutionVarianceContinuity
/-! The source's closed intermediate-time interval follows by continuity from the open-left gate range. -/
public section
namespace WaveTurbulence.Induct
open Set

theorem variance_bound_closed_left {f φ : ℝ → ℝ} {p C : ℝ}
    (hf : ContinuousOn f (Icc p (p + 1))) (hφ : ContinuousOn φ (Icc p (p + 1)))
    (hb : ∀ t ∈ Ioc p (p + 1), |f t - φ t| ≤ C) :
    ∀ t ∈ Icc p (p + 1), |f t - φ t| ≤ C := by
  have hcl : closure (Ioc p (p + 1)) = Icc p (p + 1) := closure_Ioc (by linarith)
  intro t ht
  exact le_on_closure hb (by simpa only [hcl, Pi.sub_apply] using (hf.sub hφ).abs)
    continuousOn_const (by simpa only [hcl] using ht)

end WaveTurbulence.Induct
