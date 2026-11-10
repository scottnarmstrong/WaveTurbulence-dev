/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.SpatialInputBounds
/-! Real input regularity and uniform finite-order bounds from the literal source remainder premise. -/
public section
set_option autoImplicit false
namespace WaveTurbulence.LGSpine
open WaveTurbulence.Induct
open Set

theorem contDiff_real_of_SNormR_bound {d A B : ℕ} (hA : A ≠ 0) (f : Mom d → ℝ)
    (C : ℝ) (h : SNormR A B f ≤ ENNReal.ofReal C) : ContDiff ℝ A f := by
  have hc := contDiff_of_SNorm_bound hA (fun x => (f x : ℂ)) C h
  have hr := Complex.reCLM.contDiff.comp hc
  change ContDiff ℝ A (fun x => (f x : ℂ).re) at hr
  simpa only [Complex.ofReal_re] using hr

end WaveTurbulence.LGSpine
