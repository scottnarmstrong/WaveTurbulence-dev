/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.WaveB.Bridges
/-! Continuity of the exact snapshot Taylor term, via the proved polynomial bridge. -/
public section
set_option autoImplicit false
namespace WaveTurbulence.LGSpine

theorem continuous_wkeTaylorTerm {d : ℕ} (hd : 2 ≤ d)
    (φ : ℝ → SchwartzMap (Mom d) ℝ) (δ : ℝ) (p n : ℕ) (k : Mom d) :
    Continuous (fun t : ℝ => wkeTaylorTerm (φ (δ * p)) δ p n t k) := by
  simp_rw [WaveBBridges.wkeTaylorTerm_eq_taylorU hd φ δ p n]
  unfold WKE.taylorU
  change Continuous (fun t : ℝ => (δ * (t - p)) ^ n * (WKE.taylorCoeff hd (φ (p * δ)) n) k)
  fun_prop

end WaveTurbulence.LGSpine
