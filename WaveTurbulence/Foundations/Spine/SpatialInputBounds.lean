/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.SchwartzUniformNorm
public import WaveTurbulence.Foundations.Spine.CoherentZeroNorm
public import WaveTurbulence.Foundations.XChain.SNormAddBounds
/-! Actual high-order source inputs: the WKE profile costs C2, while each remainder remains small. -/
public section
set_option autoImplicit false
namespace WaveTurbulence.LGSpine
open WaveTurbulence.Induct
open scoped ENNReal

theorem Lambda_antitone (P : WTParams) (hd : 1 ≤ P.d) {r p : ℕ} (hr : r ≤ p) :
    P.Lambda p ≤ P.Lambda r := by
  unfold WTParams.Lambda
  exact Nat.pow_le_pow_right (by omega : 0 < 40 * P.d) (by omega)

theorem theta_nonneg (P : WTParams) (r : ℕ) : 0 ≤ P.theta r := by
  unfold WTParams.theta
  positivity

theorem inputsF_SNormR_bound (P : WTParams) (hd : 1 ≤ P.d) (hL : 1 ≤ P.L)
    {p A B : ℕ} (hp : p < P.D) (hA : A ≤ P.Lambda p) (hB : B ≤ P.Lambda p)
    (R : ℕ → Mom P.d → ℝ) (hR : RemainderBound P R p) (C : ℝ) (hC : 0 ≤ C)
    (hφ : ∀ r ≤ p, SNormR A B (P.φ (P.δ * r)) ≤ ENNReal.ofReal C) :
    ∀ r ≤ p, SNormR A B (inputsF P R r) ≤ ENNReal.ofReal (C + 1) := by
  intro r hr
  have hAr := hA.trans (Lambda_antitone P hd hr)
  have hBr := hB.trans (Lambda_antitone P hd hr)
  have hΛ := forty_dim_le_Lambda P hd (hr.trans hp.le)
  have hRnorm := hR r hr
  have hRcont := contDiff_of_SNorm_bound (by omega : P.Lambda r ≠ 0) _ _ hRnorm
  have hpos : 0 ≤ P.L ^ (-P.theta r) := Real.rpow_nonneg (zero_le_one.trans hL) _
  have hRlow := SNorm_mono_bound hAr hBr _ hRcont _ hpos hRnorm
  have hRone : SNormR A B (R r) ≤ ENNReal.ofReal 1 := hRlow.trans (ENNReal.ofReal_le_ofReal
    (Real.rpow_le_one_of_one_le_of_nonpos hL (neg_nonpos.mpr (theta_nonneg P r))))
  have hcφ : ContDiff ℝ A (fun k => (P.φ (P.δ * r) k : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp ((P.φ (P.δ * r)).smooth A)
  have hcR : ContDiff ℝ A (fun k => (R r k : ℂ)) := hRcont.of_le (by exact_mod_cast hAr)
  have hh := SNorm_add_bound _ _ hcφ hcR C 1 hC zero_le_one (hφ r hr) hRone
  have he : ((fun k => (P.φ (P.δ * r) k : ℂ)) + fun k => (R r k : ℂ)) =
      fun k => (inputsF P R r k : ℂ) := by
    funext k
    simp only [Pi.add_apply, inputsF, Complex.ofReal_add]
  rw [he] at hh
  exact hh

end WaveTurbulence.LGSpine
