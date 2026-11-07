/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Flower.Typed.Defs
public import WaveTurbulence.Foundations.FC23.FrozenRadialBridge
public import WaveTurbulence.Foundations.Fourier.Chi0
/-! # FL-TYPED: support of the family pair profile at the top layer. -/
@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace WaveTurbulence.Flower.Typed

theorem endpointFactor_top_support (p : ℕ) (tail : Bool) {M A z r : ℝ} (hM : 0 < M) (hr : M ≤ r) :
    FC23.endpointFactor p p tail M A z r = 0 := by
  have h1 : chi0 (r / (M / 2)) = 0 := by
    rw [FC23.frozen_chi0_eq]
    apply Fourier.chi0_eq_zero
    rw [abs_of_nonneg (div_nonneg (hM.le.trans hr) (by positivity))]
    rw [one_le_div (by positivity)]
    linarith
  have h2 : chi0 (r / M) = 0 := by
    rw [FC23.frozen_chi0_eq]
    apply Fourier.chi0_eq_zero
    rw [abs_of_nonneg (div_nonneg (hM.le.trans hr) hM.le)]
    exact (one_le_div hM).mpr hr
  unfold FC23.endpointFactor
  by_cases ht : tail <;> simp [ht, h1, h2]

theorem familyProfile_support {w d : ℕ} (F : ℕ → Mom d → ℝ) (p : ℕ) (M A : ℝ) (tail : Fin w → Bool)
    (z : Fin w → ℝ) (j j' : Fin w) (x : Mom d) (hM : 0 < M) (hx : M ≤ ‖x‖) :
    familyProfile F p M A tail z p j j' x = 0 := by
  unfold familyProfile
  rw [endpointFactor_top_support p _ hM hx]
  simp

end WaveTurbulence.Flower.Typed
