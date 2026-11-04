/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Fourier.CutoffMultiplication

/-! # A fixed smooth compact extension cutoff for the source time square -/

@[expose] public section
noncomputable section
namespace WaveTurbulence.RegAsymp
open MeasureTheory WaveTurbulence.Fourier
open scoped ContDiff

/-- The fixed tensor cutoff translated to the center of the source square. -/
def unitSquareCutoff (t : Fin 2 → ℝ) : ℂ :=
  chi0TensorComplex (t-(fun _ => (1/2:ℝ)))

theorem unitSquareCutoff_eq_one {t : Fin 2 → ℝ} (ht : ∀ i, t i ∈ Set.Icc (0:ℝ) 1) :
    unitSquareCutoff t = 1 := by
  unfold unitSquareCutoff chi0TensorComplex
  rw [chi0Tensor_eq_one]
  · rfl
  · intro i
    change |t i-1/2| ≤ 1/2
    exact abs_le.mpr ⟨by linarith [(ht i).1],by linarith [(ht i).2]⟩

@[fun_prop] theorem contDiff_unitSquareCutoff : ContDiff ℝ ∞ unitSquareCutoff := by
  unfold unitSquareCutoff
  exact chi0TensorComplex_contDiff.comp (by fun_prop)

theorem hasCompactSupport_unitSquareCutoff : HasCompactSupport unitSquareCutoff := by
  have hh := (chi0TensorComplex_hasCompactSupport 2).comp_homeomorph
    (Homeomorph.addRight (-(fun _ : Fin 2 => (1/2:ℝ))))
  change HasCompactSupport (fun t : Fin 2 → ℝ => chi0TensorComplex (t-(fun _ => (1/2:ℝ))))
  simpa only [Function.comp_def, Homeomorph.coe_addRight, sub_eq_add_neg] using hh

theorem integrable_unitSquareCutoff : Integrable unitSquareCutoff :=
  contDiff_unitSquareCutoff.continuous.integrable_of_hasCompactSupport hasCompactSupport_unitSquareCutoff

/-- The extension cutoff has every fixed time Fourier norm required by the packet. -/
theorem timeFourierNorm_unitSquareCutoff_lt_top (η : ℝ) : timeFourierNorm η unitSquareCutoff < ⊤ :=
  timeFourierNorm_lt_top_of_smooth_compact η hasCompactSupport_unitSquareCutoff contDiff_unitSquareCutoff

end WaveTurbulence.RegAsymp
