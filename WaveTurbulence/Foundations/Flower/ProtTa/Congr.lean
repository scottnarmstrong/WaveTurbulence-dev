/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import Mathlib
public import WaveTurbulence.Foundations.Fourier.Norm00V

/-! # PROT-TA: `mixedFourierNorm00` only sees almost-everywhere classes of the slices -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open MeasureTheory WaveTurbulence.Fourier
open scoped ENNReal

namespace WaveTurbulence.Flower.ProtTa

theorem timeFourier_congr_ae {r : ℕ} {f g : (Fin r → ℝ) → ℂ} (h : f =ᵐ[volume] g) :
    timeFourier f = timeFourier g := by
  funext ξ
  unfold timeFourier VectorFourier.fourierIntegral
  apply integral_congr_ae
  filter_upwards [h] with t ht
  simp only [ht]

end WaveTurbulence.Flower.ProtTa
