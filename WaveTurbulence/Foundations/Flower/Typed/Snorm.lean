/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Flower.Typed.Endpoint
public import WaveTurbulence.Foundations.IncohInst.Regref.Inputs
public import WaveTurbulence.Foundations.FC23.ExtractionNumerics
/-! # FL-TYPED: the `S^{40d,40d}` bound of the family pair profile. -/
@[expose] public section
set_option autoImplicit false
noncomputable section
namespace WaveTurbulence.Flower.Typed
open WaveTurbulence.NormBridgeScratch WaveTurbulence.Induct Finset

variable {d : ℕ}

theorem wordD_weighted_of_SNormR {A B : ℕ} (hA : A ≠ 0) {f : Mom d → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (h : SNormR A B f ≤ ENNReal.ofReal C) (l : List (Fin d)) (hl : l.length ≤ A) (x : Mom d) :
    jbr x ^ B * ‖wordD l (fun y => ((f y : ℝ) : ℂ)) x‖ ≤ C := by
  have hc : ContDiff ℝ (A : WithTop ℕ∞) f :=
    WaveTurbulence.Regref.contDiff_of_SNormR_ne_top hA (ne_top_of_le_ne_top ENNReal.ofReal_ne_top h)
  have hcc : ContDiff ℝ (A : WithTop ℕ∞) (fun y => ((f y : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp hc
  have e : wordD l (fun y => ((f y : ℝ) : ℂ)) =
      Fourier.momentumDerivative (fun i : Fin l.length => l.get i) (fun y => ((f y : ℝ) : ℂ)) := by
    rw [momentumDerivative_eq_wordD _ (hcc.of_le (by exact_mod_cast hl)), List.ofFn_get]
  rw [e]
  exact SNorm_momentum_pointwise (fun y => ((f y : ℝ) : ℂ)) hcc C hC h hl _ x

end WaveTurbulence.Flower.Typed
