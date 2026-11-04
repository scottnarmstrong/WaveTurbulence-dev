/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.WKEL2.WeightedGainPairing

/-!
# The nonnegative extended gain output

The resonant measure omits the delta factor one half. Extended values are
retained until squared integrability has been established.
-/

public section

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace WaveTurbulence.WKEL2

variable {d : ℕ}

/-- Absolute gain kernel integrated against the resonant measure. -/
@[expose] def absoluteGain (e : Mom d) (f₁ f₂ f₃ : Mom d → ℝ) (k : Mom d) : ℝ≥0∞ :=
  ∫⁻ p, ENNReal.ofReal |f₁ (k + p.1)| * ENNReal.ofReal |f₂ (k + p.1 + p.2)| *
    ENNReal.ofReal |f₃ (k + p.2)| ∂resonantMeasure e

/-- Joint measurability of the absolute gain kernel. -/
theorem measurable_absoluteGain_kernel {f₁ f₂ f₃ : Mom d → ℝ}
    (h₁ : Measurable f₁) (h₂ : Measurable f₂) (h₃ : Measurable f₃) :
    Measurable (fun q : Mom d × (Mom d × Mom d) =>
      ENNReal.ofReal |f₁ (q.1 + q.2.1)| * ENNReal.ofReal |f₂ (q.1 + q.2.1 + q.2.2)| *
        ENNReal.ofReal |f₃ (q.1 + q.2.2)|) :=
  ((h₁.abs.ennreal_ofReal.comp (by fun_prop)).mul (h₂.abs.ennreal_ofReal.comp (by fun_prop))).mul
    (h₃.abs.ennreal_ofReal.comp (by fun_prop))

/-- The absolute gain output is Borel measurable before its finiteness is known. -/
theorem measurable_absoluteGain (e : Mom d) (hd : 2 ≤ d) {f₁ f₂ f₃ : Mom d → ℝ}
    (h₁ : Measurable f₁) (h₂ : Measurable f₂) (h₃ : Measurable f₃) :
    Measurable (absoluteGain e f₁ f₂ f₃) := by
  let := resonantMeasure_finiteOnCompacts e hd
  exact (measurable_absoluteGain_kernel h₁ h₂ h₃).lintegral_prod_right'

/-- Measurability of the exact frozen multiplier as a nonnegative coefficient. -/
theorem measurable_frozenWeight (s : ℝ) :
    Measurable (fun k : Mom d => ENNReal.ofReal ((1 + ‖k‖ ^ 2) ^ (s / 2))) := by
  have hc : Continuous (fun k : Mom d => 1 + ‖k‖ ^ 2) := by fun_prop
  exact (hc.rpow_const (fun _ => Or.inl (by positivity))).measurable.ennreal_ofReal

/-- Tonelli identifies output testing with the full weighted gain pairing. -/
theorem lintegral_weighted_absoluteGain_test (s : ℝ) (e : Mom d) (hd : 2 ≤ d)
    {f₁ f₂ f₃ F : Mom d → ℝ} (h₁ : Measurable f₁) (h₂ : Measurable f₂)
    (h₃ : Measurable f₃) (hF : Measurable F) :
    (∫⁻ k : Mom d, (ENNReal.ofReal ((1 + ‖k‖ ^ 2) ^ (s / 2)) * absoluteGain e f₁ f₂ f₃ k) *
      ENNReal.ofReal |F k|) =
    ∫⁻ q : Mom d × (Mom d × Mom d), ENNReal.ofReal ((1 + ‖q.1‖ ^ 2) ^ (s / 2)) *
      (ENNReal.ofReal |f₁ (q.1 + q.2.1)| * ENNReal.ofReal |f₂ (q.1 + q.2.1 + q.2.2)| *
        ENNReal.ofReal |f₃ (q.1 + q.2.2)| * ENNReal.ofReal |F q.1|)
        ∂volume.prod (resonantMeasure e) := by
  let := resonantMeasure_finiteOnCompacts e hd
  have hJ : Measurable (fun q : Mom d × (Mom d × Mom d) =>
      ENNReal.ofReal ((1 + ‖q.1‖ ^ 2) ^ (s / 2)) *
        (ENNReal.ofReal |f₁ (q.1 + q.2.1)| * ENNReal.ofReal |f₂ (q.1 + q.2.1 + q.2.2)| *
          ENNReal.ofReal |f₃ (q.1 + q.2.2)| * ENNReal.ofReal |F q.1|)) :=
    ((measurable_frozenWeight s).comp measurable_fst).mul
      ((measurable_absoluteGain_kernel h₁ h₂ h₃).mul (hF.abs.ennreal_ofReal.comp measurable_fst))
  rw [lintegral_prod _ hJ.aemeasurable]
  apply lintegral_congr
  intro k
  have hK : Measurable (fun p : Mom d × Mom d =>
      ENNReal.ofReal |f₁ (k + p.1)| * ENNReal.ofReal |f₂ (k + p.1 + p.2)| *
        ENNReal.ofReal |f₃ (k + p.2)|) :=
    ((h₁.abs.ennreal_ofReal.comp (by fun_prop)).mul (h₂.abs.ennreal_ofReal.comp (by fun_prop))).mul
      (h₃.abs.ennreal_ofReal.comp (by fun_prop))
  symm
  calc
    _ = ∫⁻ p : Mom d × Mom d,
        (ENNReal.ofReal ((1 + ‖k‖ ^ 2) ^ (s / 2)) * ENNReal.ofReal |F k|) *
          (ENNReal.ofReal |f₁ (k + p.1)| * ENNReal.ofReal |f₂ (k + p.1 + p.2)| *
            ENNReal.ofReal |f₃ (k + p.2)|) ∂resonantMeasure e := by
      apply lintegral_congr
      intro p
      dsimp only
      ac_rfl
    _ = _ := by
      rw [lintegral_const_mul _ hK]
      unfold absoluteGain
      ac_rfl

end WaveTurbulence.WKEL2
