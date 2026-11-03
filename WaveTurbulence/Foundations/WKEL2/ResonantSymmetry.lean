/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.WKEL2.CompactKernel
public import WaveTurbulence.Foundations.WKEL2.ResonantIntegral

/-!
# Symmetry of resonant measure for all nonnegative Borel kernels

Lemma 1 of `docs/research/git20-general-d.md`. Equality on continuous compactly
supported test functions determines these locally finite Borel measures.
-/

public section

open MeasureTheory Set
open scoped ENNReal

namespace WaveTurbulence.WKEL2

variable {d : ℕ}

/-- Resonant measure is invariant under interchanging its two momenta. -/
theorem map_swap_resonantMeasure {e : Mom d} (he : ‖e‖ = 1) (hd : 2 ≤ d) :
    Measure.map Prod.swap (resonantMeasure e) = resonantMeasure e := by
  have := resonantMeasure_finiteOnCompacts e hd
  have : (Measure.map Prod.swap (resonantMeasure e)).Regular :=
    Measure.Regular.map (μ := resonantMeasure e) (Homeomorph.prodComm _ _)
  apply Measure.ext_of_integral_eq_on_compactlySupported
  intro f
  have hfi : Integrable (fun p => f p) (resonantMeasure e) :=
    f.continuous.integrable_of_hasCompactSupport f.hasCompactSupport
  have hfsc : HasCompactSupport (fun p : Mom d × Mom d => f (p.2, p.1)) :=
    f.hasCompactSupport.comp_homeomorph (Homeomorph.prodComm _ _)
  have hfs : Continuous (fun p : Mom d × Mom d => f (p.2, p.1)) :=
    f.continuous.comp continuous_swap
  have hfsi : Integrable (fun p : Mom d × Mom d => f (p.2, p.1)) (resonantMeasure e) :=
    hfs.integrable_of_hasCompactSupport hfsc
  obtain ⟨A, hA⟩ := exists_deltaKernel_of_compactSupport hd
    (fun a b => f (a, b)) f.continuous f.hasCompactSupport (d + 1) (by linarith)
  obtain ⟨B, hB⟩ := exists_deltaKernel_of_compactSupport hd
    (fun a b => f (b, a)) hfs hfsc (d + 1) (by linarith)
  calc
    ∫ p, f p ∂Measure.map Prod.swap (resonantMeasure e) =
        ∫ p : Mom d × Mom d, f (p.2, p.1) ∂resonantMeasure e :=
      integral_map (f := fun p => f p) measurable_swap.aemeasurable
        f.continuous.aestronglyMeasurable
    _ = 2 * deltaInt (fun a b => f (b, a)) :=
      integral_resonantMeasure_eq_two_deltaInt he hfsi
    _ = 2 * deltaInt (fun a b => f (a, b)) :=
      congrArg (fun z : ℝ => 2 * z) (deltaInt_swap_of_decay hB hA (by omega))
    _ = ∫ p, f p ∂resonantMeasure e :=
      (integral_resonantMeasure_eq_two_deltaInt he hfi).symm

/-- Nonnegative Borel form of research-note Lemma 1, including infinite integrals. -/
theorem lintegral_resonant_swap {e : Mom d} (he : ‖e‖ = 1) (hd : 2 ≤ d)
    {F : Mom d × Mom d → ℝ≥0∞} (hF : Measurable F) :
    (∫⁻ a : Mom d, ENNReal.ofReal (‖a‖⁻¹) * ∫⁻ b : ↥(ℝ ∙ a)ᗮ, F (a, b)) =
      ∫⁻ b : Mom d, ENNReal.ofReal (‖b‖⁻¹) * ∫⁻ a : ↥(ℝ ∙ b)ᗮ, F (a, b) := by
  have ht : (∫⁻ p : Mom d × Mom d, F (p.2, p.1) ∂resonantMeasure e) =
      ∫⁻ p, F p ∂resonantMeasure e := by
    calc
      _ = ∫⁻ p, F p ∂Measure.map Prod.swap (resonantMeasure e) :=
        (lintegral_map hF measurable_swap).symm
      _ = _ := by rw [map_swap_resonantMeasure he hd]
  exact (lintegral_resonantMeasure he hF).symm.trans
    (ht.symm.trans (lintegral_resonantMeasure he
      (F := fun p => F (p.2, p.1)) (hF.comp measurable_swap)))

/-- Lemma 1 without an auxiliary reference vector in its hypotheses. -/
theorem lintegral_inv_norm_hyperplane_swap (hd : 2 ≤ d)
    {F : Mom d × Mom d → ℝ≥0∞} (hF : Measurable F) :
    (∫⁻ a : Mom d, ENNReal.ofReal (‖a‖⁻¹) * ∫⁻ b : ↥(ℝ ∙ a)ᗮ, F (a, b)) =
      ∫⁻ b : Mom d, ENNReal.ofReal (‖b‖⁻¹) * ∫⁻ a : ↥(ℝ ∙ b)ᗮ, F (a, b) := by
  have : Nontrivial (Mom d) := Module.nontrivial_of_finrank_pos (R := ℝ)
    (by simpa only [finrank_euclideanSpace_fin] using (show 0 < d by omega))
  obtain ⟨e, he⟩ := exists_norm_eq (Mom d) (show (0 : ℝ) ≤ 1 by norm_num)
  exact lintegral_resonant_swap he hd hF

end WaveTurbulence.WKEL2
