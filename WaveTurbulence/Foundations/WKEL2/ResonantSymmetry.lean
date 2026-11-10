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

end WaveTurbulence.WKEL2
