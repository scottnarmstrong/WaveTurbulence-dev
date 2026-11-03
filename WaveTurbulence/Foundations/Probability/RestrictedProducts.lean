/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Probability.RestrictedCauchySchwarz
public import Mathlib.Basic.Complex.Basic

/-!
# Restricted product moments

The two-factor Cauchy–Schwarz estimate for the unnormalized event expectations
of TARGET L813–L815. Together with the small-event estimate, this controls
products of random factors without dividing by an event probability.
-/

public section

namespace WaveTurbulence.Probability
open MeasureTheory

/-- Cauchy–Schwarz for two complex factors integrated against a restricted measure. -/
theorem norm_integral_mul_restrict_le {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {f g : Ω → ℂ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) (A : Set Ω) :
    ‖∫ ω in A, f ω * g ω ∂μ‖ ≤
      Real.sqrt (∫ ω in A, ‖f ω‖ ^ 2 ∂μ) * Real.sqrt (∫ ω in A, ‖g ω‖ ^ 2 ∂μ) := by
  have h := integral_mul_le_Lp_mul_Lq_of_nonneg (p := 2) (q := 2)
    (by norm_num [Real.holderConjugate_iff])
    (Filter.Eventually.of_forall fun ω => norm_nonneg (f ω))
    (Filter.Eventually.of_forall fun ω => norm_nonneg (g ω))
    (by simpa using (hf.restrict A).norm) (by simpa using (hg.restrict A).norm)
  have hpf : (fun ω => ‖f ω‖ ^ (2 : ℝ)) = (fun ω => ‖f ω‖ ^ (2 : ℕ)) := by
    funext ω
    exact Real.rpow_natCast _ 2
  have hpg : (fun ω => ‖g ω‖ ^ (2 : ℝ)) = (fun ω => ‖g ω‖ ^ (2 : ℕ)) := by
    funext ω
    exact Real.rpow_natCast _ 2
  rw [hpf, hpg, ← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow] at h
  apply (norm_integral_le_integral_norm _).trans
  simpa only [norm_mul] using h

end WaveTurbulence.Probability
