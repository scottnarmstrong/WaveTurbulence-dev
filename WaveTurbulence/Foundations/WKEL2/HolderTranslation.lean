/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Frozen.Defs.Mom
public import Mathlib.MeasureTheory.Group.Integral
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Uniform translation bounds from Hölder

The translation-invariance step of the two Hölder estimates in research-note
Lemma 4, for arbitrary functions in conjugate Lebesgue spaces.
-/

public section

open MeasureTheory
open scoped ENNReal

namespace WaveTurbulence.WKEL2

variable {d : ℕ}

/-- Products of a translated Lᵖ function and an Lᑫ function are integrable. -/
theorem integrable_translate_mul {p q : ℝ} (hpq : p.HolderConjugate q)
    {f g : Mom d → ℝ} (hf : MemLp f (ENNReal.ofReal p))
    (hg : MemLp g (ENNReal.ofReal q)) (k : Mom d) :
    Integrable (fun x => f (k + x) * g x) := by
  have ht : MemLp (fun x => f (k + x)) (ENNReal.ofReal p) :=
    hf.comp_measurePreserving (measurePreserving_add_left volume k)
  have := hpq.ennrealOfReal
  exact ht.integrable_mul hg

/-- Hölder bound independent of the translation parameter. -/
theorem integral_translate_mul_norm_le {p q : ℝ} (hpq : p.HolderConjugate q)
    {f g : Mom d → ℝ} (hf : MemLp f (ENNReal.ofReal p))
    (hg : MemLp g (ENNReal.ofReal q)) (k : Mom d) :
    ∫ x, ‖f (k + x)‖ * ‖g x‖ ≤
      (∫ x, ‖f x‖ ^ p) ^ (1 / p) * (∫ x, ‖g x‖ ^ q) ^ (1 / q) := by
  have ht : MemLp (fun x => f (k + x)) (ENNReal.ofReal p) :=
    hf.comp_measurePreserving (measurePreserving_add_left volume k)
  have h := integral_mul_norm_le_Lp_mul_Lq hpq ht hg
  rw [integral_add_left_eq_self (fun x => ‖f x‖ ^ p) k] at h
  exact h

end WaveTurbulence.WKEL2
