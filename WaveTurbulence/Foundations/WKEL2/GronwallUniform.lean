/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Analysis.ODE.Gronwall

/-!
# Uniform closed-interval Gronwall bounds for Banach-valued coordinates
-/

public section

open Set

namespace WaveTurbulence.WKEL2

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A differential inequality controls the whole closed interval by its terminal Gronwall bound. -/
theorem norm_le_gronwallBound_uniform {u v : ℝ → E} {b B K L : ℝ}
    (hB : 0 ≤ B) (hK : 0 ≤ K) (hL : 0 ≤ L)
    (hu : ∀ t ∈ Icc 0 b, HasDerivWithinAt u (v t) (Icc 0 b) t)
    (h₀ : ‖u 0‖ ≤ B) (hv : ∀ t ∈ Icc 0 b, ‖v t‖ ≤ K * ‖u t‖ + L) :
    ∀ t ∈ Icc 0 b, ‖u t‖ ≤ gronwallBound B K L b := by
  have H := norm_le_gronwallBound_of_norm_deriv_right_le
    (fun t ht => (hu t ht).continuousWithinAt)
    (fun t ht => (hu t (Ico_subset_Icc_self ht)).mono_of_mem_nhdsWithin
      (Icc_mem_nhdsGE_of_mem ht)) h₀
    (fun t ht => hv t (Ico_subset_Icc_self ht))
  intro t ht
  have HH : ‖u t‖ ≤ gronwallBound B K L t := by simpa only [sub_zero] using H t ht
  exact HH.trans (gronwallBound_mono hB hL hK ht.2)

/-- A common upper time controls Gronwall constants on every shorter interval. -/
theorem norm_le_gronwallBound_uniform_horizon {u v : ℝ → E} {b H B K L : ℝ} (hbH : b ≤ H)
    (hB : 0 ≤ B) (hK : 0 ≤ K) (hL : 0 ≤ L)
    (hu : ∀ t ∈ Icc 0 b, HasDerivWithinAt u (v t) (Icc 0 b) t)
    (h₀ : ‖u 0‖ ≤ B) (hv : ∀ t ∈ Icc 0 b, ‖v t‖ ≤ K * ‖u t‖ + L) :
    ∀ t ∈ Icc 0 b, ‖u t‖ ≤ gronwallBound B K L H := by
  have H := norm_le_gronwallBound_of_norm_deriv_right_le
    (fun t ht => (hu t ht).continuousWithinAt)
    (fun t ht => (hu t (Ico_subset_Icc_self ht)).mono_of_mem_nhdsWithin
      (Icc_mem_nhdsGE_of_mem ht)) h₀
    (fun t ht => hv t (Ico_subset_Icc_self ht))
  intro t ht
  have HH : ‖u t‖ ≤ gronwallBound B K L t := by simpa only [sub_zero] using H t ht
  exact HH.trans (gronwallBound_mono hB hL hK (ht.2.trans hbH))

/-- The uniform Gronwall constant is nonnegative for nonnegative data and time. -/
theorem gronwallBound_nonneg_of_nonneg {b B K L : ℝ}
    (hb : 0 ≤ b) (hB : 0 ≤ B) (hK : 0 ≤ K) (hL : 0 ≤ L) :
    0 ≤ gronwallBound B K L b := by
  have H := gronwallBound_mono hB hL hK hb
  rw [gronwallBound_x0] at H
  exact hB.trans H

end WaveTurbulence.WKEL2
