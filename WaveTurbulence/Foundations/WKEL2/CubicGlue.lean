/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.WKEL2.CubicUniqueness

/-!
# Gluing closed-interval solutions of a cubic equation
-/

public section

noncomputable section

open Set Filter
open scoped Topology

namespace WaveTurbulence.WKEL2

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

local instance glueNormedOp : NormedAddCommGroup (E →L[ℝ] E) := inferInstance
local instance glueSpaceOp : NormedSpace ℝ (E →L[ℝ] E) := inferInstance
local instance glueNormedOp₂ : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E) := inferInstance
local instance glueSpaceOp₂ : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E) := inferInstance

/-- Join two time curves at their common endpoint. -/
@[expose] def glueCurve (b : ℝ) (f g : ℝ → E) (t : ℝ) : E := if t ≤ b then f t else g t

/-- Closed-interval cubic solutions glue when their endpoint values agree. -/
theorem hasDerivWithinAt_glueCurve (T : E →L[ℝ] E →L[ℝ] E →L[ℝ] E)
    {a b c : ℝ} (hab : a ≤ b) (hbc : b ≤ c) {f g : ℝ → E}
    (hf : ∀ t ∈ Icc a b, HasDerivWithinAt f (cubicField T (f t)) (Icc a b) t)
    (hg : ∀ t ∈ Icc b c, HasDerivWithinAt g (cubicField T (g t)) (Icc b c) t)
    (hfg : f b = g b) (t : ℝ) (ht : t ∈ Icc a c) :
    HasDerivWithinAt (glueCurve b f g) (cubicField T (glueCurve b f g t)) (Icc a c) t := by
  have hleft (r : ℝ) (hr : r ∈ Icc a b) : glueCurve b f g r = f r := ite_eq_left hr.2
  have hright (r : ℝ) (hr : r ∈ Icc b c) : glueCurve b f g r = g r := by
    by_cases h : r ≤ b
    · have he : r = b := le_antisymm h hr.1
      subst r
      simpa only [glueCurve, ite_eq_left le_rfl] using hfg
    · exact ite_eq_right h
  rcases lt_trichotomy t b with htb | heq | hbt
  · have hmem : Icc a b ∈ 𝓝[Icc a c] t := by
      filter_upwards [self_mem_nhdsWithin,
        (eventually_lt_nhds htb).filter_mono nhdsWithin_le_nhds] with r hr hb
      exact ⟨hr.1, hb.le⟩
    have H := (hf t ⟨ht.1, htb.le⟩).mono_of_mem_nhdsWithin hmem
    rw [hleft t ⟨ht.1, htb.le⟩]
    apply H.congr_of_eventuallyEq_of_mem _ ht
    filter_upwards [hmem] with r hr
    exact hleft r hr
  · subst t
    have Hl := (hf b ⟨hab, le_rfl⟩).congr_of_mem hleft ⟨hab, le_rfl⟩
    have Hr := (hg b ⟨le_rfl, hbc⟩).congr_of_mem hright ⟨le_rfl, hbc⟩
    rw [← hfg] at Hr
    have H := Hl.union Hr
    rw [Icc_union_Icc_eq_Icc hab hbc] at H
    simpa only [glueCurve, ite_eq_left le_rfl] using H
  · have hmem : Icc b c ∈ 𝓝[Icc a c] t := by
      filter_upwards [self_mem_nhdsWithin,
        (eventually_gt_nhds hbt).filter_mono nhdsWithin_le_nhds] with r hr hb
      exact ⟨hb.le, hr.2⟩
    have H := (hg t ⟨hbt.le, ht.2⟩).mono_of_mem_nhdsWithin hmem
    rw [hright t ⟨hbt.le, ht.2⟩]
    apply H.congr_of_eventuallyEq_of_mem _ ht
    filter_upwards [hmem] with r hr
    exact hright r hr

end WaveTurbulence.WKEL2
