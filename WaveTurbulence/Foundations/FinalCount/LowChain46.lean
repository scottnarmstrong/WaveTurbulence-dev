/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.LowChain45
/-! **FINALCOUNT LOW-CHAIN, session 6 (20): the smallness form `low_loop_class_bound_all`** (the target of the brief):
`∀ d ≥ 3, γ ∈ (1/2, 1), ∃ η₀ > 0, ∀ η ∈ (0, η₀], LowLoopClassBound d γ η`. -/
@[expose] public section
open WaveTurbulence.VineParamContract
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Set (Ioo Ioc)
namespace WaveTurbulence.FinalCountAsm

theorem low_loop_class_bound_all :
    ∀ d : ℕ, 3 ≤ d → ∀ γ : ℝ, γ ∈ Ioo (1 / 2 : ℝ) 1 → ∃ η₀ : ℝ, 0 < η₀ ∧ ∀ η ∈ Ioc (0 : ℝ) η₀, LowLoopClassBound d γ η := by
  intro d hd γ hγ
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  have h1 : 0 < min γ (1 - γ) := lt_min (by linarith [hγ.1]) (by linarith [hγ.2])
  have h2 : 0 < 2 * γ - 1 := by linarith [hγ.1]
  refine ⟨min (min γ (1 - γ) / (1000 * d)) (min ((2 * γ - 1) / (1000 * d)) (1 / (4 * 1440061))), by positivity, fun η hη => ?_⟩
  obtain ⟨hη0, hηle⟩ := hη
  have ha : η ≤ min γ (1 - γ) / (1000 * d) := le_trans hηle (min_le_left _ _)
  have hb : η ≤ (2 * γ - 1) / (1000 * d) := le_trans hηle (le_trans (min_le_right _ _) (min_le_left _ _))
  have hc : η ≤ 1 / (4 * 1440061) := le_trans hηle (le_trans (min_le_right _ _) (min_le_right _ _))
  refine low_loop_class_bound hd hγ hη0 ?_ ?_ ?_
  · rw [le_div_iff₀ (by positivity)] at ha
    nlinarith
  · rw [le_div_iff₀ (by positivity)] at hb
    nlinarith
  · rw [le_div_iff₀ (by positivity)] at hc
    nlinarith

end WaveTurbulence.FinalCountAsm
