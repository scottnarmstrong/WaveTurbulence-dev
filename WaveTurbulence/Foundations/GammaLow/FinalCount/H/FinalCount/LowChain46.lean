/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.LowChain46
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.InputsLow
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.LowChain45
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Api
/-! **L6-H port of main `WaveTurbulence.Foundations.FinalCount.LowChain46`** (sha256 in H/COPIED-SHA256SUMS): only the declarations that
depend on the vine-family carrier, re-stated over the low family `Src … Src.γL` (and L6-STEP1's
`Step1.VineCut Src.γL`); everything else is main's, by import.

 **FINALCOUNT LOW-CHAIN, session 6 (20): the smallness form `low_loop_class_bound_all`** (the target of the brief):
`∀ d ≥ 3, γ ∈ (1/2, 1), ∃ η₀ > 0, ∀ η ∈ (0, η₀], LowLoopClassBound d γ η`. 

Low-range change (L6-HLOW, GAMMA row): `γ ∈ (0, 1/2]`, the η-choice without `(2γ − 1)/(1000 d)` (no `hsm2`),
under `[Src.LowInputs]` (the ghost step, RULING R194).-/
@[expose] public section
open WaveTurbulence.VineParamContract
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Set (Ioo Ioc)
namespace WaveTurbulence.GammaLow.FinalCount.H
open WaveTurbulence.FinalCountAsm

theorem low_loop_class_bound_all [Src.LowInputs] :
    ∀ d : ℕ, 3 ≤ d → ∀ γ : ℝ, γ ∈ Ioc (0 : ℝ) (1 / 2) → ∃ η₀ : ℝ, 0 < η₀ ∧ ∀ η ∈ Ioc (0 : ℝ) η₀, LowLoopClassBound d γ η := by
  intro d hd γ hγ
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  have h1 : 0 < min γ (1 - γ) := lt_min hγ.1 (by linarith [hγ.2])
  refine ⟨min (min γ (1 - γ) / (1000 * d)) (1 / (4 * 1440061)), by positivity, fun η hη => ?_⟩
  obtain ⟨hη0, hηle⟩ := hη
  have ha : η ≤ min γ (1 - γ) / (1000 * d) := le_trans hηle (min_le_left _ _)
  have hc : η ≤ 1 / (4 * 1440061) := le_trans hηle (min_le_right _ _)
  refine low_loop_class_bound hd hγ hη0 ?_ ?_
  · rw [le_div_iff₀ (by positivity)] at ha
    nlinarith
  · rw [le_div_iff₀ (by positivity)] at hc
    nlinarith

end WaveTurbulence.GammaLow.FinalCount.H
