/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Mathlib.MeasureTheory.Constructions.Pi

/-! # Null equality hyperplanes for distinct source branching clocks -/

public section
noncomputable section
open MeasureTheory

namespace WaveTurbulence.Incoh

/-- Distinct finite real coordinate clocks are unequal almost everywhere for Lebesgue measure.
This justifies the source's strict/closed fiber endpoint changes. -/
theorem ae_clock_ne_clock {V : Type*} [Fintype V] [DecidableEq V] (i j : V) (hij : i ≠ j) :
    ∀ᵐ t : V → ℝ, t i ≠ t j := by
  let f : (V → ℝ) →ₗ[ℝ] ℝ := (LinearMap.proj i : (V → ℝ) →ₗ[ℝ] ℝ) - (LinearMap.proj j : (V → ℝ) →ₗ[ℝ] ℝ)
  have hker : f.ker ≠ ⊤ := by
    intro he
    have hm : (Pi.single i (1 : ℝ)) ∈ f.ker := he ▸ Submodule.mem_top
    have hji : j ≠ i := Ne.symm hij
    simp [LinearMap.mem_ker, f, hji] at hm
  have hm := Measure.addHaar_submodule (volume : Measure (V → ℝ)) f.ker hker
  have hzero : (volume : Measure (V → ℝ)) {t | t i = t j} = 0 := by
    have hs : {t : V → ℝ | t i = t j} = (f.ker : Set (V → ℝ)) := by
      ext t
      change (t i = t j) ↔ f t = 0
      simp [f, sub_eq_zero]
    rw [hs]
    exact hm
  change {t : V → ℝ | t i = t j}ᶜ ∈ ae volume
  exact compl_mem_ae_iff.mpr hzero

end WaveTurbulence.Incoh
