/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.VdCB.StationaryFrequencies
public import WaveTurbulence.Foundations.VdCB.OpenFrequencies
public import WaveTurbulence.Foundations.VdCB.IntegerRangeSum

/-!
# Actual selected frequencies as one consecutive integer block

Integer normalization is removed from the selected set itself. The open
interval representation keeps strict endpoint conventions exact.
-/

public section

namespace WaveTurbulence.VdCB

/-- Removing the integer normalization gives the actual open derivative window. -/
theorem image_stationaryFrequencies_add_eq (g : ℝ → ℝ) (a b r : ℝ) (m : ℤ) (N : ℕ)
    (hlo : 0 ≤ deriv g (a + r)) (hhi : deriv g (b - r) ≤ N) :
    (stationaryFrequencies g a b r N).image (fun ν => m + ν) =
      openFrequencies ((m : ℝ) + deriv g (a + r)) ((m : ℝ) + deriv g (b - r)) := by
  ext k
  constructor
  · intro hk
    obtain ⟨ν, hν, rfl⟩ := Finset.mem_image.mp hk
    have h := (Finset.mem_filter.mp hν).2
    apply mem_openFrequencies.mpr
    push_cast
    constructor <;> linarith only [h.1, h.2]
  · intro hk
    obtain ⟨h1, h2⟩ := mem_openFrequencies.mp hk
    apply Finset.mem_image.mpr
    refine ⟨k - m, ?_, ?_⟩
    · apply Finset.mem_filter.mpr
      have hlow : 0 ≤ (k - m : ℤ) := by
        have hh : (0 : ℝ) ≤ (k : ℝ) - m := by linarith only [h1, hlo]
        exact_mod_cast hh
      have hhigh : k - m ≤ (N : ℤ) := by
        have hh : (k : ℝ) - m ≤ N := by linarith only [h2, hhi]
        exact_mod_cast hh
      refine ⟨Finset.mem_Icc.mpr ⟨hlow, hhigh⟩, ?_⟩
      push_cast
      constructor <;> linarith only [h1, h2]
    · omega

/-- The actual open integer interval is one consecutive half-open block,
with the natural length truncated at zero when it is empty. -/
theorem openFrequencies_eq_Ioc (A B : ℝ) :
    openFrequencies A B = Finset.Ioc ⌊A⌋ (⌊A⌋ + ((⌈B⌉ - 1 - ⌊A⌋).toNat : ℤ)) := by
  ext k
  simp only [openFrequencies, Finset.mem_Ioo, Finset.mem_Ioc]
  omega

/-- Parametrization of the actual open frequency sum by natural indices. -/
theorem sum_openFrequencies_eq_range {E : Type*} [AddCommMonoid E]
    (F : ℤ → E) (A B : ℝ) :
    (∑ k ∈ openFrequencies A B, F k) =
      ∑ j ∈ Finset.range (⌈B⌉ - 1 - ⌊A⌋).toNat, F (⌊A⌋ + j + 1) := by
  rw [openFrequencies_eq_Ioc, sum_Ioc_int_eq_range]

end WaveTurbulence.VdCB
