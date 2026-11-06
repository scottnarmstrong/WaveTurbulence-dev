/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.PrefixConjunction
public import WaveTurbulence.Foundations.Spine.LeafwiseAt
/-! Monotonic scalar costs used to combine independently quantified source gates. -/
public section
set_option autoImplicit false
namespace WaveTurbulence.LGSpine
open WaveTurbulence.Induct

@[simp] theorem Rdown_largeConstants (P : WTParams) (C₁ C₂ : ℝ) (k : ℕ) :
    ({P with C₁ := C₁, C₂ := C₂} : WTParams).Rdown k = P.Rdown k := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [WTParams.Rdown, ih]

@[simp] theorem N_largeConstants (P : WTParams) (C₁ C₂ : ℝ) (p : ℕ) :
    ({P with C₁ := C₁, C₂ := C₂} : WTParams).N p = P.N p := by
  simp only [WTParams.N, WTParams.R, Rdown_largeConstants]

theorem source_coefficient_mono {C C' δ : ℝ} (hC : 0 ≤ C) (hCC : C ≤ C')
    (hδ : 0 ≤ δ) (n : ℕ) : C * (C * δ) ^ n ≤ C' * (C' * δ) ^ n := by
  exact mul_le_mul hCC (pow_le_pow_left₀ (mul_nonneg hC hδ)
    (mul_le_mul_of_nonneg_right hCC hδ) n) (by positivity) (hC.trans hCC)

theorem source_factor_mono {C C' : ℝ} (hC : 0 ≤ C) (hCC : C ≤ C') (n : ℕ) :
    C * C ^ n ≤ C' * C' ^ n := by
  exact mul_le_mul hCC (pow_le_pow_left₀ hC hCC n) (by positivity) (hC.trans hCC)

theorem regBound_largeConstants_mono (P : WTParams) {C₁ C₂ : ℝ}
    (hC : 0 ≤ P.C₁) (hCC : P.C₁ ≤ C₁) (hδ : 0 ≤ P.δ) (hL : 0 ≤ P.L) (n g : ℕ) :
    regBound P n g ≤ regBound {P with C₁ := C₁, C₂ := C₂} n g := by
  unfold regBound
  apply ENNReal.ofReal_le_ofReal
  exact mul_le_mul_of_nonneg_right (source_coefficient_mono hC hCC hδ n) (Real.rpow_nonneg hL _)

end WaveTurbulence.LGSpine
