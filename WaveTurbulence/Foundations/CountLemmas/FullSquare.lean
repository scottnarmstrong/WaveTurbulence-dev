/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.WeylSums.TimeSquareScaling
public import WaveTurbulence.Foundations.WeylSums.NormalizedWeyl

/-! # Full-square time dilation using the established square-window API -/

public section
open MeasureTheory Set
open WaveTurbulence.WeylSums
namespace WaveTurbulence.CountLemmas

theorem timeSquareWindow_zero (B : ℝ) :
    timeSquareWindow 0 B = ({t : ℝ | |t| ≤ B} ×ˢ {t : ℝ | |t| ≤ B}) := by
  ext ts
  change (0 ≤ max |ts.1| |ts.2| ∧ |ts.1| ≤ B ∧ |ts.2| ≤ B) ↔ _
  exact and_iff_right (le_trans (abs_nonneg _) (le_max_left _ _))

/-- Dilation of both actual time coordinates contributes the Jacobian `J²`. -/
theorem integral_fullSquare_div (f : ℝ × ℝ → ℝ) (B : ℝ) {J : ℝ} (hJ : 0 < J) :
    (∫ ts : ℝ × ℝ in ({t : ℝ | |t| ≤ B} ×ˢ {t : ℝ | |t| ≤ B}), f (ts.1/J,ts.2/J)) =
      J^2*(∫ ts : ℝ × ℝ in ({t : ℝ | |t| ≤ B/J} ×ˢ {t : ℝ | |t| ≤ B/J}), f ts) := by
  simpa only [zero_div,timeSquareWindow_zero] using integral_timeSquareWindow_div f 0 B hJ

theorem integrableOn_fullSquare_div (f : ℝ × ℝ → ℝ) (B : ℝ) {J : ℝ} (hJ : 0 < J)
    (hi : IntegrableOn f ({t : ℝ | |t| ≤ B/J} ×ˢ {t : ℝ | |t| ≤ B/J})) :
    IntegrableOn (fun ts : ℝ × ℝ => f (ts.1/J,ts.2/J))
      ({t : ℝ | |t| ≤ B} ×ˢ {t : ℝ | |t| ≤ B}) := by
  have hi' : IntegrableOn f (timeSquareWindow (0/J) (B/J)) := by
    simpa only [zero_div,timeSquareWindow_zero] using hi
  simpa only [timeSquareWindow_zero] using integrableOn_timeSquareWindow_div 0 B hJ hi'

/-- Reducing the dimension of a minimum costs only the actual pointwise cap. -/
theorem min_pow_le_cap_mul_cube {u v A : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v)
    (huA : u ≤ A) (hvA : v ≤ A) {d : ℕ} (hd : 3 ≤ d) :
    min (u^d) (v^d) ≤ A^(d-3)*min (u^3) (v^3) := by
  have hA : 0 ≤ A := hu.trans huA
  rw [mul_min_of_nonneg _ _ (pow_nonneg hA _)]
  have hp (x : ℝ) (hx : 0 ≤ x) (hxA : x ≤ A) : x^d ≤ A^(d-3)*x^3 := by
    calc
      _ = x^(d-3)*x^3 := by rw [← pow_add,Nat.sub_add_cancel hd]
      _ ≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hx hxA _) (pow_nonneg hx 3)
  exact min_le_min (hp u hu huA) (hp v hv hvA)

/-- Uniform cap for the full normalized Weyl function. -/
theorem normalizedWeyl_le_cap {M : ℝ} (hM : 1 ≤ M) (t : ℝ) :
    normalizedWeyl M t ≤ 25*M := by
  have hMp : 0 < M := lt_of_lt_of_le zero_lt_one hM
  rw [normalizedWeyl,div_le_iff₀ hMp]
  have hb := (sq_le_sq₀ (weylSupremum_nonneg hMp t) (by positivity : 0 ≤ 5*M)).mpr
    (weylSupremum_le_five_mul hM t)
  nlinarith only [hb]

end WaveTurbulence.CountLemmas
