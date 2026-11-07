/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.AppBStarCoordinates
public import WaveTurbulence.Foundations.FinalCount.AppBPhysicalPhaseIdentities
import Mathlib.Tactic

/-! # The three exact coupled phase selectors for two overlapping triples -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole

/-- The second energy factor is exactly one of the three coupled selectors.
Both old momenta enter only through their difference. -/
theorem appb_star_second_factor {d : ℕ} (ζ : Fin 3) (q : Fin 5 → Mom d) (K1 K2 : Mom d)
    (h1 : q 0-q 1+q 2 = K1)
    (h2 : (appbStarSecond ζ q).1-(appbStarSecond ζ q).2.1+(appbStarSecond ζ q).2.2 = K2) :
    let t := appbStarDifferences ζ q
    inner ℝ ((appbStarSecond ζ q).1-(appbStarSecond ζ q).2.1)
      ((appbStarSecond ζ q).2.2-(appbStarSecond ζ q).2.1) =
      inner ℝ (![t.1-(K1-K2),t.1+t.2.1-(K1-K2),t.1+t.2.1-(K1-K2)-t.2.2] ζ) t.2.2 := by
  fin_cases ζ
  · change inner ℝ (q 2-q 3) (q 4-q 3) = inner ℝ ((q 0-q 1)-(K1-K2)) (q 2-q 3)
    change q 2-q 3+q 4 = K2 at h2
    rw [← h1,← h2]
    have he : (q 0-q 1)-(q 0-q 1+q 2-(q 2-q 3+q 4)) = q 4-q 3 := by abel
    rw [he,real_inner_comm]
  · change inner ℝ (q 1-q 3) (q 4-q 3) = inner ℝ ((q 0-q 1)+(q 2-q 1)-(K1-K2)) (q 1-q 3)
    change q 1-q 3+q 4 = K2 at h2
    rw [← h1,← h2]
    have he : (q 0-q 1)+(q 2-q 1)-(q 0-q 1+q 2-(q 1-q 3+q 4)) = q 4-q 3 := by abel
    rw [he,real_inner_comm]
  · change inner ℝ (q 3-q 1) (q 4-q 1) =
      inner ℝ ((q 0-q 1)+(q 2-q 1)-(K1-K2)-(q 3-q 1)) (q 3-q 1)
    change q 3-q 1+q 4 = K2 at h2
    rw [← h1,← h2]
    have he : (q 0-q 1)+(q 2-q 1)-(q 0-q 1+q 2-(q 3-q 1+q 4))-(q 3-q 1) = q 4-q 1 := by abel
    rw [he,real_inner_comm]

end WaveTurbulence.Mole
