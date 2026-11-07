/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.AppBCosetTriples
import Mathlib.Tactic

/-! # Physical-space identities for the canonical coupled profiles -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole

theorem appb_three_energy_band_bilinear {d : ℕ} (a b c K : Mom d) (β τ : ℝ)
    (hτ : 0 ≤ τ) (hK : a-b+c = K)
    (he : |‖a‖^2-‖b‖^2+‖c‖^2-β| ≤ τ) :
    |inner ℝ (a-b) (c-b)-(‖K‖^2-β)/2| ≤ τ := by
  have hi := WeylSums.three_vector_energy_identity a b c
  rw [hK] at hi
  have ha : inner ℝ (a-b) (c-b)-(‖K‖^2-β)/2 =
      -(‖a‖^2-‖b‖^2+‖c‖^2-β)/2 := by linarith only [hi]
  rw [ha,abs_div,abs_neg,abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  linarith only [he,hτ]

theorem appb_difference_spatial_bound {d : ℕ} {x y a b : Mom d}
    (hx : ‖x-a‖ ≤ 1) (hy : ‖y-b‖ ≤ 1) : ‖(x-y)-(a-b)‖ ≤ 2 := by
  have he : (x-y)-(a-b) = (x-a)-(y-b) := by abel
  rw [he]
  exact (norm_sub_le _ _).trans (by linarith only [hx,hy])

theorem appb_coset_difference_spatial_bound {d : ℕ} (L : ℝ) (w : Mom d)
    (q r : Fin d → ℤ) (a b : Mom d)
    (hq : ‖w+latticePoint L q-a‖ ≤ 1) (hr : ‖w+latticePoint L r-b‖ ≤ 1) :
    ‖latticePoint L (q-r)-(a-b)‖ ≤ 2 := by
  have he : latticePoint L (q-r) = (w+latticePoint L q)-(w+latticePoint L r) := by
    rw [WeylSums.latticePoint_sub_eq]
    abel
  rw [he]
  exact appb_difference_spatial_bound hq hr

end WaveTurbulence.Mole
