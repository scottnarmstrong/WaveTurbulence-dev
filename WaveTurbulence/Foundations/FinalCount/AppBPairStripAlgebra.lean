/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Frozen.Defs.Mom
import Mathlib.Tactic

/-! # From a conserved difference and energy to an independent linear strip -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole

theorem appb_difference_energy_identity {d : ℕ} (a b : Mom d) :
    2*inner ℝ (a-b) a-‖a-b‖^2 = ‖a‖^2-‖b‖^2 := by
  rw [inner_sub_left,norm_sub_sq_real,real_inner_self_eq_norm_sq,real_inner_comm]
  ring

/-- The two atomic energy windows produce exactly one original-width
strip after division by two. -/
theorem appb_difference_strip_bound {d : ℕ} (a b r : Mom d) (β τ : ℝ)
    (hr : r = a-b) (hE : |‖a‖^2-‖b‖^2-β| ≤ 2*τ) :
    |inner ℝ r a-(β+‖r‖^2)/2| ≤ τ := by
  have he : inner ℝ r a-(β+‖r‖^2)/2 = (‖a‖^2-‖b‖^2-β)/2 := by
    rw [hr]
    have hh := appb_difference_energy_identity a b
    linarith only [hh]
  rw [he,abs_div,abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  linarith only [hE]

end WaveTurbulence.Mole
