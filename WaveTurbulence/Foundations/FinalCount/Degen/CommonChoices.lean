/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.Degen.RemovalCounting
public import WaveTurbulence.Foundations.Counting.LatticeBox
import Mathlib.Tactic

/-! # The actual `O(L^d)` common-label choices in degenerate atom removal -/

@[expose] public section
set_option autoImplicit false
open Finset

namespace WaveTurbulence.Degen

/-- Unit-ball localization gives the precise common-label count; this is
valid at zero gap and uses no nonzero-frequency atom-count estimate. -/
theorem card_common_choices_le {D : Type*} [Fintype D] {d : ℕ}
    {L : ℝ} (hL : 0 < L) (w center : Mom d) (e : D)
    (S : Finset (D → (Fin d → ℤ)))
    (hball : ∀ κ ∈ S, ‖Molecule.kvec L w κ e - center‖ ≤ 1) :
    ((S.image (fun κ => κ e)).card : ℝ) ≤ (2 * L + 1) ^ d := by
  classical
  apply Counting.card_le_of_coordinate_bounds _ (fun i => L * (center i - w i)) hL.le
  intro n hn i
  obtain ⟨κ, hκ, rfl⟩ := mem_image.mp hn
  have hi := (PiLp.norm_apply_le (p := (2 : ENNReal))
    (Molecule.kvec L w κ e - center) i).trans (hball κ hκ)
  change |w i + (κ e i : ℝ) / L - center i| ≤ 1 at hi
  have he : L * (w i + (κ e i : ℝ) / L - center i) = (κ e i : ℝ) - L * (center i - w i) := by
    field_simp
    ring
  rw [← he, abs_mul, abs_of_pos hL]
  simpa only [mul_one] using mul_le_mul_of_nonneg_left hi hL.le

/-- The standard dimensional form used in DH23 section 10.5(4). -/
theorem card_common_choices_le_pow {D : Type*} [Fintype D] {d : ℕ}
    {L : ℝ} (hL : 1 ≤ L) (w center : Mom d) (e : D)
    (S : Finset (D → (Fin d → ℤ)))
    (hball : ∀ κ ∈ S, ‖Molecule.kvec L w κ e - center‖ ≤ 1) :
    ((S.image (fun κ => κ e)).card : ℝ) ≤ 3 ^ d * L ^ d := by
  calc
    _ ≤ (2 * L + 1) ^ d := card_common_choices_le (zero_lt_one.trans_le hL) w center e S hball
    _ ≤ (3 * L) ^ d := pow_le_pow_left₀ (by positivity) (by linarith only [hL]) d
    _ = _ := mul_pow _ _ _

end WaveTurbulence.Degen
