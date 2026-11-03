/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.CountLemmas.LatticeSets
public import WaveTurbulence.Foundations.CountLemmas.LinearBox
public import WaveTurbulence.Foundations.CountLemmas.LargeCoordinate

/-! # Spatial-ball versions of the coordinate strip count -/

public section
open Finset
namespace WaveTurbulence.CountLemmas

/-- Coordinate conversion of a physical radius-R ball into an integer box. -/
theorem coordinate_bound_of_ball {d : ℕ} {L R : ℝ} (hL : 0 < L)
    (a : Mom d) (n : Fin d → ℤ) (hn : ‖latticePoint L n-a‖ ≤ R) (i : Fin d) :
    |(n i : ℝ)-L*a i| ≤ L*R := by
  have hh : |(n i : ℝ)/L-a i| ≤ R :=
    (show |(latticePoint L n-a) i| ≤ ‖latticePoint L n-a‖ from
      by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le (latticePoint L n-a) i).trans hn
  have heq : (n i : ℝ)-L*a i = L*((n i : ℝ)/L-a i) := by field_simp
  rw [heq,abs_mul,abs_of_pos hL]
  exact mul_le_mul_of_nonneg_left hh hL.le

/-- Strip counting inside an actual Euclidean ball, with one retained
nonzero coordinate of the coefficient. -/
theorem card_dot_strip_ball_le {d : ℕ} (s : Finset (Fin d → ℤ))
    {L R τ : ℝ} (hL : 0 < L) (hR : 0 ≤ R) (hτ : 0 ≤ τ)
    (a r : Mom d) (β : ℝ) (i : Fin d) (hi : r i ≠ 0)
    (hball : ∀ n ∈ s, ‖latticePoint L n-a‖ ≤ R)
    (hstrip : ∀ n ∈ s, |inner ℝ r (latticePoint L n)-β| ≤ τ) :
    (s.card : ℝ) ≤ (2*(L*R)+1)^(d-1)*(2*τ*L/|r i|+1) := by
  have hb := card_linear_box_le s (fun j => L*a j) (fun j => r j/L) i
    (mul_nonneg hL.le hR) hτ (div_ne_zero hi hL.ne')
    (fun n hn j => coordinate_bound_of_ball hL a n (hball n hn) j)
    (β := β) (by
      intro n hn
      have hid : (∑ j, (r j/L)*(n j : ℝ)) = inner ℝ r (latticePoint L n) := by
        simp only [PiLp.inner_apply,Real.inner_apply,latticePoint]
        apply sum_congr rfl
        intro j _
        ring
      rw [hid]
      exact hstrip n hn)
  have heq : 2*τ/|r i/L| = 2*τ*L/|r i| := by
    rw [abs_div,abs_of_pos hL]
    field_simp
  simpa only [heq] using hb

/-- A lower bound on the coefficient norm suffices after choosing its
largest coordinate; no direction is fixed by the statement. -/
theorem card_dot_strip_ball_norm_le {d : ℕ} (hd : 0 < d)
    (s : Finset (Fin d → ℤ)) {L R τ A : ℝ} (hL : 0 < L)
    (hR : 0 ≤ R) (hτ : 0 ≤ τ) (hA : 0 < A)
    (a r : Mom d) (β : ℝ) (hr : A ≤ ‖r‖)
    (hball : ∀ n ∈ s, ‖latticePoint L n-a‖ ≤ R)
    (hstrip : ∀ n ∈ s, |inner ℝ r (latticePoint L n)-β| ≤ τ) :
    (s.card : ℝ) ≤ (2*(L*R)+1)^(d-1)*(2*(d : ℝ)*τ*L/A+1) := by
  obtain ⟨i,hi⟩ := exists_large_coordinate hd r
  have hdi : (0 : ℝ) < d := by exact_mod_cast hd
  have hip : 0 < |r i| := (mul_pos_iff_of_pos_left hdi).mp (hA.trans_le (hr.trans hi))
  have hc := card_dot_strip_ball_le s hL hR hτ a r β i (abs_pos.mp hip) hball hstrip
  have hh : 2*τ*L/|r i| ≤ 2*(d : ℝ)*τ*L/A := by
    apply (div_le_div_iff₀ hip hA).mpr
    have hm := mul_le_mul_of_nonneg_left (hr.trans hi) (by positivity : 0 ≤ 2*τ*L)
    nlinarith only [hm]
  exact hc.trans (mul_le_mul_of_nonneg_left (add_le_add hh le_rfl) (by positivity))

end WaveTurbulence.CountLemmas
