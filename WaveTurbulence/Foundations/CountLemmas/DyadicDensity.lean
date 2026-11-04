/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Counting.DyadicBlocks
public import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Tactic

/-! # Summing the actual weak-L² density distribution -/

public section
open Finset
namespace WaveTurbulence.CountLemmas

/-- Finite dyadic layer summation. A quadratic bound on the number of dense
fibers costs only a linear density threshold after weighting by their sizes. -/
theorem sum_le_of_dyadic_density_bounds {ι : Type*} (X : Finset ι) (w : ι → ℝ)
    {H K : ℝ} (hH : 0 ≤ H) (hK : 0 ≤ K) (J : ℕ)
    (hcap : ∀ x ∈ X, w x ≤ H)
    (hdense : ∀ j < J,
      (((X.filter (fun x => H/(2 : ℝ)^(j+1) < w x ∧ w x ≤ H/(2 : ℝ)^j)).card) : ℝ) ≤
        K*((2 : ℝ)^(j+1))^2) :
    (∑ x ∈ X, w x) ≤ (X.card : ℝ)*(H/(2 : ℝ)^J)+4*K*H*(2 : ℝ)^J := by
  classical
  have he := Counting.sum_eq_low_add_dyadic_blocks X w w hH hcap J
  have hlow : (∑ x ∈ X.filter (fun x => w x ≤ H/(2 : ℝ)^J), w x) ≤
      (X.card : ℝ)*(H/(2 : ℝ)^J) := by
    calc
      _ ≤ ∑ _x ∈ X.filter (fun x => w x ≤ H/(2 : ℝ)^J), H/(2 : ℝ)^J :=
        sum_le_sum (fun x hx => (mem_filter.mp hx).2)
      _ = ((X.filter (fun x => w x ≤ H/(2 : ℝ)^J)).card : ℝ)*(H/(2 : ℝ)^J) := by rw [sum_const,nsmul_eq_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (card_filter_le _ _)) (by positivity)
  have hblock (j : ℕ) (hj : j < J) :
      (∑ x ∈ X.filter (fun x => H/(2 : ℝ)^(j+1) < w x ∧ w x ≤ H/(2 : ℝ)^j), w x) ≤
        4*K*H*(2 : ℝ)^j := by
    let t := X.filter (fun x => H/(2 : ℝ)^(j+1) < w x ∧ w x ≤ H/(2 : ℝ)^j)
    calc
      _ ≤ ∑ _x ∈ t, H/(2 : ℝ)^j := sum_le_sum (fun x hx => (mem_filter.mp hx).2.2)
      _ = (t.card : ℝ)*(H/(2 : ℝ)^j) := by rw [sum_const,nsmul_eq_mul]
      _ ≤ (K*((2 : ℝ)^(j+1))^2)*(H/(2 : ℝ)^j) := mul_le_mul_of_nonneg_right (hdense j hj) (by positivity)
      _ = _ := by rw [pow_succ]; field_simp; ring
  have hgeom : (∑ j ∈ range J, (2 : ℝ)^j) ≤ (2 : ℝ)^J := by
    have hh := geom_sum_mul_neg (2 : ℝ) J
    linarith only [hh]
  calc
    _ = _ := he
    _ ≤ (X.card : ℝ)*(H/(2 : ℝ)^J)+∑ j ∈ range J, 4*K*H*(2 : ℝ)^j :=
      add_le_add hlow (sum_le_sum (fun j hj => hblock j (mem_range.mp hj)))
    _ = (X.card : ℝ)*(H/(2 : ℝ)^J)+(4*K*H)*(∑ j ∈ range J, (2 : ℝ)^j) := by rw [mul_sum]
    _ ≤ _ := add_le_add le_rfl (mul_le_mul_of_nonneg_left hgeom (by positivity))

end WaveTurbulence.CountLemmas
