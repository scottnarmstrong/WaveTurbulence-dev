/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Counting.DyadicPowerBlocks
public import Mathlib.Algebra.Order.Field.GeomSum

/-! # Summing geometric shell counts without a logarithmic loss -/

public section
open Finset
namespace WaveTurbulence.CountLemmas

/-- Every positive integer power of dyadic radii has a uniformly bounded
geometric sum. The initial radius is included. -/
theorem sum_dyadic_radius_pow_le {R : ℝ} (hR : 0 ≤ R) (p J : ℕ) (hp : 1 ≤ p) :
    (∑ j ∈ range J, (R/(2 : ℝ)^j)^p) ≤ 2*R^p := by
  have hq : (1/2 : ℝ)^p ≤ 1/2 := by
    simpa only [pow_one] using pow_le_pow_of_le_one (by norm_num : (0 : ℝ) ≤ 1/2)
      (by norm_num : (1/2 : ℝ) ≤ 1) hp
  have hterm (j : ℕ) : (R/(2 : ℝ)^j)^p ≤ R^p*(1/2 : ℝ)^j := by
    have heq : (R/(2 : ℝ)^j)^p = R^p*((1/2 : ℝ)^p)^j := by
      calc
        _ = R^p/((2 : ℝ)^p)^j := by rw [div_pow,← pow_mul,← pow_mul,Nat.mul_comm j p]
        _ = _ := by simp only [div_eq_mul_inv,one_mul,inv_pow]
    rw [heq]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hq j) (pow_nonneg hR p)
  have hsum : (∑ j ∈ range J, (1/2 : ℝ)^j) ≤ 2 := by
    have he := geom_sum_mul_neg (1/2 : ℝ) J
    have hh : 0 ≤ (1/2 : ℝ)^J := by positivity
    linarith only [he,hh]
  calc
    _ ≤ ∑ j ∈ range J, R^p*(1/2 : ℝ)^j := sum_le_sum (fun j _ => hterm j)
    _ = R^p*(∑ j ∈ range J, (1/2 : ℝ)^j) := (mul_sum _ _ _).symm
    _ ≤ R^p*2 := mul_le_mul_of_nonneg_left hsum (pow_nonneg hR p)
    _ = _ := mul_comm _ _

/-- A purely finite dyadic aggregation lemma. Concrete applications prove
its shell and terminal-box bounds from the actual counting constraints. -/
theorem card_le_of_two_geometric_shell_bounds {ι : Type*} (s : Finset ι)
    (height : ι → ℝ) {R A B D : ℝ} (hR : 0 ≤ R) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (p q J : ℕ) (hp : 1 ≤ p) (hq : 1 ≤ q)
    (hheight : ∀ x ∈ s, height x ≤ R)
    (hlow : (((s.filter (fun x => height x ≤ R/(2 : ℝ)^J)).card) : ℝ) ≤ D)
    (hblock : ∀ j < J,
      (((s.filter (fun x => R/(2 : ℝ)^(j+1) < height x ∧ height x ≤ R/(2 : ℝ)^j)).card) : ℝ) ≤
        A*(R/(2 : ℝ)^j)^p+B*(R/(2 : ℝ)^j)^q) :
    (s.card : ℝ) ≤ D+2*A*R^p+2*B*R^q := by
  classical
  have he := Counting.sum_eq_low_add_dyadic_blocks s height (fun _ => (1 : ℝ)) hR hheight J
  simp only [sum_const,nsmul_eq_mul,mul_one] at he
  calc
    _ = _ := he
    _ ≤ D+∑ j ∈ range J, (A*(R/(2 : ℝ)^j)^p+B*(R/(2 : ℝ)^j)^q) :=
      add_le_add hlow (sum_le_sum (fun j hj => hblock j (mem_range.mp hj)))
    _ = D+A*(∑ j ∈ range J, (R/(2 : ℝ)^j)^p)+B*(∑ j ∈ range J, (R/(2 : ℝ)^j)^q) := by
      rw [sum_add_distrib,← mul_sum,← mul_sum]
      ring
    _ ≤ D+A*(2*R^p)+B*(2*R^q) := add_le_add
      (add_le_add le_rfl (mul_le_mul_of_nonneg_left (sum_dyadic_radius_pow_le hR p J hp) hA))
      (mul_le_mul_of_nonneg_left (sum_dyadic_radius_pow_le hR q J hq) hB)
    _ = _ := by ring

end WaveTurbulence.CountLemmas
