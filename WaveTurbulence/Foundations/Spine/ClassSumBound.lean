/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Algebra.Order.Field.GeomSum
public import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic
/-! TARGET L2249-L2252 (finalprooffin): summing the per-class bounds over the classes, using the
class count `C_0^n (C_0 r)! (C_0 R)! C_2^{g+r}` for classes with incoherency index `g` and
`rho-bar = r`. Pure algebra with explicit smallness hypotheses. -/
public section
set_option autoImplicit false
namespace WaveTurbulence.LGSpine
open Finset

theorem geom_range_le_two {x : ℝ} (hx : 0 ≤ x) (hx2 : x ≤ 1 / 2) (m : ℕ) :
    ∑ i ∈ range m, x ^ i ≤ 2 := by
  have h := geom_sum_Ico_le_of_lt_one (m := 0) (n := m) hx (by linarith)
  rw [← Finset.range_eq_Ico, pow_zero] at h
  refine h.trans ?_
  rw [div_le_iff₀ (by linarith)]
  linarith

theorem class_sum_bound {ι : Type*} [Fintype ι] (K : ι → ℂ) (gb rb : ι → ℕ) (n R C₀ : ℕ)
    (H B T S U C₂ : ℝ) (hH : 0 ≤ H) (hB : 0 ≤ B) (hT : 0 ≤ T) (hS : 0 ≤ S) (hU : 0 ≤ U)
    (hC₂ : 0 ≤ C₂)
    (hpiece : ∀ π, ‖K π‖ ≤ H * B ^ n * T ^ gb π * S ^ rb π * U)
    (hrb : ∀ π, 1 ≤ rb π ∧ rb π ≤ n) (hgb : ∀ π, gb π ≤ n)
    (hcount : ∀ g r, (((univ.filter fun π => gb π = g ∧ rb π = r).card : ℕ) : ℝ) ≤
      (C₀ : ℝ) ^ n * (((C₀ * r).factorial : ℕ) : ℝ) * (((C₀ * R).factorial : ℕ) : ℝ) * C₂ ^ (g + r))
    (hT2 : C₂ * T ≤ 1 / 2) (hS2 : ((C₀ * n : ℕ) : ℝ) ^ C₀ * C₂ * S ≤ 1 / 2) :
    ‖∑ π, K π‖ ≤ 4 * (H * B ^ n * U * (C₀ : ℝ) ^ n * (((C₀ * R).factorial : ℕ) : ℝ) *
      (((C₀ * n : ℕ) : ℝ) ^ C₀ * C₂ * S)) := by
  classical
  set P0 : ℝ := H * B ^ n * U * (C₀ : ℝ) ^ n * (((C₀ * R).factorial : ℕ) : ℝ) with hP0
  set x : ℝ := C₂ * T with hx
  set q : ℝ := ((C₀ * n : ℕ) : ℝ) ^ C₀ * C₂ * S with hq
  have hP0nn : 0 ≤ P0 := by positivity
  have hxnn : 0 ≤ x := by positivity
  have hqnn : 0 ≤ q := by positivity
  let f : ℕ → ℕ → ℝ := fun g r => H * B ^ n * T ^ g * S ^ r * U
  -- reorganize the sum over pieces by (g, r)
  have hsum : ∑ π, f (gb π) (rb π) =
      ∑ y ∈ range (n + 1) ×ˢ range (n + 1),
        (((univ.filter fun π => gb π = y.1 ∧ rb π = y.2).card : ℕ) : ℝ) * f y.1 y.2 := by
    rw [← Finset.sum_fiberwise_of_maps_to (s := univ) (t := range (n + 1) ×ˢ range (n + 1))
      (g := fun π => (gb π, rb π)) (f := fun π => f (gb π) (rb π))
      (fun π _ => mem_product.mpr ⟨mem_range.mpr (Nat.lt_succ_of_le (hgb π)),
        mem_range.mpr (Nat.lt_succ_of_le (hrb π).2)⟩)]
    apply sum_congr rfl
    intro y _
    have : (univ.filter fun π => (gb π, rb π) = y) = (univ.filter fun π => gb π = y.1 ∧ rb π = y.2) := by
      ext π; simp [Prod.ext_iff]
    rw [this, sum_congr rfl (g := fun _ => f y.1 y.2)]
    · simp
    · intro π hπ
      have := (mem_filter.mp hπ).2
      rw [this.1, this.2]
  have hterm : ∀ y ∈ range (n + 1) ×ˢ range (n + 1),
      (((univ.filter fun π => gb π = y.1 ∧ rb π = y.2).card : ℕ) : ℝ) * f y.1 y.2 ≤
        if y.2 = 0 then 0 else P0 * x ^ y.1 * q ^ y.2 := by
    intro y hy
    obtain ⟨hg, hr⟩ := mem_product.mp hy
    have hrn : y.2 ≤ n := Nat.lt_succ_iff.mp (mem_range.mp hr)
    by_cases h0 : y.2 = 0
    · have hempty : (univ.filter fun π => gb π = y.1 ∧ rb π = y.2) = ∅ := by
        apply Finset.filter_eq_empty_iff.mpr
        intro π _ hπ
        have := (hrb π).1
        omega
      rw [if_pos h0, hempty]; simp
    · rw [if_neg h0]
      have hfac : (((C₀ * y.2).factorial : ℕ) : ℝ) ≤ (((C₀ * n : ℕ) : ℝ) ^ C₀) ^ y.2 := by
        have h1 : ((C₀ * y.2).factorial : ℕ) ≤ (C₀ * y.2) ^ (C₀ * y.2) := Nat.factorial_le_pow _
        have h2 : (C₀ * y.2) ^ (C₀ * y.2) ≤ (C₀ * n) ^ (C₀ * y.2) :=
          Nat.pow_le_pow_left (Nat.mul_le_mul_left _ hrn) _
        have h3 := h1.trans h2
        have h4 : (((C₀ * n : ℕ) : ℝ) ^ C₀) ^ y.2 = (((C₀ * n) ^ (C₀ * y.2) : ℕ) : ℝ) := by
          push_cast; rw [← pow_mul]
        rw [h4]; exact_mod_cast h3
      calc (((univ.filter fun π => gb π = y.1 ∧ rb π = y.2).card : ℕ) : ℝ) * f y.1 y.2
          ≤ ((C₀ : ℝ) ^ n * (((C₀ * y.2).factorial : ℕ) : ℝ) * (((C₀ * R).factorial : ℕ) : ℝ) *
              C₂ ^ (y.1 + y.2)) * f y.1 y.2 :=
            mul_le_mul_of_nonneg_right (hcount y.1 y.2) (by positivity)
        _ ≤ ((C₀ : ℝ) ^ n * ((((C₀ * n : ℕ) : ℝ) ^ C₀) ^ y.2) * (((C₀ * R).factorial : ℕ) : ℝ) *
              C₂ ^ (y.1 + y.2)) * f y.1 y.2 := by
            apply mul_le_mul_of_nonneg_right _ (by positivity)
            have hC0 : (0 : ℝ) ≤ (C₀ : ℝ) ^ n := by positivity
            have hRf : (0 : ℝ) ≤ (((C₀ * R).factorial : ℕ) : ℝ) := by positivity
            have hCp : (0 : ℝ) ≤ C₂ ^ (y.1 + y.2) := by positivity
            exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hfac hC0) hRf |>.trans_eq' rfl |> fun h => mul_le_mul_of_nonneg_right h hCp
        _ = P0 * x ^ y.1 * q ^ y.2 := by
            simp only [hP0, hx, hq, f]
            rw [pow_add, mul_pow, mul_pow, mul_pow]
            ring
  have hnorm : ‖∑ π, K π‖ ≤ ∑ π, f (gb π) (rb π) :=
    (norm_sum_le _ _).trans (sum_le_sum fun π _ => hpiece π)
  refine hnorm.trans ?_
  rw [hsum]
  refine (sum_le_sum hterm).trans ?_
  rw [sum_product]
  have hinner : ∀ g : ℕ, ∑ r ∈ range (n + 1), (if r = 0 then (0 : ℝ) else P0 * x ^ g * q ^ r) ≤
      P0 * x ^ g * (2 * q) := by
    intro g
    have e : ∑ r ∈ range (n + 1), (if r = 0 then (0 : ℝ) else P0 * x ^ g * q ^ r) =
        ∑ r ∈ range n, P0 * x ^ g * q ^ (r + 1) := by
      rw [sum_range_succ']; simp
    rw [e]
    have := geom_range_le_two (x := q) hqnn (by linarith) n
    calc ∑ r ∈ range n, P0 * x ^ g * q ^ (r + 1) = P0 * x ^ g * q * ∑ r ∈ range n, q ^ r := by
          rw [mul_sum]; apply sum_congr rfl; intro r _; ring
      _ ≤ P0 * x ^ g * q * 2 := mul_le_mul_of_nonneg_left this (by positivity)
      _ = P0 * x ^ g * (2 * q) := by ring
  calc ∑ g ∈ range (n + 1), ∑ r ∈ range (n + 1), (if r = 0 then (0 : ℝ) else P0 * x ^ g * q ^ r)
      ≤ ∑ g ∈ range (n + 1), P0 * x ^ g * (2 * q) := sum_le_sum fun g _ => hinner g
    _ = P0 * (2 * q) * ∑ g ∈ range (n + 1), x ^ g := by
        rw [mul_sum]; apply sum_congr rfl; intro g _; ring
    _ ≤ P0 * (2 * q) * 2 := mul_le_mul_of_nonneg_left (geom_range_le_two hxnn hT2 _) (by positivity)
    _ = 4 * (P0 * q) := by ring

end WaveTurbulence.LGSpine
