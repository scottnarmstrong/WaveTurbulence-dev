/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.VdCB.CircleSourceBound
public import WaveTurbulence.Foundations.VdCB.IntegerRangeSum

/-! # Integer translations and arbitrary consecutive circle source blocks -/

public section

open Set
open WaveTurbulence.NumberTheory

namespace WaveTurbulence.VdCB

/-- Translating the physical integer interval preserves the uniform circle bound. -/
theorem norm_sum_circleColumnPhase_Ioc_le {R h U c : ℝ}
    (hU : 1 ≤ U) (hUR : 3 * U ≤ R) (hh : 1 ≤ h)
    {a b : ℤ} (hab : a ≤ b)
    (ha : R + c - 2 * U ≤ a) (hb : (b : ℝ) ≤ R + c - U)
    (haOct : R + c - R * (1 - 1 / Real.sqrt 2) ≤ a) :
    ‖∑ n ∈ Finset.Ioc a b, expPhase (circleColumnPhase R h ((n : ℝ) - c))‖ ≤
      circleBConstant * circleBScale R h U := by
  let N := (b - a).toNat
  have hN : (N : ℤ) = b - a := Int.toNat_of_nonneg (sub_nonneg.mpr hab)
  have hNR : (N : ℝ) = b - a := by exact_mod_cast hN
  have hs := norm_sum_circleColumnPhase_le_BScale (c := c - a) hU hUR hh
    (a := 0) (b := N) (Nat.zero_le _) (by push_cast; linarith only [ha])
    (by linarith only [hb, hNR]) (by push_cast; linarith only [haOct])
  have hbN : b = a + N := by omega
  rw [hbN, sum_Ioc_int_eq_range]
  rw [Nat.Ico_zero_eq_range] at hs
  convert hs using 2
  apply Finset.sum_congr rfl
  intro j _
  congr 2
  push_cast
  ring

/-- A consecutive finite set is bounded with only its first sample discarded.
Pointwise geometric hypotheses suffice, including for a clipped octant block. -/
theorem norm_sum_circleColumnPhase_convex_le {R h U c : ℝ}
    (hU : 1 ≤ U) (hUR : 3 * U ≤ R) (hh : 1 ≤ h)
    (S : Finset ℤ)
    (hconvex : ∀ x ∈ S, ∀ y ∈ S, ∀ z : ℤ, x ≤ z → z ≤ y → z ∈ S)
    (hblock : ∀ x ∈ S, R + c - (x : ℝ) ∈ Icc U (2 * U))
    (hoct : ∀ x ∈ S, R + c - (x : ℝ) ≤ R * (1 - 1 / Real.sqrt 2)) :
    ‖∑ x ∈ S, expPhase (circleColumnPhase R h ((x : ℝ) - c))‖ ≤
      (circleBConstant + 1) * circleBScale R h U := by
  have hU0 : 0 < U := zero_lt_one.trans_le hU
  have hR : 0 < R := (by positivity : 0 < 3 * U).trans_le hUR
  have hB1 := one_le_circleBScale hR (zero_lt_one.trans_le hh) hU
    (le_circleOscillation hU (by linarith only [hUR, hU0]) hh)
  classical
  by_cases hS : S.Nonempty
  · let a := S.min' hS
    let b := S.max' hS
    have haS : a ∈ S := Finset.min'_mem S hS
    have hbS : b ∈ S := Finset.max'_mem S hS
    have hab : a ≤ b := Finset.min'_le S b hbS
    have heq : S = insert a (Finset.Ioc a b) := by
      ext x
      constructor
      · intro hx
        have hal := Finset.min'_le S x hx
        have hbu := Finset.le_max' S x hx
        by_cases hax : x = a
        · exact Finset.mem_insert.mpr (Or.inl hax)
        · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_Ioc.mpr ⟨lt_of_le_of_ne hal (Ne.symm hax), hbu⟩))
      · intro hx
        obtain rfl | hx := Finset.mem_insert.mp hx
        · exact haS
        · have hx' := Finset.mem_Ioc.mp hx
          exact hconvex a haS b hbS x hx'.1.le hx'.2
    have hs := norm_sum_circleColumnPhase_Ioc_le (c := c) hU hUR hh hab
      (by have := (hblock a haS).2; linarith)
      (by have := (hblock b hbS).1; linarith)
      (by have := hoct a haS; linarith)
    rw [heq, Finset.sum_insert (by simp)]
    calc
      _ ≤ ‖expPhase (circleColumnPhase R h ((a : ℝ) - c))‖ +
          ‖∑ x ∈ Finset.Ioc a b, expPhase (circleColumnPhase R h ((x : ℝ) - c))‖ := norm_add_le _ _
      _ ≤ 1 + circleBConstant * circleBScale R h U := by rw [norm_expPhase]; exact add_le_add le_rfl hs
      _ ≤ _ := by nlinarith only [hB1]
  · rw [Finset.not_nonempty_iff_eq_empty.mp hS, Finset.sum_empty, norm_zero]
    apply mul_nonneg
    · unfold circleBConstant; positivity
    · exact zero_le_one.trans hB1

end WaveTurbulence.VdCB
