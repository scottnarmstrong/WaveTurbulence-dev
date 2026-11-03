/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import Mathlib.Analysis.Fourier.ZMod
import Mathlib.Tactic

/-!
# Complete quadratic Gauss sums

The finite rational-completion ingredient for the smooth-cutoff estimate.
The factor two accommodates even denominators without any parity restriction.
-/

public section

open scoped BigOperators ComplexConjugate
open Finset AddChar

namespace WaveTurbulence.WeylSums

/-- Complete quadratic sum over all residue classes. -/
@[expose] noncomputable def completeGauss {q : ℕ} [NeZero q] (a b : ZMod q) : ℂ :=
  ∑ x : ZMod q, ZMod.stdAddChar (a * x ^ 2 + b * x)

/-- The doubling map on a cyclic group has at most two zeros. -/
theorem card_zmod_two_mul_eq_zero_le_two (q : ℕ) [NeZero q] :
    ((univ : Finset (ZMod q)).filter (fun x => 2 * x = 0)).card ≤ 2 := by
  have hq : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  have hsub : (univ : Finset (ZMod q)).filter (fun x => 2 * x = 0) ⊆
      {0, ((q / 2 : ℕ) : ZMod q)} := by
    intro x hx
    have hx0 := (mem_filter.mp hx).2
    have hd : q ∣ 2 * x.val := by
      apply (ZMod.natCast_eq_zero_iff (2 * x.val) q).mp
      simpa only [Nat.cast_mul, Nat.cast_ofNat, ZMod.natCast_zmod_val] using hx0
    obtain ⟨k, hk⟩ := hd
    have hxq := ZMod.val_lt x
    have hklt : k < 2 := by nlinarith only [hk, hxq, hq]
    have hxval : x.val = 0 ∨ x.val = q / 2 := by
      have hk01 : k = 0 ∨ k = 1 := by omega
      rcases hk01 with rfl | rfl
      · simp only [mul_zero] at hk
        left
        omega
      · simp only [mul_one] at hk
        right
        omega
    rcases hxval with hz | hh
    · have heq : x = 0 := (ZMod.val_eq_zero x).mp hz
      simp only [heq, mem_insert, mem_singleton, true_or]
    · have heq : x = ((q / 2 : ℕ) : ZMod q) := by
        rw [← hh, ZMod.natCast_zmod_val]
      simp only [heq, mem_insert, mem_singleton, or_true]
  have hpair : ({0, ((q / 2 : ℕ) : ZMod q)} : Finset (ZMod q)).card ≤ 2 := by
    have hh := card_insert_le (0 : ZMod q) {((q / 2 : ℕ) : ZMod q)}
    simpa only [card_singleton] using hh
  exact (card_le_card hsub).trans hpair

/-- Complete quadratic sums have square-root cancellation, uniformly in the
linear coefficient and including even moduli. -/
theorem norm_completeGauss_sq_le {q : ℕ} [NeZero q] (a b : ZMod q) (ha : IsUnit a) :
    ‖completeGauss a b‖ ^ 2 ≤ 2 * (q : ℝ) := by
  classical
  let ψ : AddChar (ZMod q) ℂ := ZMod.stdAddChar
  have hnorm (x : ZMod q) : ‖ψ x‖ = 1 := by
    simp only [ψ, ZMod.stdAddChar_apply, Circle.norm_coe]
  have hconj (x : ZMod q) : conj (ψ x) = ψ (-x) := by
    rw [map_neg_eq_inv, Complex.inv_eq_conj (hnorm x)]
  have horth (c : ZMod q) : (∑ y : ZMod q, ψ (c * y)) = if c = 0 then (q : ℂ) else 0 := by
    split_ifs with hc
    · simp only [hc, zero_mul, map_zero_eq_one, sum_const, card_univ, ZMod.card,
        nsmul_eq_mul, mul_one]
    · simpa only [ψ, AddChar.mulShift_apply, mul_comm] using
        sum_eq_zero_of_ne_one (ZMod.isPrimitive_stdAddChar q hc)
  have hsq : ‖completeGauss a b‖ ^ 2 =
      ‖∑ x : ZMod q, ∑ y : ZMod q,
        ψ ((a * x ^ 2 + b * x) - (a * y ^ 2 + b * y))‖ := by
    calc
      _ = ‖completeGauss a b * conj (completeGauss a b)‖ := by
        rw [norm_mul, Complex.norm_conj, pow_two]
      _ = _ := by
        simp only [completeGauss, map_sum]
        rw [sum_mul]
        congr 1
        apply sum_congr rfl
        intro x _
        rw [mul_sum]
        apply sum_congr rfl
        intro y _
        rw [hconj, ← map_add_eq_mul]
        simp only [ψ, sub_eq_add_neg]
  have hshift (y : ZMod q) :
      (∑ x : ZMod q, ψ ((a * x ^ 2 + b * x) - (a * y ^ 2 + b * y))) =
        ∑ h : ZMod q, ψ ((2 * a * h) * y + (a * h ^ 2 + b * h)) := by
    symm
    refine Fintype.sum_equiv (Equiv.addRight y) _ _ ?_
    intro h
    congr 1
    dsimp
    ring
  rw [hsq, sum_comm]
  simp_rw [hshift]
  rw [sum_comm]
  have hinner (h : ZMod q) :
      (∑ y : ZMod q, ψ ((2 * a * h) * y + (a * h ^ 2 + b * h))) =
        (if 2 * a * h = 0 then (q : ℂ) else 0) * ψ (a * h ^ 2 + b * h) := by
    calc
      _ = (∑ y : ZMod q, ψ ((2 * a * h) * y)) * ψ (a * h ^ 2 + b * h) := by
        rw [sum_mul]
        apply sum_congr rfl
        intro y _
        exact map_add_eq_mul ψ _ _
      _ = _ := by rw [horth]
  simp_rw [hinner]
  calc
    _ ≤ ∑ h : ZMod q, ‖(if 2 * a * h = 0 then (q : ℂ) else 0) * ψ (a * h ^ 2 + b * h)‖ :=
      norm_sum_le _ _
    _ = (((univ : Finset (ZMod q)).filter (fun h => 2 * a * h = 0)).card : ℝ) * q := by
      simp only [norm_mul, hnorm, mul_one, apply_ite norm, Complex.norm_natCast, norm_zero,
        ← sum_filter, sum_const, nsmul_eq_mul]
    _ ≤ 2 * (q : ℝ) := by
      apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg q)
      have hker (h : ZMod q) : 2 * a * h = 0 ↔ 2 * h = 0 := by
        rw [show 2 * a * h = a * (2 * h) by ring]
        exact ha.mul_right_eq_zero
      simp_rw [hker]
      exact_mod_cast card_zmod_two_mul_eq_zero_le_two q

/-- Square-root form of the complete quadratic estimate. -/
theorem norm_completeGauss_le {q : ℕ} [NeZero q] (a b : ZMod q) (ha : IsUnit a) :
    ‖completeGauss a b‖ ≤ Real.sqrt (2 * q) := by
  exact (Real.le_sqrt (norm_nonneg _) (by positivity)).mpr (norm_completeGauss_sq_le a b ha)

/-- Fourier coefficients of the periodic rational quadratic phase. -/
@[expose] noncomputable def quadraticFourierCoeff {q : ℕ} [NeZero q] (a b : ZMod q) : ℂ :=
  (q : ℂ)⁻¹ * completeGauss a (-b)

/-- Rational completion, as an exact finite Fourier expansion. -/
theorem quadratic_completion {q : ℕ} [NeZero q] (a x : ZMod q) :
    ZMod.stdAddChar (a * x ^ 2) =
      ∑ b : ZMod q, quadraticFourierCoeff a b * ZMod.stdAddChar (b * x) := by
  let Φ : ZMod q → ℂ := fun y => ZMod.stdAddChar (a * y ^ 2)
  have hDFT (b : ZMod q) : ZMod.dft Φ b = completeGauss a (-b) := by
    rw [ZMod.dft_apply]
    simp only [smul_eq_mul, Φ, completeGauss]
    apply sum_congr rfl
    intro y _
    rw [← map_add_eq_mul]
    congr 1
    ring
  have hinv := congrFun ((ZMod.dft (N := q)).symm_apply_apply Φ) x
  rw [ZMod.invDFT_apply] at hinv
  simp only [smul_eq_mul, hDFT] at hinv
  calc
    _ = (q : ℂ)⁻¹ * ∑ b : ZMod q, ZMod.stdAddChar (b * x) * completeGauss a (-b) := hinv.symm
    _ = _ := by
      rw [mul_sum]
      apply sum_congr rfl
      intro b _
      rw [quadraticFourierCoeff]
      ring

/-- Uniform square-root bound for each rational-completion coefficient. -/
theorem norm_quadraticFourierCoeff_le {q : ℕ} [NeZero q] (a b : ZMod q) (ha : IsUnit a) :
    ‖quadraticFourierCoeff a b‖ ≤ Real.sqrt 2 / Real.sqrt q := by
  have hq : (0 : ℝ) < q := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne q))
  have hs : (Real.sqrt (q : ℝ)) ^ 2 = q := Real.sq_sqrt hq.le
  have hsp : 0 < Real.sqrt (q : ℝ) := Real.sqrt_pos.mpr hq
  rw [quadraticFourierCoeff, norm_mul, norm_inv, Complex.norm_natCast]
  calc
    _ ≤ (q : ℝ)⁻¹ * Real.sqrt (2 * q) :=
      mul_le_mul_of_nonneg_left (norm_completeGauss_le a (-b) ha) (inv_nonneg.mpr hq.le)
    _ = _ := by
      rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
      apply (eq_div_iff hsp.ne').mpr
      field_simp
      nlinarith only [hs]


end WaveTurbulence.WeylSums
