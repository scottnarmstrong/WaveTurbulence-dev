/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.WeylSums.RationalSpacing
public import Mathlib.Data.Nat.ModEq
import Mathlib.Tactic.LinearCombination

/-!
# Integer residue numerators for nearby rational frequencies

Subtracting the nearest integer to `sj` leaves an integer numerator plus the
small rational-approximation error. Fibers of this numerator are contained
in single residue classes, allowing harmonic counting on each fiber.
-/

public section

namespace WaveTurbulence.WeylSums

/-- The integer numerator after subtracting the nearest integer from `sj`. -/
@[expose] noncomputable def residueNumerator (s : ℝ) (a : ℤ) (q j : ℕ) : ℤ :=
  a * j - q * round (s * j)

/-- The exact real frequency represented by the residue numerator. -/
theorem residueNumerator_identity (s : ℝ) (a : ℤ) {q : ℕ} (hq : 0 < q) (j : ℕ) :
    (residueNumerator s a q j : ℝ) / q + (s - (a : ℝ) / q) * j =
      s * j - round (s * j) := by
  have hq' : (q : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_zero_of_lt hq)
  unfold residueNumerator
  push_cast
  field_simp
  ring

/-- Distance to the integers in terms of the residue numerator. -/
theorem norm_frequency_eq_residue (s : ℝ) (a : ℤ) {q : ℕ} (hq : 0 < q) (j : ℕ) :
    ‖(s * (j : ℝ) : AddCircle (1 : ℝ))‖ =
      |(residueNumerator s a q j : ℝ) / q + (s - (a : ℝ) / q) * j| := by
  rw [residueNumerator_identity s a hq j, AddCircle.norm_eq]
  simp only [inv_one, one_mul, mul_one]

/-- Equal numerator fibers lie in a single residue class modulo `q`. -/
theorem residueNumerator_mod_eq (s : ℝ) (a : ℤ) {q i j : ℕ}
    (ha : a.natAbs.Coprime q)
    (h : residueNumerator s a q i = residueNumerator s a q j) : i % q = j % q := by
  have hcop : Int.gcd (q : ℤ) a = 1 := by
    change Nat.gcd (Int.natAbs (q : ℤ)) a.natAbs = 1
    simpa only [Int.natAbs_natCast] using ha.symm.gcd_eq_one
  have hd : (q : ℤ) ∣ a * ((j : ℤ) - i) := by
    refine ⟨round (s * j) - round (s * i), ?_⟩
    unfold residueNumerator at h
    linear_combination -h
  exact Nat.modEq_iff_dvd.mpr (Int.dvd_of_dvd_mul_right_of_gcd_one hd hcop)

/-- A bounded rational-approximation error bounds all residue numerators. -/
theorem abs_residueNumerator_le (s : ℝ) (a : ℤ) {q N j : ℕ}
    (hq : 0 < q) (hj : j < N) {B : ℝ}
    (happrox : |s - (a : ℝ) / q| * N ≤ B / q) :
    |(residueNumerator s a q j : ℝ)| ≤ (q : ℝ) / 2 + B := by
  have hq' : (0 : ℝ) < q := Nat.cast_pos.mpr hq
  have hid := residueNumerator_identity s a hq j
  have hrep : (residueNumerator s a q j : ℝ) =
      q * (s * j - round (s * j)) - q * ((s - (a : ℝ) / q) * j) := by
    apply (div_left_inj' hq'.ne').mp
    field_simp at hid ⊢
    linear_combination hid
  have herr : |(s - (a : ℝ) / q) * j| ≤ B / q := by
    rw [abs_mul, abs_of_nonneg (show (0 : ℝ) ≤ j from Nat.cast_nonneg j)]
    exact (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hj.le) (abs_nonneg _)).trans happrox
  calc
    _ ≤ |q * (s * j - round (s * j))| + |q * ((s - (a : ℝ) / q) * j)| :=
      hrep ▸ abs_sub _ _
    _ = q * |s * j - round (s * j)| + q * |(s - (a : ℝ) / q) * j| := by
      rw [abs_mul, abs_mul, abs_of_pos hq']
    _ ≤ q * (1 / 2) + q * (B / q) :=
      add_le_add (mul_le_mul_of_nonneg_left (abs_sub_round _) hq'.le)
        (mul_le_mul_of_nonneg_left herr hq'.le)
    _ = q / 2 + B := by field_simp

end WaveTurbulence.WeylSums
