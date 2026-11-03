/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import Mathlib.Analysis.Normed.Group.AddCircle
public import Mathlib.Data.Int.GCD

/-!
# Separation of rational frequencies

Nonzero rational residues with denominator `q` have distance at least `1/q`
from the integers. This is an arithmetic ingredient for counting the
near-resonances in the Weyl differencing bound (DH23's Gauss lemma).
-/

public section

namespace WaveTurbulence.WeylSums

/-- A rational number with numerator not divisible by its denominator stays
at least `1/q` away from the integers. -/
theorem inv_den_le_norm_rat (m : ℤ) {q : ℕ} (hq : 0 < q) (hm : ¬ (q : ℤ) ∣ m) :
    1 / (q : ℝ) ≤ ‖((m : ℝ) / (q : ℝ) : AddCircle (1 : ℝ))‖ := by
  let k : ℤ := round ((m : ℝ) / q)
  have hne : m - k * q ≠ 0 := by
    intro h
    apply hm
    exact ⟨k, by rw [mul_comm]; exact (sub_eq_zero.mp h)⟩
  have hge : (1 : ℝ) ≤ |((m - k * q : ℤ) : ℝ)| := by
    exact_mod_cast Int.one_le_abs hne
  have hq' : (0 : ℝ) < q := Nat.cast_pos.mpr hq
  rw [AddCircle.norm_eq]
  simp only [inv_one, one_mul, mul_one]
  change 1 / (q : ℝ) ≤ |(m : ℝ) / q - (k : ℝ)|
  have heq : (m : ℝ) / q - k = ((m - k * q : ℤ) : ℝ) / q := by
    push_cast
    field_simp
  rw [heq, abs_div, abs_of_pos hq']
  exact div_le_div_of_nonneg_right hge hq'.le

/-- Coprimality ensures every nonzero residue index has nonzero numerator
modulo the denominator. -/
theorem inv_den_le_norm_coprime_mul (a : ℤ) {q : ℕ} (hq : 0 < q)
    (ha : a.natAbs.Coprime q) (d : ℤ) (hd : ¬ (q : ℤ) ∣ d) :
    1 / (q : ℝ) ≤ ‖((a : ℝ) * (d : ℝ) / (q : ℝ) : AddCircle (1 : ℝ))‖ := by
  have hcop : Int.gcd (q : ℤ) a = 1 := by
    change Nat.gcd (Int.natAbs (q : ℤ)) a.natAbs = 1
    simpa only [Int.natAbs_natCast, Nat.gcd_comm] using ha.symm.gcd_eq_one
  have hnd : ¬ (q : ℤ) ∣ a * d := by
    intro h
    exact hd (Int.dvd_of_dvd_mul_right_of_gcd_one h hcop)
  simpa only [Int.cast_mul] using inv_den_le_norm_rat (a * d) hq hnd

/-- Rational separation persists quantitatively under a perturbation of the
quadratic coefficient. This does not assume any exponential-sum estimate. -/
theorem inv_den_le_norm_mul_add_error (s : ℝ) (a : ℤ) {q : ℕ} (hq : 0 < q)
    (ha : a.natAbs.Coprime q) (d : ℤ) (hd : ¬ (q : ℤ) ∣ d) :
    1 / (q : ℝ) ≤ ‖(s * (d : ℝ) : AddCircle (1 : ℝ))‖ +
      |s - (a : ℝ) / (q : ℝ)| * |(d : ℝ)| := by
  have hdist := inv_den_le_norm_coprime_mul a hq ha d hd
  have htriangle := norm_sub_le
    (s * (d : ℝ) : AddCircle (1 : ℝ))
    ((s - (a : ℝ) / (q : ℝ)) * (d : ℝ) : AddCircle (1 : ℝ))
  have hproj : ‖(((s - (a : ℝ) / (q : ℝ)) * (d : ℝ) : ℝ) : AddCircle (1 : ℝ))‖ ≤
      |s - (a : ℝ) / (q : ℝ)| * |(d : ℝ)| := by
    simpa only [Real.norm_eq_abs, abs_mul] using
      (QuotientAddGroup.norm_mk_le_norm (S := AddSubgroup.zmultiples (1 : ℝ))
        (m := (s - (a : ℝ) / (q : ℝ)) * (d : ℝ)))
  have heq : (s * (d : ℝ) : AddCircle (1 : ℝ)) -
      ((s - (a : ℝ) / (q : ℝ)) * (d : ℝ) : AddCircle (1 : ℝ)) =
      ((a : ℝ) * (d : ℝ) / (q : ℝ) : AddCircle (1 : ℝ)) := by
    rw [← QuotientAddGroup.mk_sub]
    congr 1
    ring
  rw [heq] at htriangle
  exact hdist.trans (htriangle.trans (add_le_add_right hproj _))


end WaveTurbulence.WeylSums
