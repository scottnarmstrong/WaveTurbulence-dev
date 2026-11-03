/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Tactic

/-!
# Quantitative Gevrey-2 bounds

TARGET L623, with the owner-approved correction F41: derivative bounds have
absolute prefactors and exponential constants. This module records the
normalization `C * A^m * (2*m)!` and its elementary closure properties.
-/

public section

open scoped ContDiff

namespace WaveTurbulence.Fourier

/-- A specified global Gevrey-2 derivative bound. Smoothness is stated
separately when needed; this predicate only records the numerical estimates. -/
@[expose] def GevreyTwoBound (f : ℝ → ℝ) (C A : ℝ) : Prop :=
  ∀ (m : ℕ) (x : ℝ), |iteratedDeriv m f x| ≤ C * A ^ m * (Nat.factorial (2 * m) : ℝ)

/-- Constant functions satisfy the bound with exponential constant zero. -/
theorem gevreyTwoBound_const (c : ℝ) : GevreyTwoBound (fun _ => c) |c| 0 := by
  intro m x
  cases m with
  | zero => simp
  | succ m => simp [iteratedDeriv_const]

/-- Negation preserves the same constants. -/
theorem GevreyTwoBound.neg {f : ℝ → ℝ} {C A : ℝ} (hf : GevreyTwoBound f C A) :
    GevreyTwoBound (fun x => -f x) C A := by
  intro m x
  change |iteratedDeriv m (-f) x| ≤ _
  rw [iteratedDeriv_neg, abs_neg]
  exact hf m x

/-- Increasing either nonnegative constant preserves a Gevrey bound. -/
theorem GevreyTwoBound.mono {f : ℝ → ℝ} {C D A B : ℝ}
    (hf : GevreyTwoBound f C A) (hC : 0 ≤ C) (hA : 0 ≤ A)
    (hCD : C ≤ D) (hAB : A ≤ B) : GevreyTwoBound f D B := by
  intro m x
  apply (hf m x).trans
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul hCD (pow_le_pow_left₀ hA hAB m) (pow_nonneg hA m) (hC.trans hCD))
    (Nat.cast_nonneg _)

/-- Addition with a common exponential constant adds the prefactors. -/
theorem GevreyTwoBound.add {f g : ℝ → ℝ} {C D A : ℝ}
    (hf : GevreyTwoBound f C A) (hg : GevreyTwoBound g D A)
    (hfs : ContDiff ℝ ∞ f) (hgs : ContDiff ℝ ∞ g) :
    GevreyTwoBound (fun x => f x + g x) (C + D) A := by
  intro m x
  rw [iteratedDeriv_fun_add (hfs.of_le (by simp)).contDiffAt
    (hgs.of_le (by simp)).contDiffAt]
  exact (abs_add_le _ _).trans ((add_le_add (hf m x) (hg m x)).trans_eq (by ring))

private theorem factorial_pair_le {m i : ℕ} (hi : i ≤ m) :
    (Nat.factorial (2 * i) : ℝ) * Nat.factorial (2 * (m - i)) ≤
      Nat.factorial (2 * m) := by
  have he : 2 * i + 2 * (m - i) = 2 * m := by omega
  exact_mod_cast he ▸ Nat.le_of_dvd (Nat.factorial_pos _)
    (Nat.factorial_mul_factorial_dvd_factorial_add (2 * i) (2 * (m - i)))

/-- Products preserve Gevrey-2 bounds, with exponential constant `A+B`.
The constants are uniform in derivative order and position. -/
theorem GevreyTwoBound.mul {f g : ℝ → ℝ} {C D A B : ℝ}
    (hf : GevreyTwoBound f C A) (hg : GevreyTwoBound g D B)
    (hfs : ContDiff ℝ ∞ f) (hgs : ContDiff ℝ ∞ g)
    (hC : 0 ≤ C) (hD : 0 ≤ D) (hA : 0 ≤ A) (hB : 0 ≤ B) :
    GevreyTwoBound (fun x => f x * g x) (C * D) (A + B) := by
  intro m x
  rw [iteratedDeriv_fun_mul (hfs.of_le (by simp)).contDiffAt
    (hgs.of_le (by simp)).contDiffAt]
  calc
    |∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ) * iteratedDeriv i f x *
        iteratedDeriv (m - i) g x| ≤
        ∑ i ∈ Finset.range (m + 1),
          (m.choose i : ℝ) * |iteratedDeriv i f x| * |iteratedDeriv (m - i) g x| := by
      simpa only [abs_mul, Nat.abs_cast] using
        Finset.abs_sum_le_sum_abs (s := Finset.range (m + 1))
          (f := fun i => (m.choose i : ℝ) * iteratedDeriv i f x *
            iteratedDeriv (m - i) g x)
    _ ≤ ∑ i ∈ Finset.range (m + 1),
          (m.choose i : ℝ) * (C * D) *
            (A ^ i * B ^ (m - i)) * (Nat.factorial (2 * m) : ℝ) := by
      apply Finset.sum_le_sum
      intro i hi
      have him : i ≤ m := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
      calc
        (m.choose i : ℝ) * |iteratedDeriv i f x| * |iteratedDeriv (m - i) g x| ≤
            (m.choose i : ℝ) * (C * A ^ i * (Nat.factorial (2 * i) : ℝ)) *
              (D * B ^ (m - i) * (Nat.factorial (2 * (m - i)) : ℝ)) :=
          mul_le_mul (mul_le_mul_of_nonneg_left (hf i x) (Nat.cast_nonneg _))
            (hg (m - i) x) (abs_nonneg _) (by positivity)
        _ = ((m.choose i : ℝ) * (C * D) * (A ^ i * B ^ (m - i))) *
            ((Nat.factorial (2 * i) : ℝ) * Nat.factorial (2 * (m - i))) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left (factorial_pair_le him) (by positivity)
    _ = C * D * (A + B) ^ m * (Nat.factorial (2 * m) : ℝ) := by
      rw [add_pow]
      simp only [Finset.sum_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring

/-- Affine precomposition preserves the bound, multiplying the exponential
constant by the absolute value of the slope. -/
theorem GevreyTwoBound.comp_affine {f : ℝ → ℝ} {C A : ℝ}
    (hf : GevreyTwoBound f C A) (hfs : ContDiff ℝ ∞ f)
    (a b : ℝ) : GevreyTwoBound (fun x => f (a * x + b)) C (|a| * A) := by
  intro m x
  have he : (fun x => f (a * x + b)) = (fun y => f (y + b)) ∘ (fun x => a * x) := rfl
  rw [he, show (fun y => f (y + b)) ∘ (fun x => a * x) =
      (fun x => (fun y => f (y + b)) (a * x)) from rfl,
    iteratedDeriv_comp_const_mul (f := fun y => f (y + b))
      ((hfs.comp (contDiff_id.add contDiff_const)).of_le (by simp)) a,
    iteratedDeriv_comp_add_const]
  simp only [abs_mul, abs_pow]
  calc
    |a| ^ m * |iteratedDeriv m f (a * x + b)| ≤
        |a| ^ m * (C * A ^ m * (Nat.factorial (2 * m) : ℝ)) :=
      mul_le_mul_of_nonneg_left (hf m _) (pow_nonneg (abs_nonneg _) _)
    _ = _ := by rw [mul_pow]; ring

end WaveTurbulence.Fourier
