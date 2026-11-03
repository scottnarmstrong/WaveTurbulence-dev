/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Fourier.Gevrey
public import Mathlib.Data.Nat.Choose.Vandermonde
import Mathlib.Tactic

/-!
# Reciprocal closure for Gevrey-2 bounds

Uniform positivity of the denominator gives uniform Gevrey constants for
its reciprocal. This supplies the quantitative denominator control needed
for the explicit cutoff based on `Real.smoothTransition`.
-/

public section

open scoped ContDiff

namespace WaveTurbulence.Fourier

private theorem choose_double_le (m i : ℕ) : m.choose i ≤ (2 * m).choose (2 * i) := by
  have hh : m.choose i * m.choose i ≤ (m + m).choose (i + i) := by
    rw [Nat.add_choose_eq]
    exact Finset.single_le_sum (f := fun ij : ℕ × ℕ => m.choose ij.1 * m.choose ij.2) (a := (i, i)) (fun _ _ => Nat.zero_le _) (Finset.mem_antidiagonal.mpr rfl)
  have hs : m.choose i ≤ m.choose i * m.choose i := by
    have : m.choose i = 0 ∨ 1 ≤ m.choose i := by omega
    rcases this with h | h
    · simp [h]
    · exact Nat.le_mul_of_pos_right _ h
  simpa only [two_mul] using hs.trans hh

private theorem gevrey_leibniz_factor {m i : ℕ} (hi : i ≤ m) :
    (m.choose i : ℝ) * (Nat.factorial (2 * i) : ℝ) *
      (Nat.factorial (2 * (m - i)) : ℝ) ≤ (Nat.factorial (2 * m) : ℝ) := by
  have he : 2 * m - 2 * i = 2 * (m - i) := by omega
  have hf := Nat.choose_mul_factorial_mul_factorial (show 2 * i ≤ 2 * m by omega)
  rw [he] at hf
  exact_mod_cast (Nat.mul_le_mul_right (Nat.factorial (2 * (m - i)))
    (Nat.mul_le_mul_right (Nat.factorial (2 * i)) (choose_double_le m i))).trans_eq hf

private theorem geometric_majorant {C A B δ : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hδ : 0 ≤ δ) (he : C * A + δ * A ≤ δ * B) (m : ℕ) :
    C * (∑ j ∈ Finset.range m, A ^ (j + 1) * B ^ (m - 1 - j)) ≤ δ * B ^ m := by
  induction m with
  | zero => simpa using hδ
  | succ m ih =>
    rw [Finset.sum_range_succ']
    have hs : (∑ j ∈ Finset.range m, A ^ (j + 1 + 1) * B ^ (m - (j + 1))) =
        A * ∑ j ∈ Finset.range m, A ^ (j + 1) * B ^ (m - 1 - j) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      rw [show m - (j + 1) = m - 1 - j by omega, pow_succ]
      ring
    simp only [Nat.add_sub_cancel, Nat.sub_zero, Nat.zero_add, pow_one, hs]
    calc
      C * (A * ∑ j ∈ Finset.range m, A ^ (j + 1) * B ^ (m - 1 - j) + A * B ^ m) =
          A * (C * ∑ j ∈ Finset.range m, A ^ (j + 1) * B ^ (m - 1 - j)) +
            C * A * B ^ m := by ring
      _ ≤ A * (δ * B ^ m) + C * A * B ^ m :=
        add_le_add (mul_le_mul_of_nonneg_left ih hA) le_rfl
      _ = (C * A + δ * A) * B ^ m := by ring
      _ ≤ δ * B ^ (m + 1) := by
        simpa [pow_succ, mul_assoc, mul_comm, mul_left_comm] using mul_le_mul_of_nonneg_right he (pow_nonneg hB m)

/-- Reciprocal closure with explicit constants. Positivity is uniform in `x`;
no derivative estimate is hidden in the lower-bound hypothesis. -/
theorem GevreyTwoBound.inv {f : ℝ → ℝ} {C A δ : ℝ}
    (hf : GevreyTwoBound f C A) (hfs : ContDiff ℝ ∞ f)
    (hC : 0 ≤ C) (hA : 0 ≤ A) (hδ : 0 < δ) (hlo : ∀ x, δ ≤ f x) :
    GevreyTwoBound (fun x => (f x)⁻¹) δ⁻¹ (A * (1 + C / δ)) := by
  have hfpos (x : ℝ) : 0 < f x := hδ.trans_le (hlo x)
  have hgi : ContDiff ℝ ∞ (fun x => (f x)⁻¹) := hfs.inv (fun x => (hfpos x).ne')
  let B := A * (1 + C / δ)
  have hB : 0 ≤ B := mul_nonneg hA (by positivity)
  have he : C * A + δ * A ≤ δ * B := by
    dsimp [B]
    field_simp
    ring_nf
    exact le_rfl
  intro m
  induction m using Nat.strong_induction_on with
  | h m ih =>
    intro x
    rcases m with _ | n
    · simpa [abs_of_pos (hfpos x)] using inv_le_inv₀ (hfpos x) hδ |>.2 (hlo x)
    have hm : 0 < n + 1 := Nat.zero_lt_succ _
    have hid : (fun y => f y * (f y)⁻¹) = fun _ => (1 : ℝ) := by
      funext y
      exact mul_inv_cancel₀ (hfpos y).ne'
    have hd := iteratedDeriv_fun_mul
      (hfs.of_le (show (n + 1 : WithTop ℕ∞) ≤ ∞ by simp)).contDiffAt
      (hgi.of_le (show (n + 1 : WithTop ℕ∞) ≤ ∞ by simp)).contDiffAt (x := x)
    rw [hid, iteratedDeriv_const, ite_eq_right (Nat.ne_of_gt hm), Finset.sum_range_succ'] at hd
    simp only [Nat.choose_zero_right, Nat.cast_one, one_mul, iteratedDeriv_zero,
      Nat.sub_zero] at hd
    have habs : f x * |iteratedDeriv (n + 1) (fun y => (f y)⁻¹) x| ≤
        ∑ j ∈ Finset.range (n + 1), ((n + 1).choose (j + 1) : ℝ) *
          |iteratedDeriv (j + 1) f x| *
          |iteratedDeriv (n + 1 - (j + 1)) (fun y => (f y)⁻¹) x| := by
      have hz : f x * iteratedDeriv (n + 1) (fun y => (f y)⁻¹) x =
          -(∑ j ∈ Finset.range (n + 1), ((n + 1).choose (j + 1) : ℝ) *
            iteratedDeriv (j + 1) f x *
            iteratedDeriv (n + 1 - (j + 1)) (fun y => (f y)⁻¹) x) := by linarith only [hd]
      calc
        _ = |f x * iteratedDeriv (n + 1) (fun y => (f y)⁻¹) x| := by
          rw [abs_mul, abs_of_pos (hfpos x)]
        _ = _ := by rw [hz, abs_neg]
        _ ≤ _ := by
          simpa only [abs_mul, Nat.abs_cast] using Finset.abs_sum_le_sum_abs
            (s := Finset.range (n + 1))
            (f := fun j => ((n + 1).choose (j + 1) : ℝ) * iteratedDeriv (j + 1) f x *
              iteratedDeriv (n + 1 - (j + 1)) (fun y => (f y)⁻¹) x)
    have hsum : (∑ j ∈ Finset.range (n + 1), ((n + 1).choose (j + 1) : ℝ) *
          |iteratedDeriv (j + 1) f x| *
          |iteratedDeriv (n + 1 - (j + 1)) (fun y => (f y)⁻¹) x|) ≤
        C * δ⁻¹ * (Nat.factorial (2 * (n + 1)) : ℝ) *
          (∑ j ∈ Finset.range (n + 1), A ^ (j + 1) * B ^ (n - j)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro j hj
      have hjn : j < n + 1 := Finset.mem_range.mp hj
      have hjle : j + 1 ≤ n + 1 := by omega
      have hk : n + 1 - (j + 1) < n + 1 := by omega
      calc
        _ ≤ ((n + 1).choose (j + 1) : ℝ) *
            (C * A ^ (j + 1) * (Nat.factorial (2 * (j + 1)) : ℝ)) *
            (δ⁻¹ * B ^ (n + 1 - (j + 1)) *
              (Nat.factorial (2 * (n + 1 - (j + 1))) : ℝ)) :=
          mul_le_mul (mul_le_mul_of_nonneg_left (hf _ _) (Nat.cast_nonneg _))
            (ih _ hk x) (abs_nonneg _) (by positivity)
        _ = (C * δ⁻¹ * (A ^ (j + 1) * B ^ (n - j))) *
            (((n + 1).choose (j + 1) : ℝ) * Nat.factorial (2 * (j + 1)) *
              Nat.factorial (2 * (n + 1 - (j + 1)))) := by
          rw [show n + 1 - (j + 1) = n - j by omega]
          ring
        _ ≤ _ := by
          simpa only [mul_assoc, mul_left_comm, mul_comm] using
            mul_le_mul_of_nonneg_left (gevrey_leibniz_factor hjle)
              (show 0 ≤ C * δ⁻¹ * (A ^ (j + 1) * B ^ (n - j)) by positivity)
    have hgeo := geometric_majorant hA hB hδ.le he (n + 1)
    simp only [Nat.add_sub_cancel] at hgeo
    have htotal : δ * |iteratedDeriv (n + 1) (fun y => (f y)⁻¹) x| ≤
        (Nat.factorial (2 * (n + 1)) : ℝ) * B ^ (n + 1) := by
      calc
        _ ≤ f x * |iteratedDeriv (n + 1) (fun y => (f y)⁻¹) x| :=
          mul_le_mul_of_nonneg_right (hlo x) (abs_nonneg _)
        _ ≤ _ := habs.trans hsum
        _ ≤ _ := by
          have hh := mul_le_mul_of_nonneg_left hgeo
            (show 0 ≤ δ⁻¹ * (Nat.factorial (2 * (n + 1)) : ℝ) by positivity)
          calc
            _ = (δ⁻¹ * (Nat.factorial (2 * (n + 1)) : ℝ)) *
                (C * ∑ j ∈ Finset.range (n + 1), A ^ (j + 1) * B ^ (n - j)) := by ring
            _ ≤ _ := hh
            _ = _ := by field_simp
    change _ ≤ δ⁻¹ * B ^ (n + 1) * (Nat.factorial (2 * (n + 1)) : ℝ)
    apply (mul_le_mul_iff_right₀ hδ).mp
    convert htotal using 1
    field_simp

end WaveTurbulence.Fourier
