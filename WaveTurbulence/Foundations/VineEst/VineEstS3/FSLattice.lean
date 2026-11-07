/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Fourier.LatticeConvergence
public import WaveTurbulence.Foundations.Fourier.CoordinateSchwartz
public import WaveTurbulence.Foundations.Torus.Inversion

/-! # Uniform weighted lattice sums of shifted Schwartz functions (B2, step 2)

`∑_{m ∈ ℤ^r} (1 + ‖m - y‖)^θ |H(m - y)| ≤ C` uniformly in the shift `y ∈ ℝ^r`, for a Schwartz function `H`.
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineEstS3.FS
open WaveTurbulence WaveTurbulence.Fourier MeasureTheory Set
open scoped SchwartzMap

variable {r : ℕ}

/-- The lattice point as a real vector. -/
def zvec (m : Fin r → ℤ) : Fin r → ℝ := fun i => (m i : ℝ)

/-- The pointwise bound for one centred lattice term. -/
theorem shifted_term_le (H : 𝓢((Fin r → ℝ), ℂ)) {θ : ℝ} (hθ : 0 ≤ θ) (x : Fin r → ℝ)
    (hxn : ‖x‖ ≤ 1 / 2) (n : Fin r → ℤ) :
    (1 + ‖x + zvec n‖) ^ θ * ‖H (x + zvec n)‖ ≤ (3 / 2 : ℝ) ^ θ *
      ((2 : ℝ) ^ (⌈θ⌉₊ + 2 * r - 1) * (SchwartzMap.seminorm ℂ 0 0 H +
        SchwartzMap.seminorm ℂ (⌈θ⌉₊ + 2 * r) 0 H) * (1 + 1 / 2) ^ (⌈θ⌉₊ + 2 * r)) *
      (1 + ‖n‖) ^ (-((2 * r : ℕ) : ℤ)) := by
  set N : ℕ := ⌈θ⌉₊ + 2 * r with hN
  have hb : 1 + ‖x + zvec n‖ ≤ (3 / 2) * (1 + ‖n‖) := by
    have h1 : ‖x + zvec n‖ ≤ ‖x‖ + ‖n‖ := by
      rw [← norm_integerCast n]; exact norm_add_le _ _
    have h2 : (0 : ℝ) ≤ ‖n‖ := norm_nonneg _
    linarith
  have h1 : (1 + ‖x + zvec n‖) ^ θ ≤ ((3 / 2) * (1 + ‖n‖)) ^ θ :=
    Real.rpow_le_rpow (by positivity) hb hθ
  rw [Real.mul_rpow (by norm_num) (by positivity)] at h1
  have hnn : (1 : ℝ) ≤ 1 + ‖n‖ := by linarith [norm_nonneg n]
  have hH := schwartz_translate_weight_le H N (R := 1 / 2) (by norm_num) hxn n
  have hpow : (1 + ‖n‖) ^ θ ≤ (1 + ‖n‖) ^ (N : ℝ) * (1 + ‖n‖) ^ (-((2 * r : ℕ) : ℝ)) := by
    rw [← Real.rpow_add (by linarith)]
    apply Real.rpow_le_rpow_of_exponent_le hnn
    have : (θ : ℝ) ≤ ⌈θ⌉₊ := Nat.le_ceil θ
    simp only [hN]; push_cast; linarith
  have hwz : (1 + ‖n‖) ^ (-((2 * r : ℕ) : ℤ)) = (1 + ‖n‖) ^ (-((2 * r : ℕ) : ℝ)) := by
    rw [← Real.rpow_intCast]; push_cast; rfl
  rw [hwz]
  calc (1 + ‖x + zvec n‖) ^ θ * ‖H (x + zvec n)‖
      ≤ ((3 / 2 : ℝ) ^ θ * (1 + ‖n‖) ^ θ) * ‖H (x + zvec n)‖ :=
        mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
    _ ≤ ((3 / 2 : ℝ) ^ θ * ((1 + ‖n‖) ^ (N : ℝ) * (1 + ‖n‖) ^ (-((2 * r : ℕ) : ℝ)))) *
          ‖H (x + zvec n)‖ := by gcongr
    _ = (3 / 2 : ℝ) ^ θ * ((1 + ‖n‖) ^ (-((2 * r : ℕ) : ℝ)) *
          ((1 + ‖n‖) ^ N * ‖H (x + zvec n)‖)) := by
        rw [Real.rpow_natCast]; ring
    _ ≤ (3 / 2 : ℝ) ^ θ * ((1 + ‖n‖) ^ (-((2 * r : ℕ) : ℝ)) *
          ((2 : ℝ) ^ (N - 1) * (SchwartzMap.seminorm ℂ 0 0 H + SchwartzMap.seminorm ℂ N 0 H) *
            (1 + 1 / 2) ^ N)) := by
        have hH' : (1 + ‖n‖) ^ N * ‖H (x + zvec n)‖ ≤ (2 : ℝ) ^ (N - 1) *
            (SchwartzMap.seminorm ℂ 0 0 H + SchwartzMap.seminorm ℂ N 0 H) * (1 + 1 / 2) ^ N := hH
        exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hH' (by positivity)) (by positivity)
    _ = _ := by ring

theorem tsum_addRight_shift (n₀ : Fin r → ℤ) (f : (Fin r → ℤ) → ℝ) :
    ∑' n, f (n + n₀) = ∑' m, f m := (Equiv.addRight n₀).tsum_eq f

theorem summable_addRight_shift (n₀ : Fin r → ℤ) (f : (Fin r → ℤ) → ℝ) :
    Summable (fun n => f (n + n₀)) ↔ Summable f := (Equiv.addRight n₀).summable_iff (f := f)

theorem schwartz_shifted_sum_bound (H : 𝓢((Fin r → ℝ), ℂ)) {θ : ℝ} (hθ : 0 ≤ θ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y : Fin r → ℝ,
      Summable (fun m : Fin r → ℤ => (1 + ‖zvec m - y‖) ^ θ * ‖H (zvec m - y)‖) ∧
      ∑' m : Fin r → ℤ, (1 + ‖zvec m - y‖) ^ θ * ‖H (zvec m - y)‖ ≤ C := by
  obtain ⟨CH, hCH⟩ : ∃ CH : ℝ, CH = (3 / 2 : ℝ) ^ θ *
      ((2 : ℝ) ^ (⌈θ⌉₊ + 2 * r - 1) * (SchwartzMap.seminorm ℂ 0 0 H +
        SchwartzMap.seminorm ℂ (⌈θ⌉₊ + 2 * r) 0 H) * (1 + 1 / 2) ^ (⌈θ⌉₊ + 2 * r)) := ⟨_, rfl⟩
  have hs0 : 0 ≤ SchwartzMap.seminorm ℂ 0 0 H := apply_nonneg _ _
  have hs1 : 0 ≤ SchwartzMap.seminorm ℂ (⌈θ⌉₊ + 2 * r) 0 H := apply_nonneg _ _
  have hCH0 : 0 ≤ CH := by rw [hCH]; positivity
  have hws : Summable (fun n : Fin r → ℤ => (1 + ‖n‖) ^ (-((2 * r : ℕ) : ℤ))) :=
    summable_one_add_norm_zpow
  have hw0 : ∀ n : Fin r → ℤ, 0 ≤ (1 + ‖n‖) ^ (-((2 * r : ℕ) : ℤ)) := fun n => by positivity
  refine ⟨CH * ∑' n : Fin r → ℤ, (1 + ‖n‖) ^ (-((2 * r : ℕ) : ℤ)),
    mul_nonneg hCH0 (tsum_nonneg hw0), fun y => ?_⟩
  obtain ⟨n₀, hn₀⟩ : ∃ n₀ : Fin r → ℤ, n₀ = fun i => round (y i) := ⟨_, rfl⟩
  obtain ⟨x, hx⟩ : ∃ x : Fin r → ℝ, x = zvec n₀ - y := ⟨_, rfl⟩
  have hxn : ‖x‖ ≤ 1 / 2 := by
    apply (pi_norm_le_iff_of_nonneg (by norm_num)).mpr
    intro i
    simp only [hx, hn₀, zvec, Pi.sub_apply, Real.norm_eq_abs]
    rw [abs_sub_comm]
    exact abs_sub_round (y i)
  have hterm : ∀ n : Fin r → ℤ, (1 + ‖zvec (n + n₀) - y‖) ^ θ * ‖H (zvec (n + n₀) - y)‖ ≤
      CH * (1 + ‖n‖) ^ (-((2 * r : ℕ) : ℤ)) := by
    intro n
    have hv : zvec (n + n₀) - y = x + zvec n := by
      funext i; simp only [zvec, hx, Pi.add_apply, Pi.sub_apply, Int.cast_add]; ring
    rw [hv, hCH]
    exact shifted_term_le H hθ x hxn n
  have hnn : ∀ n : Fin r → ℤ, 0 ≤ (1 + ‖zvec (n + n₀) - y‖) ^ θ * ‖H (zvec (n + n₀) - y)‖ :=
    fun n => mul_nonneg (Real.rpow_nonneg (by positivity) _) (norm_nonneg _)
  have hsum' : Summable (fun n : Fin r → ℤ =>
      (1 + ‖zvec (n + n₀) - y‖) ^ θ * ‖H (zvec (n + n₀) - y)‖) :=
    Summable.of_nonneg_of_le hnn hterm (hws.mul_left _)
  have hre : Summable (fun m : Fin r → ℤ => (1 + ‖zvec m - y‖) ^ θ * ‖H (zvec m - y)‖) :=
    (summable_addRight_shift n₀ (fun m : Fin r → ℤ =>
      (1 + ‖zvec m - y‖) ^ θ * ‖H (zvec m - y)‖)).mp hsum'
  refine ⟨hre, ?_⟩
  have hshift := tsum_addRight_shift n₀
    (fun m : Fin r → ℤ => (1 + ‖zvec m - y‖) ^ θ * ‖H (zvec m - y)‖)
  rw [← hshift]
  refine (hsum'.tsum_le_tsum hterm (hws.mul_left _)).trans (le_of_eq ?_)
  exact tsum_mul_left

end WaveTurbulence.VineEstS3.FS
