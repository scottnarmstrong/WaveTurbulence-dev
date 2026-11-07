/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import WaveTurbulence.Foundations.Fourier.TimeFourier
public import WaveTurbulence.Foundations.Fourier.TimeWeights

/-! # Brackets of sums of integer modes (engine step ASM)

`J(t) = √(1+t²)`. `J(a+b) ≤ √2 J(a) J(b)`, hence `J(∑_k x_k) ≤ (√2)^{#k} ∏_k J(x_k)`.
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineEstS3.Eng
open WaveTurbulence.Fourier Finset

/-- `⟨t⟩ = √(1+t²)`. -/
noncomputable def Jb (t : ℝ) : ℝ := Real.sqrt (1 + t ^ 2)

theorem Jb_pos (t : ℝ) : 0 < Jb t := Real.sqrt_pos.2 (by positivity)

theorem one_le_Jb (t : ℝ) : 1 ≤ Jb t := by
  unfold Jb
  rw [Real.one_le_sqrt]
  nlinarith [sq_nonneg t]

theorem Jb_zero : Jb 0 = 1 := by simp [Jb]

theorem Jb_add_le (a b : ℝ) : Jb (a + b) ≤ Real.sqrt 2 * Jb a * Jb b := by
  unfold Jb
  rw [← Real.sqrt_mul (by norm_num), ← Real.sqrt_mul (by positivity)]
  refine Real.sqrt_le_sqrt ?_
  nlinarith [sq_nonneg (a - b), sq_nonneg (a * b)]

theorem Jb_sum_le {κ : Type*} [Fintype κ] (x : κ → ℝ) :
    Jb (∑ k, x k) ≤ Real.sqrt 2 ^ Fintype.card κ * ∏ k, Jb (x k) := by
  classical
  have : ∀ s : Finset κ, Jb (∑ k ∈ s, x k) ≤ Real.sqrt 2 ^ s.card * ∏ k ∈ s, Jb (x k) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp [Jb_zero]
    | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.prod_insert ha, Finset.card_insert_of_notMem ha, pow_succ]
      refine (Jb_add_le _ _).trans ?_
      have h1 := Jb_pos (x a)
      calc Real.sqrt 2 * Jb (x a) * Jb (∑ k ∈ s, x k)
          ≤ Real.sqrt 2 * Jb (x a) * (Real.sqrt 2 ^ s.card * ∏ k ∈ s, Jb (x k)) :=
            mul_le_mul_of_nonneg_left ih (by positivity)
        _ = _ := by ring
  simpa using this Finset.univ

/-- A sub-sum selected by a predicate. -/
theorem Jb_select_le {κ : Type*} [Fintype κ] (p : κ → Prop) [DecidablePred p] (x : κ → ℝ) :
    Jb (∑ k, if p k then x k else 0) ≤ Real.sqrt 2 ^ Fintype.card κ * ∏ k, Jb (x k) := by
  refine (Jb_sum_le _).trans ?_
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  have hp : ∀ k, Jb (if p k then x k else 0) ≤ Jb (x k) := by
    intro k
    split_ifs
    · exact le_rfl
    · rw [Jb_zero]; exact one_le_Jb _
  gcongr with k hk
  · exact fun i _ => (Jb_pos _).le
  · exact hp k

theorem Jb_le_two_timeBracket {r : ℕ} (m : Fin r → ℤ) (i : Fin r) :
    Jb (m i : ℝ) ≤ 2 * timeBracket (fun j => (m j : ℝ) / 2) := by
  have h1 := bracket_le_timeBracket (fun j => (m j : ℝ) / 2) i
  unfold Jb
  have h2 : Real.sqrt (1 + (m i : ℝ) ^ 2) ≤ 2 * Real.sqrt (1 + ((m i : ℝ) / 2) ^ 2) := by
    have h4 : Real.sqrt 4 = 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num]; exact Real.sqrt_sq (by norm_num)
    calc Real.sqrt (1 + (m i : ℝ) ^ 2) ≤ Real.sqrt (4 * (1 + ((m i : ℝ) / 2) ^ 2)) :=
          Real.sqrt_le_sqrt (by nlinarith [sq_nonneg (m i : ℝ)])
      _ = 2 * Real.sqrt (1 + ((m i : ℝ) / 2) ^ 2) := by rw [Real.sqrt_mul (by norm_num), h4]
  exact h2.trans (by linarith)

theorem Jb_half_le_timeBracket {r : ℕ} (m : Fin r → ℤ) (i : Fin r) :
    Jb ((m i : ℝ) / 2) ≤ timeBracket (fun j => (m j : ℝ) / 2) :=
  bracket_le_timeBracket (fun j => (m j : ℝ) / 2) i

end WaveTurbulence.VineEstS3.Eng
