/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5A.A3Scalar
public import WaveTurbulence.Foundations.VineEst.VineEstS3Par.ClockPhase

/-! # Two-clock expansions as three-clock expansions with a zero third mode (V5 Step 4d-A, item 2) -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineEstS5A
open WaveTurbulence WaveTurbulence.Fourier WaveTurbulence.VineEstS3.FS WaveTurbulence.VineEstS3Par.Eng
  MeasureTheory
open scoped ENNReal

/-- The embedding of two-clock modes `n ∈ ℤ²` as `(n₀, n₁, 0) ∈ ℤ³`. -/
def embedMode (n : Fin 2 → ℤ) : Fin 3 → ℤ := ![n 0, n 1, 0]

theorem embedMode_injective : Function.Injective embedMode := by
  intro n n' h
  funext i
  fin_cases i
  · exact congrFun h 0
  · exact congrFun h 1

/-- The three-clock coefficients of a two-clock coefficient family (zero unless the third mode vanishes). -/
noncomputable def embed2 (h : (Fin 2 → ℤ) → ℂ) : (Fin 3 → ℤ) → ℂ :=
  fun m => if m 2 = 0 then h ![m 0, m 1] else 0

theorem embed2_embedMode (h : (Fin 2 → ℤ) → ℂ) (n : Fin 2 → ℤ) : embed2 h (embedMode n) = h n := by
  unfold embed2 embedMode
  have h2 : (![n 0, n 1, 0] : Fin 3 → ℤ) 2 = 0 := rfl
  rw [if_pos h2]
  have : (![(![n 0, n 1, 0] : Fin 3 → ℤ) 0, (![n 0, n 1, 0] : Fin 3 → ℤ) 1] : Fin 2 → ℤ) = n := by
    funext i; fin_cases i <;> rfl
  rw [this]

theorem embed2_eq_zero (h : (Fin 2 → ℤ) → ℂ) (m : Fin 3 → ℤ) (hm : m ∉ Set.range embedMode) :
    embed2 h m = 0 := by
  unfold embed2
  split_ifs with h2
  · exfalso; apply hm
    refine ⟨![m 0, m 1], ?_⟩
    unfold embedMode
    funext i; fin_cases i <;> simp [h2]
  · rfl

theorem fsPhase_embedMode (n : Fin 2 → ℤ) (t : Fin 3 → ℝ) :
    fsPhase (embedMode n) t = fsPhase n ![t 0, t 1] := by
  rw [fsPhase_eq_exp, fsPhase_eq_exp]
  simp [embedMode, Fin.sum_univ_three, Fin.sum_univ_two]

theorem hasSum_embed2 (h : (Fin 2 → ℤ) → ℂ) (t : Fin 3 → ℝ) {S : ℂ}
    (hS : HasSum (fun n : Fin 2 → ℤ => h n * fsPhase n ![t 0, t 1]) S) :
    HasSum (fun m : Fin 3 → ℤ => embed2 h m * fsPhase m t) S := by
  rw [← embedMode_injective.hasSum_iff (f := fun m : Fin 3 → ℤ => embed2 h m * fsPhase m t)
    (fun m hm => by rw [embed2_eq_zero h m hm, zero_mul])]
  convert hS using 2 with n
  rw [Function.comp_apply, embed2_embedMode, fsPhase_embedMode]

theorem maxBracketPow_embedMode (θ : ℝ) (n : Fin 2 → ℤ) :
    maxBracketPow θ (half (embedMode n)) = maxBracketPow θ (half n) := by
  unfold maxBracketPow
  congr 2
  apply le_antisymm
  · refine sup_le (Real.iSup_le (fun i => ?_) (le_trans (by norm_num) le_sup_right)) le_sup_right
    fin_cases i
    · exact le_sup_of_le_left (le_ciSup (f := fun j : Fin 2 => Real.sqrt (1 + half n j ^ 2))
        (Set.finite_range _).bddAbove 0)
    · exact le_sup_of_le_left (le_ciSup (f := fun j : Fin 2 => Real.sqrt (1 + half n j ^ 2))
        (Set.finite_range _).bddAbove 1)
    · simp [half, embedMode]
  · refine sup_le (Real.iSup_le (fun i => ?_) (le_trans (by norm_num) le_sup_right)) le_sup_right
    fin_cases i
    · exact le_sup_of_le_left (le_ciSup (f := fun j : Fin 3 => Real.sqrt (1 + half (embedMode n) j ^ 2))
        (Set.finite_range _).bddAbove 0)
    · exact le_sup_of_le_left (le_ciSup (f := fun j : Fin 3 => Real.sqrt (1 + half (embedMode n) j ^ 2))
        (Set.finite_range _).bddAbove 1)

theorem tsum_embed2 (θ : ℝ) (h : (Fin 2 → ℤ) → ℂ) :
    ∑' m : Fin 3 → ℤ, maxBracketPow θ (half m) * ‖embed2 h m‖ₑ =
      ∑' n : Fin 2 → ℤ, maxBracketPow θ (half n) * ‖h n‖ₑ := by
  rw [← embedMode_injective.tsum_eq (f := fun m : Fin 3 → ℤ => maxBracketPow θ (half m) * ‖embed2 h m‖ₑ)]
  · refine tsum_congr fun n => ?_
    rw [embed2_embedMode, maxBracketPow_embedMode]
  · intro m hm
    by_contra hnr
    apply hm
    simp [embed2_eq_zero h m hnr]

end WaveTurbulence.VineEstS5A
