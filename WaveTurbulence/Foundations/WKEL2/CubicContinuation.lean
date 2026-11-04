/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.WKEL2.CubicStep

/-!
# Finite-step continuation from a uniform a priori bound

A fixed positive Picard step suffices; no assertion about an unconstructed
maximal flow or endpoint limit is needed.
-/

public section

noncomputable section

open Set

namespace WaveTurbulence.WKEL2

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

local instance continuationNormedOp : NormedAddCommGroup (E →L[ℝ] E) := inferInstance
local instance continuationSpaceOp : NormedSpace ℝ (E →L[ℝ] E) := inferInstance
local instance continuationNormedOp₂ : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E) := inferInstance
local instance continuationSpaceOp₂ : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E) := inferInstance

/-- A uniform a priori bound for every shorter solution gives existence on the full interval. -/
theorem exists_cubic_solution_of_uniform_bound
    (F : E →L[ℝ] E →L[ℝ] E →L[ℝ] E) (x : E) {T Q : ℝ} (hT : 0 ≤ T)
    (hbound : ∀ b : ℝ, 0 ≤ b → b ≤ T → ∀ u : ℝ → E, u 0 = x →
      (∀ t ∈ Icc 0 b, HasDerivWithinAt u (cubicField F (u t)) (Icc 0 b) t) →
      ∀ t ∈ Icc 0 b, ‖u t‖ ≤ Q) :
    ∃ u : ℝ → E, u 0 = x ∧
      ∀ t ∈ Icc 0 T, HasDerivWithinAt u (cubicField F (u t)) (Icc 0 T) t := by
  let R := max Q ‖x‖
  have hR : 0 ≤ R := (norm_nonneg x).trans (le_max_right _ _)
  let δ := cubicUniformStep F R
  have hδ : 0 < δ := cubicUniformStep_pos F hR
  have H : ∀ n : ℕ, ∃ u : ℝ → E, u 0 = x ∧
      ∀ t ∈ Icc 0 (min ((n : ℝ) * δ) T),
        HasDerivWithinAt u (cubicField F (u t)) (Icc 0 (min ((n : ℝ) * δ) T)) t := by
    intro n
    induction n with
    | zero =>
        obtain ⟨u, hu₀, hu⟩ := exists_cubic_solution_uniform F hR (le_max_right Q ‖x‖)
        refine ⟨u, hu₀, ?_⟩
        simp only [Nat.cast_zero, zero_mul, min_eq_left hT]
        intro t ht
        exact (hu t ⟨ht.1, ht.2.trans hδ.le⟩).mono (Icc_subset_Icc le_rfl hδ.le)
    | succ n ih =>
        obtain ⟨u, hu₀, hu⟩ := ih
        let b := min ((n : ℝ) * δ) T
        let c := min (((n + 1 : ℕ) : ℝ) * δ) T
        have hb : 0 ≤ b := le_min (mul_nonneg (Nat.cast_nonneg n) hδ.le) hT
        have hbc : b ≤ c := by
          dsimp [b, c]
          apply min_le_min _ le_rfl
          rw [Nat.cast_add, Nat.cast_one, add_mul, one_mul]
          exact le_add_of_nonneg_right hδ.le
        have hc : c ≤ b + δ := by
          by_cases hn : (n : ℝ) * δ ≤ T
          · have Hc : c ≤ ((n : ℝ) + 1) * δ := by
              simpa only [c, Nat.cast_add, Nat.cast_one] using min_le_left (((n + 1 : ℕ) : ℝ) * δ) T
            dsimp [b]
            rw [min_eq_left hn]
            linarith only [Hc]
          · have Hb : b = T := min_eq_right (le_of_not_ge hn)
            rw [Hb]
            exact (min_le_right _ _).trans (le_add_of_nonneg_right hδ.le)
        have hub : ‖u b‖ ≤ R :=
          (hbound b hb (min_le_right _ _) u hu₀ hu b ⟨hb, le_rfl⟩).trans (le_max_left _ _)
        obtain ⟨w, hw, hwderiv⟩ := extend_cubic_solution F hR hb hbc hc hu hub
        exact ⟨w, (hw ⟨le_rfl, hb⟩).trans hu₀, hwderiv⟩
  obtain ⟨n, hn⟩ := exists_nat_gt (T / δ)
  have hN : T ≤ (n : ℝ) * δ := ((div_lt_iff₀ hδ).1 hn).le
  simpa only [min_eq_right hN] using H n

end WaveTurbulence.WKEL2
