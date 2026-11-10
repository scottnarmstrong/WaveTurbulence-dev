/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Flower.Polar.Bound
public import WaveTurbulence.Foundations.Flower.Polar.Cost
public import WaveTurbulence.Foundations.Spine.GardenEval
/-! # FL-POLAR: external decay for flowers by the polarization device. -/
@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace WaveTurbulence.Flower.Polar
open Finset LGSpine

/-- The list of rounds: every tree `m` times. -/
def rep (w : ℕ) : ℕ → List (Fin w)
  | 0 => []
  | m + 1 => List.finRange w ++ rep w m

theorem rep_length (w m : ℕ) : (rep w m).length = m * w := by
  induction m with
  | zero => simp [rep]
  | succ m ih => simp [rep, ih, Nat.succ_mul]; ring

theorem count_rep {w : ℕ} (m : ℕ) (a : Fin w) : (rep w m).count a = m := by
  induction m with
  | zero => simp [rep]
  | succ m ih =>
    rw [rep, List.count_append, ih,
      List.count_eq_one_of_mem (List.nodup_finRange w) (List.mem_finRange a)]
    ring

theorem wcnt_le_count {w : ℕ} (js : List (Fin w)) (j1 j2 : Fin w) :
    wcnt js j1 j2 ≤ js.count j1 + js.count j2 := by
  induction js with
  | nil => simp [wcnt]
  | cons j js ih =>
    rw [wcnt_cons, List.count_cons, List.count_cons]
    have : tch j j1 j2 ≤ (if j == j1 then 1 else 0) + (if j == j2 then 1 else 0) := by
      unfold tch
      by_cases hi : (j1 = j ↔ j2 = j)
      · simp [hi]
      · simp only [hi, if_false]
        have : j1 = j ∨ j2 = j := by
          by_cases h1 : j1 = j
          · exact Or.inl h1
          · right; by_contra h2; exact hi ⟨fun h => absurd h h1, fun h => absurd h h2⟩
        rcases this with h1 | h2
        · simp [h1]
        · simp [h2]
    omega

theorem wcnt_apps {w : ℕ} (js : List (Fin w)) (j1 j2 : Fin w) :
    wcnt (apps js) j1 j2 = 2 * wcnt js j1 j2 := by
  induction js with
  | nil => simp [apps, wcnt]
  | cons j js ih =>
    simp only [apps, wcnt_cons, ih]; ring

theorem wcnt_apps_rep_le {w : ℕ} (m : ℕ) (j1 j2 : Fin w) : wcnt (apps (rep w m)) j1 j2 ≤ 4 * m := by
  rw [wcnt_apps]
  have := wcnt_le_count (rep w m) j1 j2
  rw [count_rep, count_rep] at this
  omega

theorem jbr_pow_eq {d : ℕ} (x : Mom d) (R : ℕ) : jbr x ^ (2 * R) = (1 + ‖x‖ ^ 2) ^ R := by
  rw [pow_mul, jbr, Real.sq_sqrt (by positivity)]

end WaveTurbulence.Flower.Polar
